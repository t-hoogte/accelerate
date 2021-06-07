{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
module Data.Array.Accelerate.Trafo.Partitioning.ILP.Clustering where

import Control.Category
import Data.Array.Accelerate.AST.LeftHandSide
import Data.Array.Accelerate.AST.Partitioned
import Data.Array.Accelerate.Trafo.Partitioning.ILP.Graph
import Data.Array.Accelerate.Trafo.Partitioning.ILP.Labels
import Data.Bifunctor
import Prelude hiding (id, (.))
import qualified Data.Map as M
import Unsafe.Coerce (unsafeCoerce)
import qualified Data.Graph as G
import qualified Data.Set as S
import qualified Data.Array as A
import Data.Function (on)
import Lens.Micro ((^.))


-- "open research question"
-- -- Each set of ints corresponds to a set of Constructions, which themselves contain a set of ints (the things they depend on).
-- -- Some of those ints will refer to nodes in previous clusters, others to nodes in this cluster.
-- One pass over these datatypes (back-to-front) should identify the 'output type' of each cluster: which nodes are needed in later clusters?
-- Then, we can construct the clusters front-to-back:
--    identify the nodes that only depend on nodes outside of the cluster, they are the initials
--    the `output type` indicates which nodes we will need to keep: they are all either a final node in the cluster, or get diagonally fused
-- How exactly we can use this information (and a dep. graph) to construct a cluster of ver,hor,diag is not clear.. Will also depend on the exact cluster definition.

{-
Within each cluster (Labels), we do a topological sort using the edges in Graph
((a,b) means a before b in ordering). Then, we can simply insert them front-to-back:
existing `In` arguments are never touched, existing `Out` arguments are matched with
new `In` arguments vertically or diagonally (depending on if they'll be needed still),
new `Out` arguments are never touched. We can even do the re-ordering of Args as we go
on the fresh leaves, never need to touch the existing tree.
  Note that we basically build a list instead of a binary tree. 
  Could refactor Cluster to reflect this.

Data.Graph (containers) has a nice topological sort. Then we just need to know, given
such an ordering, what the live args should be at each point, or even just the death points
of each arg.
-}


-- Note that the return type `a` is not existentially qualified: The caller of this function tells
-- us what the result type should be (namely, what it was before fusion). We use unsafe tricks to
-- fulfill this contract: if something goes wrong during fusion or at the caller, bad things happen.
reconstruct :: forall op a. Graph -> [Labels] -> M.Map Label [Labels] -> M.Map Label (Construction op) -> PreOpenAcc (Cluster op) () a
reconstruct a b c d = case openReconstruct LabelEnvNil a b c d of
          -- see [NOTE unsafeCoerce result type]
          Exists res -> unsafeCoerce @(PartitionedAcc op () _)
                                     @(PartitionedAcc op () a)
                                     res

-- ordered list of labels
type ClusterL = [Label]

-- Data.Graph has an awkward definition of graphs, but also already has an implementation of 'topsort'.
-- type G.Graph = A.Array Label [Label]
topSortDieMap :: Graph -> Labels -> (M.Map Label Labels, ClusterL)
topSortDieMap (Graph _ fedges _) cluster = (dieMap, topsorted)
  where
    cluster' = S.map _labelId cluster
    getLabels = labelMap cluster
    graph, transposed :: G.Graph 
    graph = G.buildG (minimum cluster', maximum cluster') 
          . S.toList 
          . S.filter (uncurry ((&&) `on` (`elem` cluster'))) -- filter edges on 'both vertices are in the cluster'
          . S.map (\(Label x _ :-> Label y _) -> (x, y))
          $ fedges
    transposed = G.transposeG graph
    topsorted = map (getLabels M.!) $ G.topSort graph
    -- traverses the nodes in reverse topsort order
    dieMap = fst $ foldl f mempty topsorted
    f :: (M.Map Label Labels, Labels) -> Label -> (M.Map Label Labels, Labels)
    f (dieMap', keepAlive) x = let incomingEdges = S.fromList . map (getLabels M.!) $ transposed A.! (x^.labelId) in
      (M.insert x incomingEdges dieMap', S.insert x incomingEdges <> keepAlive)


openReconstruct :: forall op aenv. LabelEnv aenv -> Graph -> [Labels] -> M.Map Label [Labels] -> M.Map Label (Construction op) -> Exists (PreOpenAcc (Cluster op) aenv)
openReconstruct labelenv graph clusterslist subclustersmap construc = undefined
  where

    makeAST :: LabelEnv env -> [ClusterL] -> Exists (PreOpenAcc (Cluster op) env)
    makeAST env [] = undefined
    makeAST env [cluster] = case makeCluster cluster of
      Fold c args env' -> Exists $ Exec c args
      InitFold o args env' -> Exists $ Exec (Leaf o id) args
      NotFold _ -> undefined
    makeAST env (cluster:tail) = undefined

    -- do the topological sorting and computing of dieMap for each set
    (dieMap',    clusters) =                   first mconcat . unzip . map (topSortDieMap graph)  $    clusterslist
    (dieMapM, subclusters) = sequence . M.map (first mconcat . unzip . map (topSortDieMap graph)) $ subclustersmap
    -- dieMap informs us when variables become 'dead variables': 
    -- when they do, we can fuse vertically, until then it's diagonal instead.
    dieMap = dieMap' <> dieMapM

    makeCluster :: ClusterL -> FoldType op env
    makeCluster = undefined

    -- The label is used to choose between vertical and diagonal fusion, using the DieMap.
    fuseCluster :: Label -> FoldType op env -> FoldType op env -> FoldType op env
    fuseCluster l (Fold cluster1 args1 largs1) (InitFold op2 args2 largs2) = 
      case fuseSwap (dieMap M.! l) largs1 largs2 of
        Result swap combine largs ->
          let args = combineArgs combine args1 (swapArgs' swap args2)
          in Fold (Branch cluster1 (Leaf op2 swap) combine) args largs
    fuseCluster l (InitFold op args largs) x = fuseCluster l (Fold (Leaf op id) args largs) x
    fuseCluster _ Fold{} Fold{} = error "fuseCluster got non-leaf as second argument" -- Could support this, but should never happen
    fuseCluster _ _      _      = error "fuseCluster encountered NotFold" -- We can't fuse non-Exec nodes

    fuseSwap :: Labels -> LabelArgs a -> LabelArgs b' -> FuseSwapResult a b'
    fuseSwap vertical = go
      where
        go :: LabelArgs a -> LabelArgs b' -> FuseSwapResult a b'
        go LabelArgsNil LabelArgsNil = Result id Combine LabelArgsNil
        go (a :>>: as) b' = case findArg a b' of
          -- `a` is not in `b'`, no reordering needed and it should also not be in the dieMap
          Nothing -> if S.size a == 1 && S.findMin a `S.member` vertical 
                     then error "cannot be" 
                     else case go as b' of
            Result f c la -> Result f (WeakRight c) (a :>>: la)
          -- `a` is in `b'`, and this 'Take' tells us where! Take it out, recurse on the tail, then put it in front.
          Just (ExisTake t) -> let (a', bs) = labelledTake t b'
                               in if a /= a' then error "what did findArg even do" 
                                  else case go as bs of
            Result f c la -> _

        go LabelArgsNil (b :>>: bs) = case go LabelArgsNil bs of
          Result f c lb -> Result (liftSwap f) (WeakLeft c) (b :>>: lb)


-- | Internal datatypes for `makeCluster`.
data FoldType op env
  = forall args. Fold (Cluster op args) (Args env args) (LabelArgs args)
  | forall args. InitFold (op args) (Args env args) (LabelArgs args) -- like Fold, but without a Swap
  | NotFold (Construction op)

data FuseSwapResult a b' = forall b c. Result (SwapArgs b b') (Combine a b c) (LabelArgs c) -- don't need this last one? 'combineArgs' can generate it

data ExisTake xa = forall x a. ExisTake (Take x xa a)

findArg :: Labels -> LabelArgs xs -> Maybe (ExisTake xs)
findArg _ LabelArgsNil = Nothing
findArg ls (ms :>>: xss)
  | ls == ms = Just $ ExisTake Here
  | otherwise = (\(ExisTake t) -> ExisTake $ There t) <$> findArg ls xss



{- [NOTE unsafeCoerce result type]

  Because we lose some type information by rebuilding the AST from scratch, we use
  unsafeCoerce to tell GHC what the result type of the computation is.
  TypeApplications allows us to specify the exact types unsafeCoerce works on,
  which in turn helps retain as much typesafety as possible. Whereever this note
  is found, unsafeCoerce's type is restricted to only work on the result type.
  In particular, we take care to not allow unsafeCoerce to mess with environment types,
  as they are tricky to get right and we really like GHC agreeing with us there.

-}
