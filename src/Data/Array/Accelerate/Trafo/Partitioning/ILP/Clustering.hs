{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE EmptyCase #-}

-- _Significantly_ speeds up compilation of this file, but at an obvious cost!
-- Even in GHC 9.0.1, which has Lower Your Guards, these checks take some time (though no longer quite as long).
-- Recommended to disable these options when working on this file, and restore them when you're done.
{-# OPTIONS_GHC 
  -Wno-overlapping-patterns 
  -Wno-incomplete-patterns 
#-}

module Data.Array.Accelerate.Trafo.Partitioning.ILP.Clustering where

import Data.Array.Accelerate.AST.LeftHandSide ( Exists(..), LeftHandSide (..) )
import Data.Array.Accelerate.AST.Partitioned hiding (take', unfused)
import Data.Array.Accelerate.Representation.Type
import Data.Array.Accelerate.Trafo.Partitioning.ILP.Graph hiding (info)
import Data.Array.Accelerate.Trafo.Partitioning.ILP.Labels hiding (ELabels)

import qualified Data.Map as M
import Unsafe.Coerce (unsafeCoerce)
import qualified Data.Graph as G
import qualified Data.Set as S
import Data.Array.Accelerate.AST.Operation
import Data.Maybe (fromJust)
import Data.Type.Equality ( type (:~:)(Refl) )
import Data.Array.Accelerate.Trafo.Partitioning.ILP.Solve (ClusterLs (Execs, NonExec))
import Data.Array.Accelerate.AST.Environment (weakenWithLHS)

import Prelude hiding ( take )
import Lens.Micro (_1)
import Lens.Micro.Extras (view)
import Data.Array.Accelerate.Trafo.LiveVars (SubTupR(SubTupRkeep))
import Data.Array.Accelerate.Representation.Array (ArrayR (ArrayR))
import qualified Data.Functor.Const as C
import Data.Bifunctor (first, second)
import Data.Array.Accelerate.AST.Idx
import Data.Array.Accelerate.Trafo.Operation.Substitution (weaken)
import Data.Functor.Identity
import Data.Array.Accelerate.Pretty.Exp (IdxF(..))
import qualified Data.Tree as T
import qualified Debug.Trace
import GHC.Exts (SpecConstrAnnotation)
import Data.Array.Accelerate.Representation.Shape (shapeType)

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
((a,b) means a before b in ordering). Then, we can simply cons them on top of each other.
Data.Graph (containers) has a nice topological sort.
-}


-- map M.! key = case map M.!? key of
--   Just x -> x
--   Nothing -> Debug.Trace.trace ("error: map "<> show map <> "does not contain key " <> show key) undefined

-- instance Show (Exists a) where
--   show (Exists x) = "exis"

-- Note that the return type `a` is not existentially qualified: The caller of this function tells
-- us what the result type should be (namely, what it was before fusion). We use unsafe tricks to
-- fulfill this contract: if something goes wrong during fusion or at the caller, bad things happen.
reconstruct :: forall op a. MakesILP op => Bool -> Graph -> [ClusterLs] -> M.Map Label [ClusterLs] -> M.Map Label (Construction op) -> PreOpenAcc (Clustered op) () a
reconstruct a b c d e = case openReconstruct a LabelEnvNil b c d e of
          -- see [NOTE unsafeCoerce result type]
          Exists res -> unsafeCoerce @(PartitionedAcc op () _)
                                     @(PartitionedAcc op () a)
                                     res

reconstructF :: forall op a. MakesILP op => Bool -> Graph -> [ClusterLs] -> M.Map Label [ClusterLs] -> M.Map Label (Construction op) -> PreOpenAfun (Clustered op) () a
reconstructF a b c d e = case openReconstructF a LabelEnvNil b c (Label 1 Nothing) d e of
          -- see [NOTE unsafeCoerce result type]
          Exists res -> unsafeCoerce @(PartitionedAfun op () _)
                                     @(PartitionedAfun op () a)
                                     res


-- ordered list of labels
data ClusterL = ExecL [Label] | NonExecL Label
  deriving Show

foldC :: (Label -> b -> b) -> b -> ClusterL -> b
foldC f x (ExecL ls) = foldr f x ls
foldC f x (NonExecL l) = f l x

topSort :: Bool -> Graph -> Labels -> [ClusterL]
topSort _ _ (S.toList -> [l]) = [ExecL [l]]
-- topSort True _ ls = map (ExecL . pure) $ S.toList ls -- TODO no, need to sort them first
topSort singletons (Graph _ fedges fpedges) cluster = if singletons then concatMap (map (ExecL . pure)) topsorteds else map ExecL topsorteds
  where
    buildGraph =
            G.graphFromEdges
          . map (\(a,b) -> (a,a,b))
          . M.toList
          . flip (S.fold (\(x :-> y) -> M.adjust (y:) x)) fedges
          . M.fromList
          . map (,[])
          . S.toList
    -- for some reason, this doesn't work yet!
    -- \xs -> (map f xs, map g xs) gets split, even though I really thought this would work
    -- if @xs@ is concrete, it does seem to work? 
    -- TODO: compare the graphs of @horizontal@ and @horizontal xs@
    -- TODO: I changed stuff since I wrote the above; check whether it works now

    -- Make a graph of all these labels and their incoming edges (for horizontal fusion)...
    fpparents =                    S.unions $ S.map (\l -> (S.\\ cluster) $ S.map (\(a:->_)->a) $ S.filter (\(_:->b)->l==b) fpedges) cluster
    parents   = (S.\\ fpparents) $ S.unions $ S.map (\l -> (S.\\ cluster) $ S.map (\(a:->_)->a) $ S.filter (\(_:->b)->l==b) fedges ) cluster
    parentsPlusEdges :: S.Set (Label, Int, Label) -- (Parent, Order, Source)
    parentsPlusEdges = S.unions $ S.unions $ S.map (\l -> let relevantEdges = S.filter (\(a:->b)->l==a && b `S.member` cluster) (fedges S.\\ fpedges)
                                                              orders :: S.Set Int
                                                              orders = S.map (\(a:->b)-> readOrderOf b) relevantEdges
                                                              ordersWithEdges = S.map (\o -> S.map (\(_:->b) -> (l,o,b)) $ S.filter (\(_:->b)-> readOrderOf b == o) relevantEdges) orders
                                                          in ordersWithEdges) parents
    (graph, getAdj, _) = buildGraph $ S.union cluster parents
    -- TODO: this also 'connects' components through 'horizonal fusion' if they are in different orders.
      -- To fix this: consider each edge from outside the cluster to inside the cluster: look at the sources (parents) and the read-order of those edges.
      -- Whenever one parent has outgoing edges of varying read-orders, we should have multiple nodes for this parent, one per read-order.
      -- this is important: otherwise we end up fusing loops with different iteration sizes!

    -- .. split it into connected components and remove those parents from last step,
    components = map (S.intersection cluster . S.fromList . map ((\(x,_,_)->x) . getAdj) . T.flatten) $ G.components graph
    -- and make a graph of each of them...
    graphs = if singletons then [buildGraph cluster] else map buildGraph components
    -- .. and finally, topologically sort each of those to get the labels per cluster sorted on dependencies
    topsorteds = map (\(graph', getAdj', _) -> map (view _1 . getAdj') $ G.topSort graph') graphs
    readOrderOf = undefined --TODO

openReconstruct   :: MakesILP op
                  => Bool
                  -> LabelEnv aenv
                  -> Graph
                  -> [ClusterLs]
                  -> M.Map Label [ClusterLs]
                  -> M.Map Label (Construction op)
                  -> Exists (PreOpenAcc (Clustered op) aenv)
openReconstruct  a b c d e f = (\(Left x) -> x) $ openReconstruct' a b c d Nothing e f
openReconstructF  :: MakesILP op
                  => Bool
                  -> LabelEnv aenv
                  -> Graph
                  -> [ClusterLs]
                  -> Label
                  -> M.Map Label [ClusterLs]
                  -> M.Map Label (Construction op)
                  -> Exists (PreOpenAfun (Clustered op) aenv)
openReconstructF a b c d l e f= (\(Right x) -> x) $ openReconstruct' a b c d (Just l) e f

openReconstruct' :: forall op aenv. MakesILP op => Bool -> LabelEnv aenv -> Graph -> [ClusterLs] -> Maybe Label -> M.Map Label [ClusterLs] -> M.Map Label (Construction op) -> Either (Exists (PreOpenAcc (Clustered op) aenv)) (Exists (PreOpenAfun (Clustered op) aenv))
openReconstruct' singletons labelenv graph clusterslist mlab subclustersmap construct = case mlab of
  Just l  -> Right $ makeASTF labelenv l mempty
  Nothing -> Left $ makeAST labelenv clusters mempty
  where
    -- Make a tree of let bindings

    -- In mkFullGraph, we make sure that the bound body of a let will be in an earlier cluster.
    -- Those are stored in the 'prev' argument.
    -- Note also that we currently assume that the final cluster is the return argument: If all computations are relevant
    -- and our analysis is sound, the return argument should always appear last. If not.. oops
    makeAST :: forall env. LabelEnv env -> [ClusterL] -> M.Map Label (Exists (PreOpenAcc (Clustered op) env)) -> Exists (PreOpenAcc (Clustered op) env)
    makeAST _ [] _ = error "empty AST"
    makeAST env [cluster] prev = case makeCluster env cluster of
      Fold c args -> Exists $ Exec c $ unLabelOp args
      InitFold o l args -> unfused o l args $
                            \c args' ->
                                Exists $ Exec c (unLabelOp args')
      NotFold con -> case con of
         CExe {}    -> error "should be Fold/InitFold!"
         CExe'{}    -> error "should be Fold/InitFold!"
         CUse se  n be             -> Exists $ Use se n be
         CITE env' c t f   -> case (makeAST env (subcluster t) prev, makeAST env (subcluster f) prev) of
            (Exists tacc, Exists facc) -> Exists $ Acond
              (fromJust $ reindexVar (mkReindexPartial env' env) c)
              -- [See NOTE unsafeCoerce result type]
              (unsafeCoerce @(PreOpenAcc (Clustered op) env _)
                            @(PreOpenAcc (Clustered op) env _)
                            tacc)
              (unsafeCoerce @(PreOpenAcc (Clustered op) env _)
                            @(PreOpenAcc (Clustered op) env _)
                            facc)
         CWhl env' c b i u -> case (subcluster c, subcluster b) of
           (findTopOfF -> c', findTopOfF -> b') -> case (makeASTF env c' prev, makeASTF env b' prev) of
            (Exists cfun, Exists bfun) -> Exists $ Awhile
              u
              -- [See NOTE unsafeCoerce result type]
              (unsafeCoerce @(PreOpenAfun (Clustered op) env _)
                            @(PreOpenAfun (Clustered op) env (_ -> PrimBool))
                            cfun)
              (unsafeCoerce @(PreOpenAfun (Clustered op) env _)
                            @(PreOpenAfun (Clustered op) env (_ -> _))
                            bfun)
              (fromJust $ reindexVars (mkReindexPartial env' env) i)
         CLHS {} -> error "let without scope"
         CFun {} -> error "wrong type: function"
         CBod {} -> error "wrong type: function"
         CRet env' vars     -> Exists $ Return      (fromJust $ reindexVars (mkReindexPartial env' env) vars)
         CCmp env' expr     -> Exists $ Compute     (fromJust $ reindexExp  (mkReindexPartial env' env) expr)
         CAlc env' shr e sh -> Exists $ Alloc shr e (fromJust $ reindexVars (mkReindexPartial env' env) sh)
         CUnt env' evar     -> Exists $ Unit        (fromJust $ reindexVar  (mkReindexPartial env' env) evar)
    makeAST env (cluster:ctail) prev =

      -- TODO: use guards to fuse these two identical cases
      case makeCluster env cluster of
      NotFold con -> case con of
        CLHS (mylhs :: MyGLHS a) b u -> case prev M.! b of
          Exists bnd -> createLHS mylhs env $ \env' lhs ->
            case makeAST env' ctail (M.map (\(Exists acc) -> Exists $ weakenAcc lhs acc) prev) of
              Exists scp
                | bnd' <- unsafeCoerce @(PreOpenAcc (Clustered op) env _) -- [See NOTE unsafeCoerce result type]
                                       @(PreOpenAcc (Clustered op) env a)
                                       bnd
                  -> Exists $ Alet lhs
                      u -- (makeUniqueness lhs bnd') -- TODO @Ivo: `u` is the old uniquenesses of this lhs, do we just take that?
                      bnd'
                      scp
        _ -> let res = makeAST env [cluster] prev in case cluster of
                ExecL _ -> case (res, makeAST env ctail prev) of
                  (Exists exec@Exec{}, Exists scp) -> Exists $ Alet LeftHandSideUnit (shared TupRunit) exec scp
                  _ -> error "nope"
                NonExecL _ -> makeAST env ctail $ foldC (`M.insert` res) prev cluster
      _   -> let res = makeAST env [cluster] prev in case cluster of
                ExecL _ -> case (res, makeAST env ctail prev) of
                  (Exists exec@Exec{}, Exists scp) -> Exists $ Alet LeftHandSideUnit (shared TupRunit) exec scp
                  _ -> error "nope"
                NonExecL _ -> makeAST env ctail $ foldC (`M.insert` res) prev cluster

    makeASTF :: forall env. LabelEnv env -> Label -> M.Map Label (Exists (PreOpenAcc (Clustered op) env)) -> Exists (PreOpenAfun (Clustered op) env)
    makeASTF env l prev = case makeCluster env (NonExecL l) of
      NotFold CBod -> case makeAST env (subcluster l) prev of
        --  fromJust $ l' ^. parent) prev of 
        Exists acc -> Exists $ Abody acc
      NotFold (CFun lhs l') -> createLHS lhs env $ \env' lhs' -> case makeASTF env' l' (M.map (\(Exists acc) -> Exists $ weakenAcc lhs' acc) prev) of
        Exists fun -> Exists $ Alam lhs' fun
      NotFold {} -> error "wrong type: acc"
      _ -> error "not a notfold"

    findTopOfF :: [ClusterL] -> Label
    findTopOfF [] = error "empty list"
    findTopOfF [NonExecL x] = x
    findTopOfF (x@(NonExecL l):xs) = case construct M.! l of
      CBod -> findTopOfF xs
      CFun _ l' -> findTopOfF $ filter (\(NonExecL l'') -> l'' /= l') xs ++ [x]
      _ -> error "should be a function"
      -- findTopOfF $ filter (\(NonExecL l) -> Just l /= p) xs ++ [x]
    findTopOfF _ = error "should be a function"

    -- do the topological sorting for each set
    -- TODO: add 'backend-specific' edges to the graph for sorting, see 3.3.1 in the PLDI paper
    clusters = concatMap (\case
                      Execs ls -> topSort singletons graph ls
                      NonExec l -> [NonExecL l]) clusterslist
    subclusters = M.map (concatMap ( \case
                      Execs ls -> topSort singletons graph ls
                      NonExec l -> [NonExecL l])) subclustersmap
    subcluster l = subclusters M.! l

    makeCluster :: LabelEnv env -> ClusterL -> FoldType op env
    makeCluster env (ExecL ls) =
       foldr1 (flip fuseCluster)
                    $ map ( \l -> case construct M.! l of
                              -- At first thought, this `fromJust` might error if we fuse an array away.
                              -- It does not: The array will still be in the environment, but after we finish
                              -- the `foldr1`, the input argument will dissapear. The output argument does not:
                              -- we clean that up in the SLV pass, if this was vertical fusion. If this is diagonal fusion,
                              -- it stays.
                              CExe env' args op -> InitFold op l (fromJust $ reindexLabelledArgsOp (mkReindexPartial env' env) args)
                              _                 -> error "avoid this next refactor" -- c -> NotFold c
                          ) ls
    makeCluster _ (NonExecL l) = NotFold $ construct M.! l

    fuseCluster :: FoldType op env -> FoldType op env -> FoldType op env
    fuseCluster (Fold cluster cargs) (InitFold op l largs) =
      consCluster l largs op cargs cluster Fold
    fuseCluster (InitFold op l largs) x = unfused op l largs $ \c cargs -> fuseCluster (Fold c cargs) x
    fuseCluster Fold{} Fold{} = error "fuseCluster got non-leaf as second argument" -- Should never happen
    fuseCluster NotFold{}   _ = error "fuseCluster encountered NotFold" -- Should only occur in singleton clusters
    fuseCluster _   NotFold{} = error "fuseCluster encountered NotFold" -- Should only occur in singleton clusters

weakenAcc :: LeftHandSide s t env env' -> PreOpenAcc op env a -> PreOpenAcc op env' a
weakenAcc lhs =  runIdentity . reindexAcc (weakenReindex $ weakenWithLHS lhs)

-- | Internal datatype for `makeCluster`.

data FoldType op env
  = forall args. Fold (Clustered op args) (LabelledArgsOp op env args)
  | forall args. InitFold (op args) Label (LabelledArgsOp op env args)
  | NotFold (Construction op)



unfused :: forall op args env r. MakesILP op => op args -> Label -> LabelledArgsOp op env args -> (forall args'. Clustered op args' -> LabelledArgsOp op env args' -> r) -> r
unfused op l largs k = singleton largs op $ 
  \c@(Clustered (Op (SLVOp (SOp (SOAOp (_op :: op argsToo) soas) (SA sort _unsort)) sa)) b) ->
    case unsafeCoerce Refl of -- we know that `_op` is the same as `op`
      (Refl :: args :~: argsToo) -> k c (slv louttovar sa $ sort $ soaExpand splitLabelledArgsOp soas largs)

louttovar :: LabelledArgOp op env (Out sh e) -> LabelledArgOp op env (Var' sh)
louttovar (LOp a (_,ls) b) = LOp (outvar a) (NotArr, ls) b -- unsafe marker: maybe this NotArr ends up a problem?


{- [NOTE unsafeCoerce result type]

  Because we lose some type information by rebuilding the AST from scratch, we use
  unsafeCoerce to tell GHC what the result type of the computation is.
  TypeApplications allows us to specify the exact types unsafeCoerce works on,
  which in turn helps retain as much typesafety as possible. Whereever this note
  is found, unsafeCoerce's type is restricted to only work on the result type.
  In particular, we take care to not allow unsafeCoerce to mess with environment types,
  as they are tricky to get right and we really want GHC to check our work.

-}

tryUpdateList :: (a -> Bool) -> (a -> a) -> [a] -> Maybe [a]
tryUpdateList _ _ [] = Nothing
tryUpdateList p f (x : xs)
  | p x = Just $ f x : xs
  | otherwise = tryUpdateList p f xs




consCluster :: forall env args extra op r
             . MakesILP op
            => Label
            -> LabelledArgsOp op env extra
            -> op extra
            -> LabelledArgsOp op env args
            -> Clustered op args
            -> (forall args'. Clustered op args' -> LabelledArgsOp op env args' -> r)
            -> r
consCluster l lop op lcluster cluster k = unfused op l lop $ \c lop' ->
  fuse (unOpLabels lop') (unOpLabels lcluster) lop' lcluster c cluster fuseVertically $ flip k

fuseVertically :: LabelledArgOp op env (Out sh e) -> LabelledArgOp op env (In sh e) -> LabelledArgOp op env (Var' sh)
fuseVertically
  (LOp (ArgArray Out (ArrayR shr _) sh _) (_, ls) b)
  (LOp (ArgArray In _ _ _) (_, ls') _)
  = LOp (ArgVar $ groundToExpVar (shapeType shr) sh) (NotArr, ls<>ls') b

instance NFData' op => NFData' (Clustered op) where
  rnf' c = () -- TODO
