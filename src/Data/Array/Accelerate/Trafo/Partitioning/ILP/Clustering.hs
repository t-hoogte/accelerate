{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
module Data.Array.Accelerate.Trafo.Partitioning.ILP.Clustering where

import Data.Array.Accelerate.AST.LeftHandSide
import Data.Array.Accelerate.AST.Partitioned
import Data.Array.Accelerate.Trafo.Partitioning.ILP.Graph
import Data.Array.Accelerate.Trafo.Partitioning.ILP.Labels

import qualified Data.Map as M
import Unsafe.Coerce (unsafeCoerce)
import qualified Data.Graph as G
import qualified Data.Set as S
import Data.Function (on)
import Data.Array.Accelerate.AST.Operation
import Data.Maybe (fromJust, fromMaybe)
import Data.Type.Equality


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


topSort :: Graph -> Labels -> ClusterL
topSort (Graph _ fedges _) cluster = topsorted
  where
    cluster' = S.map _labelId cluster
    getLabels = labelMap cluster
    graph :: G.Graph
    graph = G.buildG (minimum cluster', maximum cluster')
          . S.toList
          . S.filter (uncurry ((&&) `on` (`elem` cluster'))) -- filter edges on 'both vertices are in the cluster'
          . S.map (\(Label x _ :-> Label y _) -> (x, y))
          $ fedges
    topsorted = map (getLabels M.!) $ G.topSort graph


openReconstruct :: forall op aenv. LabelEnv aenv -> Graph -> [Labels] -> M.Map Label [Labels] -> M.Map Label (Construction op) -> Exists (PreOpenAcc (Cluster op) aenv)
openReconstruct labelenv graph clusterslist subclustersmap construct = makeAST labelenv clusters
  where
    -- Make a tree of let bindings
    -- TODO every time I use a label here (that comes from a Construction) (and I wrap in [[]]),
    -- should I be using `subclusters`? Go over this again in mkFullGraph too!
    makeAST :: forall env. LabelEnv env -> [ClusterL] -> Exists (PreOpenAcc (Cluster op) env)
    makeAST _ [] = error "empty AST"
    makeAST env [cluster] = case makeCluster env cluster of
      Fold     c (unLabel -> args) -> Exists $ Exec c args
      InitFold o (unLabel -> args) -> Exists $ Exec (unfused o args) args
      NotFold con -> case con of
         CExe {}    -> error "should be Fold/InitFold!"
         CUse se be               -> Exists $ Use se be
         CITE env' c t f   -> case (makeAST env [[t]], makeAST env [[f]]) of
            (Exists tacc, Exists facc) -> Exists $ Acond
              (fromJust $ reindexVar (mkReindexPartial env' env) c)
              -- [See NOTE unsafeCoerce result type]
              (unsafeCoerce @(PreOpenAcc (Cluster op) env _)
                            @(PreOpenAcc (Cluster op) env _)
                            tacc)
              (unsafeCoerce @(PreOpenAcc (Cluster op) env _)
                            @(PreOpenAcc (Cluster op) env _)
                            facc)
         CWhl env' c b i  -> case (makeASTF env c, makeASTF env b) of
            (Exists cfun, Exists bfun) -> Exists $ Awhile
              (error "ask Ivo")
              -- [See NOTE unsafeCoerce result type]
              (unsafeCoerce @(PreOpenAfun (Cluster op) env _)
                            @(PreOpenAfun (Cluster op) env (_ -> PrimBool))
                            cfun)
              (unsafeCoerce @(PreOpenAfun (Cluster op) env _)
                            @(PreOpenAfun (Cluster op) env (_ -> _))
                            bfun)
              (fromJust $ reindexVars (mkReindexPartial env' env) i)
         CLHS {} -> error "let without scope"
         CFun {} -> error "wrong type: function"
         CBod {} -> error "wrong type: function"
    makeAST env (cluster:ctail) = case makeCluster env cluster of
      NotFold con -> case con of
        CLHS glhs b -> case makeAST env [[b]] of -- Is this right???
          Exists bnd -> case makeAST undefined ctail of
            Exists scp -> Exists $ Alet (undefined glhs)
                                         (error "ask Ivo")
                                         bnd
                                         scp
        _ -> undefined
      _ -> undefined

    makeASTF :: forall env. LabelEnv env -> Label -> Exists (PreOpenAfun (Cluster op) env)
    makeASTF env l = case makeCluster env [l] of
      NotFold (CBod l') -> case makeAST env [[l']] of
        Exists acc -> Exists $ Abody acc
      NotFold (CFun env' lhs l') -> case makeASTF undefined l' of
        Exists fun -> Exists $ Alam undefined fun
      NotFold {} -> error "wrong type: acc"
      _ -> error "not a notfold"

    -- do the topological sorting for each set
    clusters = map (topSort graph) clusterslist
    subclusters = M.map (map (topSort graph)) subclustersmap

    makeCluster :: LabelEnv env -> ClusterL -> FoldType op env
    makeCluster env = foldr1 fuseCluster
                    . map ( \l -> case construct M.! l of
                              CExe env' args op -> InitFold op $ fromJust $ reindexLabelledArgs (mkReindexPartial env' env) args --labelled env env' args
                              c                 -> NotFold c
                          )

    fuseCluster :: FoldType op env -> FoldType op env -> FoldType op env
    fuseCluster (Fold cluster1 largs1) (InitFold op2 largs2) =
      consCluster largs1 largs2 cluster1 op2 $ \c largs -> Fold c largs
    fuseCluster (InitFold op largs) x = fuseCluster (Fold (unfused op (unLabel largs)) largs) x
    fuseCluster Fold{} Fold{} = error "fuseCluster got non-leaf as second argument" -- Should never happen
    fuseCluster NotFold{}   _ = error "fuseCluster encountered NotFold" -- Should only occur in singleton clusters
    fuseCluster _   NotFold{} = error "fuseCluster encountered NotFold" -- Should only occur in singleton clusters


-- | Internal datatypes for `makeCluster`.

data FoldType op env
  = forall args. Fold (Cluster op args) (LabelledArgs env args)
  | forall args. InitFold (op args) (LabelledArgs env args) -- like Fold, but without a Swap
  | NotFold (Construction op)




consCluster :: forall env args extra op r
             . LabelledArgs env args
            -> LabelledArgs env extra
            -> Cluster op args
            -> op extra
            -> (forall args'. Cluster op args' -> LabelledArgs env args' -> r)
            -> r
consCluster largs lextra (Cluster cIO cAST) op k =
  mkReverse lextra $ \rev lartxe->
    consCluster' largs rev lartxe cAST (mkBase cIO) cIO
  where
    -- The new, extra operation has args `extra`.
    -- We have already added the args in `added`,
    -- but still need to add the args in `toAdd`.
    -- In total, we now have a (decomposed) cluster of args `total`:
    -- The CIO divides it into `i` and `result`,
    -- The CAST contains the existing computation from `scope` to `result`,
    -- whereas the `LHSArgs` cons' the `added` args in front using `i`.

    -- We simply recurse down the `toAdd` args until `toAdd ~ ()` and
    -- `added ~ extra`, when we can use the extra operation to construct
    -- the total cluster.
    consCluster' :: LabelledArgs env total
                 -> Reverse' extra added toAdd
                 -> LabelledArgs env toAdd
                 -> ClusterAST op scope result
                 -> LeftHandSideArgs added i scope
                 -> ClusterIO total i result
                 -> r
    consCluster' ltot Ordered ArgsNil ast lhs io = k (Cluster io (Bind lhs op ast)) ltot
    consCluster' ltot (Revert r) (a :>: toAdd) ast lhs io = case a of
      L (ArgArray In _ _ _) _ ->
        maybe
          (addInput ast io $ \ast' io' -> -- New input, don't fuse
            consCluster' (a :>: ltot) r toAdd ast' (Reqr Here Here lhs) io')
          (\lhs' -> -- Existing input, fuse horizontally
            consCluster'        ltot  r toAdd ast                  lhs' io)
          (fuseInput a ltot lhs io)
      L (ArgArray Out _ _ _) _ ->
        fromMaybe
          (addOutput ast io $ \ast' io' ->
            consCluster' (a :>: ltot) r toAdd ast' (Make Here lhs) io')
          (fuseOutput a ltot lhs io $ \ltot' io' lhs' ->
            consCluster' ltot' r toAdd ast lhs' io')
      -- TODO mutable arrays, and non-array arguments (which behave like input arrays)
      _ -> undefined


-- Incrementally applying arguments reverses their order, which makes the types messy.
-- As a solution, we first reverse the arguments to be added, so that we end up
-- with the original order! This datatype keeps track of the proof that peeling off args
-- one-by-one from the reversed type yields the original type, which matches the operation.
-- 
-- Building a `Reverse` (and the initial reversing) is awkward, which is why we have `mkReverse`.
-- Using them (peeling off Revert until we're done) is much easier, and happens in the recursion
-- of `consCluster'`.
type Reverse xs sx = Reverse' xs () sx
data Reverse' tot acc rev where
  Ordered :: Reverse' tot     tot       ()
  Revert  :: Reverse' tot (a -> x)      y
          -> Reverse' tot       x (a -> y)

mkReverse :: forall env xs r
           . LabelledArgs env xs
          -> (forall sx. Reverse xs sx -> LabelledArgs env sx -> r)
          -> r
mkReverse xs k = rev Ordered ArgsNil xs
  where
    rev :: Reverse' xs ys zs
        -> LabelledArgs env zs
        -> LabelledArgs env ys
        -> r
    rev a zs ArgsNil = k a zs
    rev a zs (arg :>: args) = rev (Revert a) (arg :>: zs) args

-- Takes care of fusion in the case where we add an input that is already an input: horizontal fusion
fuseInput :: LabelledArg env (In sh e)
          -> LabelledArgs  env total
          -> LeftHandSideArgs added i scope
          -> ClusterIO total i result
          -> Maybe (LeftHandSideArgs (In sh e -> added) i scope)
fuseInput _ ArgsNil _ Empty = Nothing
fuseInput 
  x@(L _ (a1, _))
  ((ArgArray In _ _ _ `L` (a2, _)) :>: as)
  (Ignr lhs)
  (Input io)
  | Just Refl <- matchALabel a1 a2 = 
    Just $ Reqr Here Here lhs
  | otherwise =
    (\(Reqr a b c) -> Reqr (There a) (There b) (Ignr c))
    <$> fuseInput x as lhs io
fuseInput x (_ :>: as) (Make t lhs) (Output _ io) =
    (\(Reqr a b c) -> ttake b t $ \b' t' -> Reqr a b' (Make t' c))
    <$> fuseInput x as lhs io
fuseInput _ _ _ _ = undefined -- TODO mut, non-array args

addInput  :: ClusterAST op scope result
          -> ClusterIO total i result
          -> (forall result'
               . ClusterAST op (scope, e) result'
              -> ClusterIO (In sh e -> total) (i, e) result'
              -> r)
          -> r
addInput None io k = k None (Input io)
addInput (Bind lhs op ast) io k =
  addInput ast io $ \ast' io' ->
    k (Bind (Ignr lhs) op ast') io'

-- Takes care of fusion where we add an output that is later used as input: vertical and diagonal fusion
fuseOutput :: LabelledArg env (Out sh e)
           -> LabelledArgs  env total
           -> LeftHandSideArgs added i scope
           -> ClusterIO total i result
           -> (forall total' i'. LabelledArgs env (Out sh e -> total') -> ClusterIO (Out sh e -> total') i' result -> LeftHandSideArgs (Out sh e -> added) i' scope -> r)
           -> Maybe r
fuseOutput _ ArgsNil _ Empty _ = Nothing
fuseOutput
  x@(L _ (a1, _))
  (y@(ArgArray In _ _ _ `L` (a2, _)) :>: ltot)
  (Ignr lhs)
  (Input io)
  k
  | Just Refl <- matchALabel a1 a2 =
    Just $ k (x :>: ltot) (Output Here io) (Make Here lhs)
  | otherwise =
    fuseOutput x ltot lhs io $ \(x' :>: ltot') (Output t1 io') (Make t2 lhs') ->
      k (x' :>: y :>: ltot') (Output (There t1) $ Input io') (Make (There t2) $ Ignr lhs')

fuseOutput _ _ _ _ _ = undefined -- TODO mut, non-array args

-- :: LabelledArgs env total
-- -> Reverse' extra added toAdd
-- -> LabelledArgs env toAdd
-- -> ClusterAST op scope result
-- -> LeftHandSideArgs added i scope
-- -> ClusterIO total i result

addOutput :: ClusterAST op scope result
          -> ClusterIO total i result
          -> (forall result'
              . ClusterAST op (scope, e) result'
             -> ClusterIO (Out sh e -> total) i result'
             -> r)
          -> r
addOutput None io k = k None (Output Here io)
addOutput (Bind lhs op ast) io k =
  addOutput ast io $ \ast' io' ->
    k (Bind (Ignr lhs) op ast') io'



{- [NOTE unsafeCoerce result type]

  Because we lose some type information by rebuilding the AST from scratch, we use
  unsafeCoerce to tell GHC what the result type of the computation is.
  TypeApplications allows us to specify the exact types unsafeCoerce works on,
  which in turn helps retain as much typesafety as possible. Whereever this note
  is found, unsafeCoerce's type is restricted to only work on the result type.
  In particular, we take care to not allow unsafeCoerce to mess with environment types,
  as they are tricky to get right and we really like GHC agreeing with us there.

-}
