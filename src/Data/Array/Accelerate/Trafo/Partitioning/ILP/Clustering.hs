{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE LambdaCase #-}
module Data.Array.Accelerate.Trafo.Partitioning.ILP.Clustering where

import Data.Array.Accelerate.AST.LeftHandSide ( Exists(..), LeftHandSide )
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
import Data.Type.Equality ( type (:~:)(Refl) )
import Data.Array.Accelerate.Trafo.Partitioning.ILP.Solve (ClusterLs (Execs, NonExec))
import Data.Array.Accelerate.AST.Environment (Identity(runIdentity), weakenWithLHS)
import Control.Applicative


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
reconstruct :: forall op a. Graph -> [ClusterLs] -> M.Map Label [ClusterLs] -> M.Map Label (Construction op) -> PreOpenAcc (Cluster op) () a
reconstruct a b c d = case openReconstruct LabelEnvNil a b c d of
          -- see [NOTE unsafeCoerce result type]
          Exists res -> unsafeCoerce @(PartitionedAcc op () _)
                                     @(PartitionedAcc op () a)
                                     res

-- ordered list of labels
data ClusterL = ExecL [Label] | NonExecL Label

foldC :: (Label -> b -> b) -> b -> ClusterL -> b
foldC f x (ExecL ls) = foldr f x ls
foldC f x (NonExecL l) = f l x

topSort :: Graph -> Labels -> ClusterL
topSort (Graph _ fedges _) cluster = ExecL topsorted
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


openReconstruct :: forall op aenv. LabelEnv aenv -> Graph -> [ClusterLs] -> M.Map Label [ClusterLs] -> M.Map Label (Construction op) -> Exists (PreOpenAcc (Cluster op) aenv)
openReconstruct labelenv graph clusterslist subclustersmap construct = makeAST labelenv clusters mempty
  where
    -- Make a tree of let bindings

    -- In mkFullGraph, we make sure that the bound body of a let will be in an earlier cluster.
    -- Those are stored in the 'prev' argument.
    -- Note also that we currently assume that the final cluster is the return argument: If all computations are relevant
    -- and our analysis is sound, the return argument should always appear last. If not.. oops
    makeAST :: forall env. LabelEnv env -> [ClusterL] -> M.Map Label (Exists (PreOpenAcc (Cluster op) env)) -> Exists (PreOpenAcc (Cluster op) env)
    makeAST _ [] _ = error "empty AST"
    makeAST env [cluster] prev = case makeCluster env cluster of
      Fold     c (unLabel -> args) -> Exists $ Exec c args
      InitFold o (unLabel -> args) -> Exists $ Exec (unfused o args) args
      NotFold con -> case con of
         CExe {}    -> error "should be Fold/InitFold!"
         CUse se be               -> Exists $ Use se be
         CITE env' c t f   -> case (makeAST env (subcluster t) prev, makeAST env (subcluster f) prev) of
            (Exists tacc, Exists facc) -> Exists $ Acond
              (fromJust $ reindexVar (mkReindexPartial env' env) c)
              -- [See NOTE unsafeCoerce result type]
              (unsafeCoerce @(PreOpenAcc (Cluster op) env _)
                            @(PreOpenAcc (Cluster op) env _)
                            tacc)
              (unsafeCoerce @(PreOpenAcc (Cluster op) env _)
                            @(PreOpenAcc (Cluster op) env _)
                            facc)
         CWhl env' c b i  -> case (makeASTF env c prev, makeASTF env b prev) of
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
         CRet env' vars     -> Exists $ Return      (fromJust $ reindexVars (mkReindexPartial env' env) vars)
         CCmp env' expr     -> Exists $ Compute     (fromJust $ reindexExp  (mkReindexPartial env' env) expr)
         CAlc env' shr e sh -> Exists $ Alloc shr e (fromJust $ reindexVars (mkReindexPartial env' env) sh)
         CUnt env' evar     -> Exists $ Unit        (fromJust $ reindexVar  (mkReindexPartial env' env) evar)
    makeAST env (cluster:ctail) prev = case makeCluster env cluster of
      NotFold con -> case con of
        CLHS (mylhs :: MyGLHS a) b -> case prev M.! b of
          Exists bnd -> createLHS mylhs env $ \env' lhs ->
            case makeAST env' ctail (M.map (\(Exists acc) -> Exists $ weakenAcc lhs acc) prev) of
              Exists scp -> Exists $ Alet lhs
                                          (error "ask Ivo")
                                          -- [See NOTE unsafeCoerce result type]
                                          (unsafeCoerce @(PreOpenAcc (Cluster op) env _)
                                                        @(PreOpenAcc (Cluster op) env a)
                                                        bnd)
                                          scp
        _ -> makeAST env ctail $ foldC (`M.insert` makeAST env [cluster] prev) prev cluster
      _   -> makeAST env ctail $ foldC (`M.insert` makeAST env [cluster] prev) prev cluster

    makeASTF :: forall env. LabelEnv env -> Label -> M.Map Label (Exists (PreOpenAcc (Cluster op) env)) -> Exists (PreOpenAfun (Cluster op) env)
    makeASTF env l prev = case makeCluster env (NonExecL l) of
      NotFold (CBod l') -> case makeAST env (subcluster l') prev of
        Exists acc -> Exists $ Abody acc
      NotFold (CFun lhs l') -> createLHS lhs env $ \env' lhs' -> case makeASTF env' l' (M.map (\(Exists acc) -> Exists $ weakenAcc lhs' acc) prev) of
        Exists fun -> Exists $ Alam lhs' fun
      NotFold {} -> error "wrong type: acc"
      _ -> error "not a notfold"

    -- do the topological sorting for each set
    clusters = map (\case
                      Execs ls -> topSort graph ls
                      NonExec l -> NonExecL l) clusterslist
    subclusters = M.map (map ( \case
                      Execs ls -> topSort graph ls
                      NonExec l -> NonExecL l)) subclustersmap
    subcluster l = subclusters M.! l

    makeCluster :: LabelEnv env -> ClusterL -> FoldType op env
    makeCluster env (ExecL ls) = foldr1 fuseCluster
                    $ map ( \l -> case construct M.! l of
                              CExe env' args op -> InitFold op $ fromJust $ reindexLabelledArgs (mkReindexPartial env' env) args --labelled env env' args
                              _                 -> error "avoid this next refactor" -- c -> NotFold c
                          ) ls
    makeCluster _ (NonExecL l) = NotFold $ construct M.! l

    fuseCluster :: FoldType op env -> FoldType op env -> FoldType op env
    fuseCluster (Fold cluster1 largs1) (InitFold op2 largs2) =
      consCluster largs1 largs2 cluster1 op2 $ \c largs -> Fold c largs
    fuseCluster (InitFold op largs) x = fuseCluster (Fold (unfused op (unLabel largs)) largs) x
    fuseCluster Fold{} Fold{} = error "fuseCluster got non-leaf as second argument" -- Should never happen
    fuseCluster NotFold{}   _ = error "fuseCluster encountered NotFold" -- Should only occur in singleton clusters
    fuseCluster _   NotFold{} = error "fuseCluster encountered NotFold" -- Should only occur in singleton clusters

weakenAcc :: LeftHandSide s t env env' -> PreOpenAcc op env a -> PreOpenAcc op env' a
weakenAcc lhs =  runIdentity . reindexAcc (weakenReindex $ weakenWithLHS lhs)


-- | Internal datatype for `makeCluster`.

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

    -- In each step, we check whether the argument array is already mentioned
    -- in the operations that follow it: If so, we fuse them (making both arguments
    -- point to the same place in the environment), otherwise we simply add a new one. 
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
          (addOutput ast io $ \ast' io' -> -- new output
            consCluster' (a :>: ltot) r toAdd ast' (Make Here lhs) io')
          (fuseOutput a ltot lhs io $ \ltot' io' lhs' -> -- diagonal fusion
            consCluster' ltot' r toAdd ast lhs' io')
      -- TODO mutable arrays
      L (ArgArray Mut _ _ _) _ -> undefined
      -- non-array arguments
      _ -> addNonArr ast io $ \ast' io' ->
        consCluster' (a :>: ltot) r toAdd ast' (EArg lhs) io'


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
-- TODO horizontal fusion of input with existing mutput
fuseInput :: LabelledArg env (In sh e)
          -> LabelledArgs  env total
          -> LeftHandSideArgs added i scope
          -> ClusterIO total i result
          -> Maybe (LeftHandSideArgs (In sh e -> added) i scope)
-- Base case, no fusion
fuseInput _ ArgsNil _ Empty = Nothing

-- The happy path: Fusion!
fuseInput
  (L _ (a1, _))
  ((ArgArray In _ _ _ `L` (a2, _)) :>: _)
  (Ignr lhs)
  (Input _)
  | Just Refl <- matchALabel a1 a2 =
    Just $ Reqr Here Here lhs

-- The rest are recursive cases
fuseInput x (_ :>: as) lhs (Output _ io) = 
  fuseInput x as lhs io
fuseInput x as (Make t lhs) io =
  (\(Reqr a b c) -> ttake b t $ \b' t' -> Reqr a b' (Make t' c))
  <$> fuseInput x as lhs io

fuseInput x as (Reqr t t2 lhs) io =
  removeInput as t io $ \as' io' _ ->
    (\(Reqr a b c) -> 
      ttake b t2 $ \b' t2' -> 
        ttake a t $ \a' t'' -> 
          Reqr a' b' $ Reqr t'' t2' c) 
    <$> fuseInput x as' lhs io'

fuseInput x as (Adju t t2 lhs) io =
  removeInput as t io $ \as' io' _ ->
    (\(Reqr a b c) ->
      ttake b t2 $ \b' t2' ->
        ttake a t $ \a' t'' ->
          Reqr a' b' $ Adju t'' t2' c)
    <$> fuseInput x as' lhs io'

fuseInput x as (EArg lhs) io = 
  removeInput as Here io $ \as' io' Here ->
    (\(Reqr a b c) -> Reqr (There a) (There b) $ EArg c)
    <$> fuseInput x as' lhs io'

-- Ignore cases that don't get fused
fuseInput x (_ :>: as) (Ignr lhs) (Input io) =
  (\(Reqr a b c) -> Reqr (There a) (There b) (Ignr c))
  <$> fuseInput x as lhs io
fuseInput x (_ :>: as) (Ignr lhs) (MutPut _ io) =
  (\(Reqr a b c) -> Reqr (There a) (There b) (Ignr c))
  <$> fuseInput x as lhs io
fuseInput x (_ :>: as) (Ignr lhs) (ExpPut io) = 
  (\(Reqr a b c) -> Reqr (There a) (There b) (Ignr c))
  <$> fuseInput x as lhs io


removeInput :: LabelledArgs  env total
            -> Take e i i'
            -> ClusterIO total i result
            -> (forall total' result'
               . LabelledArgs env total' 
              -> ClusterIO total' i' result'
              -> Take e result result'
              -> r)
            -> r
removeInput (_ :>: xs) Here (Input io) k = k xs io Here
removeInput (x :>: xs) (There t) (Input io) k =
  removeInput xs t io $ \xs' io' t' ->
    k (x :>: xs') (Input io') (There t')
removeInput (x :>: xs) t (Output t1 io) k = 
  removeInput xs t io $ \xs' io' t' -> 
    ttake t' t1 $ \t2 t3 -> 
      k (x :>: xs') (Output t3 io') t2
removeInput (_ :>: xs) Here (MutPut t1 io) k = k xs io t1
removeInput (x :>: xs) (There t) (MutPut t1 io) k =
  removeInput xs t io $ \xs' io' t' ->
    ttake t' t1 $ \t2 t3 ->
      k (x :>: xs') (MutPut t3 io') t2
removeInput _ Here (ExpPut _) _ = error "nope"
removeInput (x :>: xs) (There t) (ExpPut io) k = 
  removeInput xs t io $ \xs' io' t' -> 
    k (x :>: xs') (ExpPut io') (There t')

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

addNonArr :: ClusterAST op scope result
          -> ClusterIO total i result
          -> (forall result'
               . ClusterAST op (scope, e) result'
              -> ClusterIO (e -> total) (i, e) result'
              -> r)
          -> r
addNonArr None io k = k None (ExpPut io)
addNonArr (Bind lhs op ast) io k =
  addNonArr ast io $ \ast' io' ->
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

-- oneDown :: LeftHandSideArgs body env scope -> 
--   (forall arg body' env' scope'. LeftHandSideArgs body' env' scope' -> (LeftHandSideArgs (*) (*) (*)))


{- [NOTE unsafeCoerce result type]

  Because we lose some type information by rebuilding the AST from scratch, we use
  unsafeCoerce to tell GHC what the result type of the computation is.
  TypeApplications allows us to specify the exact types unsafeCoerce works on,
  which in turn helps retain as much typesafety as possible. Whereever this note
  is found, unsafeCoerce's type is restricted to only work on the result type.
  In particular, we take care to not allow unsafeCoerce to mess with environment types,
  as they are tricky to get right and we really want GHC to check our work.

-}
