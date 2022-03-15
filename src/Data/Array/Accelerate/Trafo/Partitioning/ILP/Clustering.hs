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

-- _Significantly_ speeds up compilation of this file, but at an obvious cost!
-- Even in GHC 9.0.1, which has Lower Your Guards, these checks take some time (though no longer as long).
-- Recommended to disable these options when working on this file, and restore them when you're done.
{-# OPTIONS_GHC 
  -Wno-overlapping-patterns 
  -Wno-incomplete-patterns 
#-}

module Data.Array.Accelerate.Trafo.Partitioning.ILP.Clustering where

import Data.Array.Accelerate.AST.LeftHandSide ( Exists(..), LeftHandSide (..), lhsToTupR )
import Data.Array.Accelerate.AST.Partitioned hiding (take')
import Data.Array.Accelerate.Representation.Type
import Data.Array.Accelerate.Trafo.Partitioning.ILP.Graph
import Data.Array.Accelerate.Trafo.Partitioning.ILP.Labels

import qualified Data.Map as M
import Unsafe.Coerce (unsafeCoerce)
import qualified Data.Graph as G
import qualified Data.Set as S
import Data.Array.Accelerate.AST.Operation
import Data.Maybe (fromJust, fromMaybe)
import Data.Type.Equality ( type (:~:)(Refl) )
import Data.Array.Accelerate.Trafo.Partitioning.ILP.Solve (ClusterLs (Execs, NonExec))
import Data.Array.Accelerate.AST.Environment (Identity(runIdentity), weakenWithLHS)

import Prelude hiding ( take )
import Lens.Micro (_1)
import Lens.Micro.Extras (view)
import qualified Data.Array.Accelerate.Pretty.Operation as Pretty
import Data.Array.Accelerate.Trafo.LiveVars (SubTupR(SubTupRkeep))
import Data.Array.Accelerate.Representation.Array (arrayRtype)

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
reconstruct :: forall op a. MakesILP op => Graph -> [ClusterLs] -> M.Map Label [ClusterLs] -> M.Map Label (Construction op) -> PreOpenAcc (Cluster op) () a
reconstruct a b c d = case openReconstruct LabelEnvNil a b c d of
          -- see [NOTE unsafeCoerce result type]
          Exists res -> unsafeCoerce @(PartitionedAcc op () _)
                                     @(PartitionedAcc op () a)
                                     res

reconstructF :: forall op a. MakesILP op => Graph -> [ClusterLs] -> M.Map Label [ClusterLs] -> M.Map Label (Construction op) -> PreOpenAfun (Cluster op) () a
reconstructF a b c d = case openReconstructF LabelEnvNil a b (Label 1 Nothing) c d of
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

topSort :: Graph -> Labels -> ClusterL
topSort _ (S.toList -> [l]) = ExecL [l]
topSort (Graph _ fedges _) cluster = ExecL topsorted
  where
    -- graphs are endomorphisms in the Kleisli category of the free semimodule monad
    (graph, getAdj, _) =
          G.graphFromEdges
          . map (\(a,b) -> (a,a,b))
          . M.toList
          . flip (S.fold (\(x :-> y) -> M.adjust (y:) x)) fedges
          . M.fromList
          . map (,[])
          . S.toList
          $ cluster
    topsorted = map (view _1 . getAdj) $ G.topSort graph 

openReconstruct   :: MakesILP op
                  => LabelEnv aenv
                  -> Graph
                  -> [ClusterLs]
                  -> M.Map Label [ClusterLs]
                  -> M.Map Label (Construction op)
                  -> Exists (PreOpenAcc (Cluster op) aenv)
openReconstruct  a b c d e = (\(Left x) -> x) $ openReconstruct' a b c Nothing d e
openReconstructF  :: MakesILP op
                  => LabelEnv aenv
                  -> Graph
                  -> [ClusterLs]
                  -> Label
                  -> M.Map Label [ClusterLs]
                  -> M.Map Label (Construction op)
                  -> Exists (PreOpenAfun (Cluster op) aenv)
openReconstructF a b c l d e= (\(Right x) -> x) $ openReconstruct' a b c (Just l) d e

openReconstruct' :: forall op aenv. MakesILP op => LabelEnv aenv -> Graph -> [ClusterLs] -> Maybe Label -> M.Map Label [ClusterLs] -> M.Map Label (Construction op) -> Either (Exists (PreOpenAcc (Cluster op) aenv)) (Exists (PreOpenAfun (Cluster op) aenv))
openReconstruct' labelenv graph clusterslist mlab subclustersmap construct = case mlab of
  Just l  -> Right $ makeASTF labelenv l mempty
  Nothing -> Left $ makeAST labelenv clusters mempty
  where
    -- Make a tree of let bindings

    -- In mkFullGraph, we make sure that the bound body of a let will be in an earlier cluster.
    -- Those are stored in the 'prev' argument.
    -- Note also that we currently assume that the final cluster is the return argument: If all computations are relevant
    -- and our analysis is sound, the return argument should always appear last. If not.. oops
    makeAST :: forall env. LabelEnv env -> [ClusterL] -> M.Map Label (Exists (PreOpenAcc (Cluster op) env)) -> Exists (PreOpenAcc (Cluster op) env)
    makeAST _ [] _ = error "empty AST"
    makeAST env [cluster] prev = case makeCluster env cluster of
      Fold     c (unLabelOp -> args) -> Exists $ Exec c args
      InitFold o args' -> let args = unLabelOp args' in Exists $ Exec (unfused o (mapArgs getClusterArg args') args) args
      NotFold con -> case con of
         CExe {}    -> error "should be Fold/InitFold!"
         CExe'{}    -> error "should be Fold/InitFold!"
         CUse se  n be             -> Exists $ Use se n be
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
         CWhl env' c b i u -> case (subcluster c, subcluster b) of
           (~[NonExecL c'], ~[NonExecL b']) -> case (makeASTF env c' prev, makeASTF env b' prev) of
            (Exists cfun, Exists bfun) -> Exists $ Awhile
              u
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
    makeAST env (cluster:ctail) prev = 

      case makeCluster env cluster of
      NotFold con -> case con of
        CLHS (mylhs :: MyGLHS a) b u -> case prev M.! b of
          Exists bnd -> createLHS mylhs env $ \env' lhs ->
            case makeAST env' ctail (M.map (\(Exists acc) -> Exists $ weakenAcc lhs acc) prev) of
              Exists scp
                | bnd' <- unsafeCoerce @(PreOpenAcc (Cluster op) env _) -- [See NOTE unsafeCoerce result type]
                                       @(PreOpenAcc (Cluster op) env a)
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

    makeASTF :: forall env. LabelEnv env -> Label -> M.Map Label (Exists (PreOpenAcc (Cluster op) env)) -> Exists (PreOpenAfun (Cluster op) env)
    makeASTF env l prev = case makeCluster env (NonExecL l) of
      NotFold CBod -> case makeAST env (subcluster l) prev of 
        --  fromJust $ l' ^. parent) prev of 
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
    makeCluster env (ExecL ls) =
       foldr1 (flip fuseCluster)
                    $ map ( \l -> case construct M.! l of
                              -- At first thought, this `fromJust` might error if we fuse an array away.
                              -- It does not: The array will still be in the environment, but after we finish
                              -- the `foldr1`, the input argument will dissapear. The output argument does not:
                              -- we clean that up in the SLV pass, if this was vertical fusion. If this is diagonal fusion,
                              -- it stays.
                              CExe env' args op -> InitFold op (fromJust $ reindexLabelledArgsOp (mkReindexPartial env' env) args)
                              _                 -> error "avoid this next refactor" -- c -> NotFold c
                          ) ls
    makeCluster _ (NonExecL l) = NotFold $ construct M.! l

    fuseCluster :: FoldType op env -> FoldType op env -> FoldType op env
    fuseCluster (Fold cluster1 largs1) (InitFold op2 largs2) =
      consCluster largs1 largs2 cluster1 op2 $ \c largs -> Fold c largs
    fuseCluster (InitFold op largs) x = fuseCluster (Fold (unfused op (mapArgs getClusterArg largs) (unLabelOp largs)) largs) x
    fuseCluster Fold{} Fold{} = error "fuseCluster got non-leaf as second argument" -- Should never happen
    fuseCluster NotFold{}   _ = error "fuseCluster encountered NotFold" -- Should only occur in singleton clusters
    fuseCluster _   NotFold{} = error "fuseCluster encountered NotFold" -- Should only occur in singleton clusters

weakenAcc :: LeftHandSide s t env env' -> PreOpenAcc op env a -> PreOpenAcc op env' a
weakenAcc lhs =  runIdentity . reindexAcc (weakenReindex $ weakenWithLHS lhs)


-- | Internal datatype for `makeCluster`.

data FoldType op env
  = forall args. Fold (Cluster op args) (LabelledArgsOp op env args)
  | forall args. InitFold (op args) (LabelledArgsOp op env args) -- like Fold, but without a Swap
  | NotFold (Construction op)



-- TODO: use the typeclass for `op`, or move order variables into the default ILP
-- either way: make each array arg also know its order, and check for them in the
-- happy paths for fusion. This ensures that we properly duplicate the arguments.
-- TOTHINK: this makes work duplication a bit trickier still: the ILP solution interpreter
-- would need to do nontrivial stuff to actually duplicate the entire Exec node?
-- Then again, maybe we already need to put operations that could be duplicated in the ILP twice,
-- and have a simple decision variable that indicates whether they are identical.
-- Then, the ILP solution interpreter would only need to combine non-duplicated nodes, which seems easier.
-- Question: How do we _find_ nodes that can be duplicated, and how do we duplicate them in the ILP formulation?
-- And if there is a 5*5 stencil after a map, do we really add 25 versions of this map to the ILP?
-- #futurework
consCluster :: forall env args extra op r
             . MakesILP op
            => LabelledArgsOp op env args
            -> LabelledArgsOp op env extra
            -> Cluster op args
            -> op extra
            -> (forall args'. Cluster op args' -> LabelledArgsOp op env args' -> r)
            -> r
consCluster largs lextra ((Cluster b (Cluster' cIO cAST))) op k =
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
    -- the total cluster. All results are passed in these accumulating parameters.

    -- In each step, we check whether the argument array is already mentioned
    -- in the operations that follow it: If so, we fuse them (making both arguments
    -- point to the same place in the environment), otherwise we simply add a new one. 

    -- note that this function has a lot of type safety (recursing wrongly is very difficult),
    -- except for two details: Whether or not to fuse is a choice, and the call to `k`
    -- works with any cluster/args. The first requires diligence, the second occurs
    -- only in the very first line (which is, visually, correct).
    consCluster' :: LabelledArgsOp op env total
                 -> Reverse' extra added toAdd
                 -> LabelledArgsOp op env toAdd
                 -> ClusterAST op scope result
                 -> LeftHandSideArgs added i scope
                 -> ClusterIO total i result
                 -> r
    consCluster' ltot Ordered ArgsNil ast lhs io = k (Cluster (mapArgs getClusterArg ltot) (Cluster' io (Bind lhs op ast))) ltot
    consCluster' ltot (Revert r) (a :>: toAdd) ast lhs io = case a of
      LOp (ArgArray In _ _ _) _ _ ->
        maybe
          (addInput ast io $ \ast' io' -> -- New input, don't fuse
            consCluster' (a :>: ltot) r toAdd ast' (Reqr Here Here lhs) io')
          (\lhs' -> -- Existing input, fuse horizontally
            consCluster'        ltot  r toAdd ast                  lhs' io)
          (fuseInput a ltot lhs io)
      LOp (ArgArray Out (arrayRtype -> r') _ _) _ _ ->
        fromMaybe
          (addOutput r' ast io $ \ast' io' -> -- new output
            consCluster' (a :>: ltot) r toAdd ast' (Make Here lhs) io')
          (fuseOutput a ltot lhs io $ \take' lhs' io' _ -> -- diagonal fusion
            -- note that we prepend 'a': The fused cluster only outputs this arg
            consCluster' (a :>: foo take' ltot) r toAdd ast lhs' io')
      -- non-array arguments
      LOp (ArgExp _) _ _ -> addExp ast io ExpPut $ \ast' io' ->
        consCluster' (a :>: ltot) r toAdd ast' (EArg lhs) io'
      LOp (ArgVar _) _ _ -> addExp ast io VarPut $ \ast' io' ->
        consCluster' (a :>: ltot) r toAdd ast' (VArg lhs) io'
      LOp (ArgFun _) _ _ -> addExp ast io FunPut $ \ast' io' ->
        consCluster' (a :>: ltot) r toAdd ast' (FArg lhs) io'
      LOp (ArgArray Mut _ _ _) _ _ -> addExp ast io MutPut $ \ast' io' ->
        consCluster' (a :>: ltot) r toAdd ast' (Adju lhs) io'

-- remove an argument
foo :: Take' (x sh e) total total' -> LabelledArgsOp op env total -> PreArgs (LabelledArgOp op env) total'
foo Here' (_ :>: as) = as
foo (There' t) (a :>: as) = a :>: foo t as


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

mkReverse :: forall env xs op r
           . LabelledArgsOp op env xs
          -> (forall sx. Reverse xs sx -> LabelledArgsOp op env sx -> r)
          -> r
mkReverse xs k = rev Ordered ArgsNil xs
  where
    rev :: Reverse' xs ys zs
        -> LabelledArgsOp op env zs
        -> LabelledArgsOp op env ys
        -> r
    rev a zs ArgsNil = k a zs
    rev a zs (arg :>: args) = rev (Revert a) (arg :>: zs) args

-- Takes care of fusion in the case where we add an input that is already an 
-- input: horizontal fusion
-- Note that we assume that it can occur at most once: We uphold this invariant
-- by correctly fusing in every step.
fuseInput :: MakesILP op 
          => LabelledArgOp op env (In sh e)
          -> LabelledArgsOp op  env total
          -> LeftHandSideArgs added i scope
          -> ClusterIO total i result
          -> Maybe (LeftHandSideArgs (In sh e -> added) i scope)
-- Base case, no fusion
fuseInput _ ArgsNil _ Empty = Nothing
-- The happy path: Fusion!
fuseInput
  (LOp _ (a1, _) o1)
  (LOp (ArgArray In _ _ _) (a2, _) o2 :>: _)
  (Ignr lhs)
  (Input _)
  | Just Refl <- matchALabel a1 a2
  , o1 == o2 =
    Just $ Reqr Here Here lhs
-- The rest are recursive cases
fuseInput x (_ :>: as) (Make t lhs) (Output _ _ _ io) =
  (\(Reqr a b c) -> ttake b t $ \b' t' -> Reqr (There a) b' (Make t' c))
  <$> fuseInput x as lhs io
fuseInput x as (Reqr t t2 lhs) io =
  removeInput as t io $ \as' io' _ _ _ ->
    (\(Reqr a b c) ->
      ttake b t2 $ \b' t2' ->
        ttake a t $ \a' t'' ->
          Reqr a' b' $ Reqr t'' t2' c)
    <$> fuseInput x as' lhs io'
fuseInput x (_ :>: as) (Adju lhs) (MutPut io) = (\(Reqr a b c) -> Reqr (There a) (There b) $ Adju c) <$> fuseInput x as lhs io
fuseInput x (_ :>: as) (EArg lhs) (ExpPut' io) = (\(Reqr a b c) -> Reqr (There a) (There b) $ EArg c) <$> fuseInput x as lhs io
fuseInput x (_ :>: as) (VArg lhs) (ExpPut' io) = (\(Reqr a b c) -> Reqr (There a) (There b) $ VArg c) <$> fuseInput x as lhs io
fuseInput x (_ :>: as) (FArg lhs) (ExpPut' io) = (\(Reqr a b c) -> Reqr (There a) (There b) $ FArg c) <$> fuseInput x as lhs io
-- Ignore cases that don't get fused
fuseInput x (_ :>: as) (Ignr lhs) (Output _ _ _ io) =
  (\(Reqr a b c) -> Reqr (There a) (There b) (Ignr c))
  <$> fuseInput x as lhs io
fuseInput x (_ :>: as) (Ignr lhs) (Input io) =
  (\(Reqr a b c) -> Reqr (There a) (There b) (Ignr c))
  <$> fuseInput x as lhs io
fuseInput x (_ :>: as) (Ignr lhs) (MutPut io) =
  (\(Reqr a b c) -> Reqr (There a) (There b) (Ignr c))
  <$> fuseInput x as lhs io
fuseInput x (_ :>: as) (Ignr lhs) (ExpPut' io) =
  (\(Reqr a b c) -> Reqr (There a) (There b) (Ignr c))
  <$> fuseInput x as lhs io
fuseInput x (_ :>: as) (Make t lhs) (Vertical _ _ io) =
  (\(Reqr a b c) -> ttake b t $ \b' t' -> Reqr (There a) b' (Make t' c))
  <$> fuseInput x as lhs io
fuseInput x (_ :>: as) (Ignr lhs) (Vertical _ _ io) =
  (\(Reqr a b c) -> Reqr (There a) (There b) (Ignr c))
  <$> fuseInput x as lhs io

removeInput :: forall op env total e i i' result r sh
             . LabelledArgsOp op  env total
            -> Take (Value sh e) i i'
            -> ClusterIO total i result
            -> (forall total' result'
               . LabelledArgsOp op env total'
              -> ClusterIO total' i' result'
              -> Take (Value sh e) result result'
              -> Take' (In sh e) total total'
              -> LabelledArgOp op env (In sh e)
              -> r)
            -> r
removeInput (a :>: xs) Here (Input io) k =
  k xs io Here Here' a
removeInput (x :>: xs) (There t) (Input io) k =
  removeInput xs t io $ \xs' io' t' t'' a ->
    k (x :>: xs') (Input io') (There t') (There' t'') a
removeInput (x :>: xs) (There t) (Output t1 s r io) k =
  removeInput xs t io $ \xs' io' t' t'' a ->
    ttake t' t1 $ \t2 t3 ->
      k (x :>: xs') (Output t3 s r io') t2 (There' t'') a
removeInput (x :>: xs) (There t) (MutPut io) k =
  removeInput xs t io $ \xs' io' t' t'' a ->
    k (x :>: xs') (MutPut io') (There t') (There' t'') a
removeInput (x :>: xs) (There t) (ExpPut io) k =
  removeInput xs t io $ \xs' io' t' t'' a ->
    k (x :>: xs') (ExpPut io') (There t') (There' t'') a
removeInput (x :>: xs) (There t) (VarPut io) k =
  removeInput xs t io $ \xs' io' t' t'' a ->
    k (x :>: xs') (VarPut io') (There t') (There' t'') a
removeInput (x :>: xs) (There t) (FunPut io) k =
  removeInput xs t io $ \xs' io' t' t'' a ->
    k (x :>: xs') (FunPut io') (There t') (There' t'') a
removeInput (x :>: xs) (There t) (Vertical t1 r io) k =
  removeInput xs t io $ \xs' io' t' t'' a ->
    ttake t' t1 $ \t2 t3 ->
      k (x :>: xs') (Vertical t3 r io') t2 (There' t'') a


restoreInput :: ClusterIO total' i' result'
             -> Take' (In sh e) total total'
             -> Take (Value sh e) i i'
             -> Take (Value sh e) result result'
             -> LabelledArgOp op env (In sh e)
             -> ClusterIO total i result
restoreInput cio Here' Here Here (LOp (ArgArray In  _ _ _) _ _) = Input cio
restoreInput (Input    cio) (There' tt) (There ti) (There tr) x =
  Input     $ restoreInput cio tt ti tr x
restoreInput (ExpPut   cio) (There' tt) (There ti) (There tr) x =
  ExpPut    $ restoreInput cio tt ti tr x
restoreInput (Output t s r cio) (There' tt) (There ti)        tr  x =
  ttake t tr $ \t' tr' ->
    Output t' s r $ restoreInput cio tt ti tr' x
restoreInput (MutPut   cio) (There' tt) (There ti) (There tr) x =
  MutPut    $ restoreInput cio tt ti tr x
restoreInput _ _ _ _ _ = error "I think this means that the take(')s in restoreInput don't agree with each other"

addInput  :: ClusterAST op scope result
          -> ClusterIO total i result
          -> (forall result'
             . ClusterAST op (scope, Value sh e) result'
            -> ClusterIO (In sh e -> total) (i, Value sh e) result'
            -> r)
          -> r
addInput None io k = k None (Input io)
addInput (Bind lhs op ast) io k =
  addInput ast io $ \ast' io' ->
    k (Bind (Ignr lhs) op ast') io'

-- use one of the IO constructors (ExpPut, VarPut, FunPut) as third argument
addExp  :: ClusterAST op scope result
        -> ClusterIO total i result
        -> (forall total' i' result'. ClusterIO total' i' result' -> ClusterIO (e -> total') (i', e) (result', e))
        -> (forall result'
              . ClusterAST op (scope, e) result'
            -> ClusterIO (e -> total) (i, e) result'
            -> r)
        -> r
addExp None io constructor k = k None (constructor io)
addExp (Bind lhs op ast) io constructor k =
  addExp ast io constructor $ \ast' io' ->
    k (Bind (Ignr lhs) op ast') io'

-- Takes care of fusion where we add an output that is later used as input: vertical and diagonal fusion
-- Note that we assume that it can occur at most once: We uphold this invariant
-- by correctly fusing in every step.
fuseOutput :: MakesILP op
           => LabelledArgOp op env (Out sh e)
           -> LabelledArgsOp op  env total
           -> LeftHandSideArgs added i scope
           -> ClusterIO total i result
           -> (forall total' i'
               . Take' (In sh e) total total'
              -> LeftHandSideArgs (Out sh e -> added)  (i', Sh sh e) scope
              -> ClusterIO        (Out sh e -> total') (i', Sh sh e) result
              -> Take (Value sh e) i i'
              -> r)
           -> Maybe r
-- Base case, no fusion
fuseOutput _ ArgsNil Base Empty _ = Nothing
-- Fusion!
fuseOutput
  (LOp _ (a1, _) o1)
  (LOp (ArgArray In r _ _) (a2, _) o2 :>: _)
  (Ignr lhs)
  (Input io)
  k
  | Just Refl <- matchALabel a1 a2
  , o1 == o2 =
    Just $ k Here' (Make Here lhs) (Output Here SubTupRkeep (arrayRtype r) io) Here

-- Make case
fuseOutput x (_ :>: as) (Make t1 lhs) (Output t2 s r io) k =
  fuseOutput x as lhs io $ \t' (Make t3 lhs') (Output t4 s' r' io') t ->
    ttake t3 t1 $ \t3' t1' ->
      ttake t4 t2 $ \t4' t2' ->
        k (There' t') (Make t3' $ Make t1' lhs') (Output t4' s' r' $ Output t2' s r io') (There t)
fuseOutput x (_ :>: as) (Make t1 lhs) (Vertical t2 r' io) k =
  fuseOutput x as lhs io $ \t' (Make t3 lhs') (Output t4 s r io') t ->
    ttake t3 t1 $ \t3' t1' ->
      ttake t4 t2 $ \t4' t2' ->
        k (There' t') (Make t3' $ Make t1' lhs') (Output t4' s r $ Vertical t2' r' io') (There t)
-- The Reqr case is difficult: we use `removeInput` to recurse past the `Reqr`, but
-- (other than in fuseInput) we have to pass the result of recursing through
-- `restoreInput` to reassemble the CIO. More elegant (no error cases) would be to
-- defunctionalise the effect on the CIO (just like Take and Take' do), but that's a heavy hammer.
fuseOutput x as (Reqr t1 t2 lhs) io k =
  removeInput as t1 io $ \as' io' t3 take' removed ->
    fuseOutput x as' lhs io' $ \take'' (Make t4 lhs') (Output t5 s r io'') t ->
      ttake t t1 $ \t' t1' ->
        ttake t4 t2 $ \t4' t2' ->
          ttake t5 t3 $ \t5' t3' ->
            ttake' take'' take' $ \take1' take2' ->
              k take1' (Make t4' $ Reqr t1' t2' lhs') (Output t5' s r $ restoreInput io'' take2' t1' t3' removed) t'
-- Ignr cases, note that we can ignore empty list, Base and Output
fuseOutput x (_ :>: as) (Ignr lhs) (Input io) k =
  fuseOutput x as lhs io $ \t' (Make t1 lhs') (Output t2 s r io') t ->
    k (There' t') (Make (There t1) $ Ignr lhs') (Output (There t2) s r $ Input io') (There t)
fuseOutput x (_ :>: as) (Ignr lhs) (Vertical t r' io) k =
  fuseOutput x as lhs io $ \t' (Make t1 lhs') (Output t2 s r io') t3 ->
    ttake t2 t $ \t2' t'' ->
      k (There' t') (Make (There t1) $ Ignr lhs') (Output t2' s r $ Vertical t'' r' io') (There t3)
fuseOutput x (_ :>: as) (Ignr lhs) (MutPut io) k =
  fuseOutput x as lhs io $ \t' (Make t1 lhs') (Output t2 s r io') t ->
    k (There' t') (Make (There t1) $ Ignr lhs') (Output (There t2) s r $ MutPut io') (There t)
fuseOutput x (_ :>: as) (Ignr lhs) (ExpPut io) k =
  fuseOutput x as lhs io $ \t' (Make t1 lhs') (Output t2 s r io') t ->
    k (There' t') (Make (There t1) $ Ignr lhs') (Output (There t2) s r $ ExpPut io') (There t)
fuseOutput x (_ :>: as) (Ignr lhs) (VarPut io) k =
  fuseOutput x as lhs io $ \t' (Make t1 lhs') (Output t2 s r io') t ->
    k (There' t') (Make (There t1) $ Ignr lhs') (Output (There t2) s r $ VarPut io') (There t)
fuseOutput x (_ :>: as) (Ignr lhs) (FunPut io) k =
  fuseOutput x as lhs io $ \t' (Make t1 lhs') (Output t2 s r io') t ->
    k (There' t') (Make (There t1) $ Ignr lhs') (Output (There t2) s r $ FunPut io') (There t)
fuseOutput x (_ :>: as) (Ignr lhs) (Output t1 s' r' io) k =
  fuseOutput x as lhs io $ \t' (Make t2 lhs') (Output t3 s r io') t ->
    ttake t3 t1 $ \t3' t1' ->
      k (There' t') (Make (There t2) $ Ignr lhs') (Output t3' s r (Output t1' s' r' io')) (There t)
-- EArg goes just like Ignr
fuseOutput x (_ :>: as) (EArg lhs) (ExpPut io) k =
  fuseOutput x as lhs io $ \t' (Make t1 lhs') (Output t2 s r io') t ->
    k (There' t') (Make (There t1) $ EArg lhs') (Output (There t2) s r $ ExpPut io') (There t)
fuseOutput x (_ :>: as) (VArg lhs) (VarPut io) k =
  fuseOutput x as lhs io $ \t' (Make t1 lhs') (Output t2 s r io') t ->
    k (There' t') (Make (There t1) $ VArg lhs') (Output (There t2) s r $ VarPut io') (There t)
fuseOutput x (_ :>: as) (FArg lhs) (FunPut io) k =
  fuseOutput x as lhs io $ \t' (Make t1 lhs') (Output t2 s r io') t ->
    k (There' t') (Make (There t1) $ FArg lhs') (Output (There t2) s r $ FunPut io') (There t)
-- Adju is like EArg
fuseOutput x (_ :>: as) (Adju lhs) (MutPut io) k =
  fuseOutput x as lhs io $ \t' (Make t1 lhs') (Output t2 s r io') t ->
    k (There' t') (Make (There t1) $ Adju lhs') (Output (There t2) s r $ MutPut io') (There t)


addOutput :: TypeR e
          -> ClusterAST op scope result
          -> ClusterIO total i result
          -> (forall result'
              . ClusterAST op (scope, Value sh e) result'
             -> ClusterIO (Out sh e -> total) (i, Sh sh e) result'
             -> r)
          -> r
addOutput r None io k = k None (Output Here SubTupRkeep r io)
addOutput r (Bind lhs op ast) io k =
  addOutput r ast io $ \ast' io' ->
    k (Bind (Ignr lhs) op ast') io'

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
