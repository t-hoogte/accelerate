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
import Data.Maybe (fromJust)


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
openReconstruct labelenv graph clusterslist subclustersmap construct = undefined
  where
    -- Make a tree of let bindings
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
              (error "call Ivo")
              -- [See NOTE unsafeCoerce result type]
              (unsafeCoerce @(PreOpenAfun (Cluster op) env _)
                            @(PreOpenAfun (Cluster op) env (_ -> PrimBool))
                            cfun)
              (unsafeCoerce @(PreOpenAfun (Cluster op) env _)
                            @(PreOpenAfun (Cluster op) env (_ -> _))
                            bfun)
              (fromJust $ reindexVars (mkReindexPartial env' env) i)
         CLHS {} -> error "This doesn't make sense, rethink `mkFullGraph @Alet`"
         CFun {} -> error "wrong type: function"
         CBod {} -> error "wrong type: function"
    makeAST env (cluster:tail) = undefined

    makeASTF :: forall env. LabelEnv env -> Label -> Exists (PreOpenAfun (Cluster op) env)
    makeASTF env l = case makeCluster env [l] of
      NotFold (CBod l') -> case makeAST env [[l']] of
        Exists acc -> Exists $ Abody acc
      NotFold (CFun env' lhs l') -> case makeASTF _ l' of
        Exists fun -> Exists $ Alam _ fun
      NotFold {} -> error "wrong type: acc"
      _ -> error "not a notfold"

    -- do the topological sorting for each set
    clusters = map (topSort graph) clusterslist
    subclusters = M.map (map (topSort graph)) subclustersmap

    makeCluster :: LabelEnv env -> ClusterL -> FoldType op env
    makeCluster env = foldr1 fuseCluster
                    . map ( \l -> case construct M.! l of
                              CExe env' args op -> InitFold op $ labelled env env' args
                              c                 -> NotFold c
                          )

    fuseCluster :: FoldType op env -> FoldType op env -> FoldType op env
    fuseCluster (Fold cluster1 largs1) (InitFold op2 largs2) =
      consCluster largs1 largs2 cluster1 op2 $ \c largs -> Fold c largs
    fuseCluster (InitFold op largs) x = fuseCluster (Fold (unfused op (unLabel largs)) largs) x
    fuseCluster Fold{} Fold{} = error "fuseCluster got non-leaf as second argument" -- Should never happen
    fuseCluster NotFold{}   _ = error "fuseCluster encountered NotFold" -- Should only occur in singleton clusters
    fuseCluster _   NotFold{} = error "fuseCluster encountered NotFold" -- Should only occur in singleton clusters


labelled :: LabelEnv env -> LabelEnv env1 -> Args env1 args -> LabelledArgs env args
labelled env env' args = getLabelArgs (fromJust $ reindexArgs (mkReindexPartial env' env) args) env



-- | Internal datatypes for `makeCluster`.

data FoldType op env
  = forall args. Fold (Cluster op args) (LabelledArgs env args)
  | forall args. InitFold (op args) (LabelledArgs env args) -- like Fold, but without a Swap
  | NotFold (Construction op)



-- TODO write. Induction on the cluster or the extra?
consCluster :: LabelledArgs env args
            -> LabelledArgs env extra
            -> Cluster op args
            -> op extra
            -> (forall args'. Cluster op args' -> LabelledArgs env args' -> r)
            -> r
consCluster largs lextra (Cluster io ast) = 
  consCluster' largs lextra ArgsNil (io, ast) id Base (mkConsists $ unLabel lextra) Done
-- consCluster _ lextra (Cluster Empty None) extra k = k (unfused extra (unLabel lextra)) lextra
-- consCluster largs ArgsNil (Cluster io ast) extra k = k (Cluster io (Bind Base extra ast)) largs
-- consCluster largs (x :>: lextra) (Cluster io ast) extra k =
--   consCluster largs      lextra  (Cluster io ast) extra $ \cluster ltot -> 
--     k _ _


consCluster' :: LabelledArgs env args
             -> LabelledArgs env toAdd
             -> LabelledArgs env added
             -> (ClusterIO args i o, ClusterAST op i o) -- ~ Cluster op args, but with i and o in scope
             -> (ClusterIO args i o -> ClusterIO newio newi o)
             -> LeftHandSideArgs added newi i
             -> ConsistsOfArgs extra toAdd added
             -> ConsistsOfArgs newio added args
             -> op extra
             -> (forall args'. Cluster op args' -> LabelledArgs env args' -> r)
             -> r
consCluster' largs _ltodo@ArgsNil ldone (io, ast) iof lhsAdded _cextra@Done cio extra k = 
  k (Cluster (iof io) (Bind lhsAdded extra ast)) (fuselargs cio ldone largs)

consCluster' largs ltodo@(_:>:_) ldone (io, ast) iof lhsAdded cextra@(Todo y) cio extra k =
  step cextra ltodo ldone $ \cextra' ltodo' ldone' -> 
    consCluster' largs ltodo' ldone' _ _ _ cextra' _ extra _



data ConsistsOfArgs tot todo done where
  Done :: ConsistsOfArgs       tot  ()          tot
  Todo :: ConsistsOfArgs       tot        todo  done
       -> ConsistsOfArgs (a -> tot) (a -> todo) done

mkConsists :: Args env args -> ConsistsOfArgs args args ()
mkConsists ArgsNil    = Done
mkConsists (_ :>: xs) = Todo $ mkConsists xs

fuselargs :: ConsistsOfArgs tot left right 
          -> LabelledArgs env left 
          -> LabelledArgs env right 
          -> LabelledArgs env tot
fuselargs = undefined 

-- remove the innermost Todo
step :: ConsistsOfArgs tot (a -> todo) done
     -> LabelledArgs env (a -> todo)
     -> LabelledArgs env done
     -> (forall todo' done'. ConsistsOfArgs tot todo' done' 
                          -> LabelledArgs env todo'
                          -> LabelledArgs env done'
                          -> r) 
     -> r
step (Todo Done) k = k Done
step (Todo x@(Todo _)) k = step x $ k . _

{- [NOTE unsafeCoerce result type]

  Because we lose some type information by rebuilding the AST from scratch, we use
  unsafeCoerce to tell GHC what the result type of the computation is.
  TypeApplications allows us to specify the exact types unsafeCoerce works on,
  which in turn helps retain as much typesafety as possible. Whereever this note
  is found, unsafeCoerce's type is restricted to only work on the result type.
  In particular, we take care to not allow unsafeCoerce to mess with environment types,
  as they are tricky to get right and we really like GHC agreeing with us there.

-}
