{-# LANGUAGE MonoLocalBinds #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE LambdaCase #-}
module Data.Array.Accelerate.Trafo.Partitioning.ILP where

import Data.Array.Accelerate.Trafo.Partitioning.ILP.Graph
    ( MakesILP, Information(Info), makeFullGraph, Construction, makeFullGraphF, Graph, backendConstruc, fusibleEdges, Edge (..), constr, fused, infusibleEdges ) 
import Data.Array.Accelerate.Trafo.Partitioning.ILP.Solve
    ( interpretSolution, makeILP, splitExecs, ClusterLs, Objective (..) ) 
import Data.Array.Accelerate.Trafo.Partitioning.ILP.Clustering
    ( reconstruct, reconstructF )
import Data.Array.Accelerate.AST.Partitioned
    ( PartitionedAcc, PartitionedAfun, Cluster)
import Data.Array.Accelerate.AST.Operation
    ( OperationAcc, OperationAfun )
import Data.Array.Accelerate.Trafo.Partitioning.ILP.Solver
    ( ILPSolver(solve), (.==.), int )
import Data.Array.Accelerate.Trafo.Partitioning.ILP.MIP
    ( cbc, cplex, glpsol, gurobiCl, lpSolve, scip )

import System.IO.Unsafe (unsafePerformIO)
import Data.Array.Accelerate.Trafo.Partitioning.ILP.Labels (Label)
import Data.Map (Map)
import qualified Data.Array.Accelerate.Pretty.Operation as Pretty
import Data.Function ((&))
import qualified Data.Set as Set
import Lens.Micro ((^.), (%~), (<>~), (.~))
import Data.Maybe (isJust)


cbcFusion, gurobiFusion, cplexFusion, glpsolFusion, lpSolveFusion, scipFusion 
  :: (MakesILP op, Pretty.PrettyOp (Cluster op)) => Objective -> OperationAcc op () a -> PartitionedAcc op () a
cbcFusion     = ilpFusion cbc
gurobiFusion  = ilpFusion gurobiCl
cplexFusion   = ilpFusion cplex
glpsolFusion  = ilpFusion glpsol
lpSolveFusion = ilpFusion lpSolve
scipFusion    = ilpFusion scip

cbcFusionF, gurobiFusionF, cplexFusionF, glpsolFusionF, lpSolveFusionF, scipFusionF 
  :: (MakesILP op, Pretty.PrettyOp (Cluster op)) => Objective -> OperationAfun op () a -> PartitionedAfun op () a
cbcFusionF     = ilpFusionF cbc
gurobiFusionF  = ilpFusionF gurobiCl
cplexFusionF   = ilpFusionF cplex
glpsolFusionF  = ilpFusionF glpsol
lpSolveFusionF = ilpFusionF lpSolve
scipFusionF    = ilpFusionF scip

ilpFusion  :: (MakesILP op, ILPSolver s op, Pretty.PrettyOp (Cluster op)) => s -> Objective -> OperationAcc  op () a -> PartitionedAcc op () a
ilpFusion  = ilpFusion' makeFullGraph  reconstruct

ilpFusionF :: (MakesILP op, ILPSolver s op, Pretty.PrettyOp (Cluster op)) => s -> Objective -> OperationAfun op () a -> PartitionedAfun op () a
ilpFusionF = ilpFusion' makeFullGraphF reconstructF

ilpFusion' :: (MakesILP op, ILPSolver s op) 
           => (x -> (Information op, Map Label (Construction op))) 
           -> (Graph -> [ClusterLs] -> Map Label [ClusterLs] -> Map Label (Construction op) -> y) 
           -> s 
           -> Objective
           -> x 
           -> y
ilpFusion' k1 k2 s obj acc = fusedAcc
  where
    (info@(Info graph _ _), constrM') = k1 acc
    constrM = backendConstruc solution constrM'
    ilp                               = makeILP obj info
    solution                          = solve' ilp
    interpreted                       = interpretSolution solution
    (labelClusters, labelClustersM)   = splitExecs interpreted constrM
    fusedAcc                          = k2 graph labelClusters labelClustersM constrM
    solve' x = unsafePerformIO (solve s x) & \case
      Nothing -> error "Accelerate: No ILP solution found"
      Just y -> y

-- for benchmarking: make all edges infusible
-- note: does allow for horizontal fusion!
-- more rigorous is to change 'topSort' in Clustering.hs into separating each cluster completely
noFusion' :: (MakesILP op, ILPSolver s op) 
           => (x -> (Information op, Map Label (Construction op))) 
           -> (Graph -> [ClusterLs] -> Map Label [ClusterLs] -> Map Label (Construction op) -> y) 
           -> s 
           -> Objective
           -> x 
           -> y
noFusion' k1 k2 s obj acc = fusedAcc
  where
    (info@(Info graph' _ _), constrM') = k1 acc
    graph = graph'&infusibleEdges<>~graph'^.fusibleEdges
    constrM = backendConstruc solution constrM'
    ilp                               = makeILP obj info
    solution                          = solve' ilp
    interpreted                       = interpretSolution solution
    (labelClusters, labelClustersM)   = splitExecs interpreted constrM
    fusedAcc                          = k2 graph labelClusters labelClustersM constrM
    solve' x = unsafePerformIO (solve s x) & \case
      Nothing -> error "Accelerate: No ILP solution found"
      Just y -> y

-- for benchmarking: greedily fuse edges
-- this search is clearly inefficient, but just an easy implementation. We only benchmark its runtime.
-- note that this is perhaps still too generous. For example, anything that can fuse into 1 loop will still be fully fused!
-- it's perhaps more of an 'alternative' than a 'baseline'
greedyFusion' :: forall s op x y. (MakesILP op, ILPSolver s op)
                    => (x -> (Information op, Map Label (Construction op))) 
                    -> (Graph -> [ClusterLs] -> Map Label [ClusterLs] -> Map Label (Construction op) -> y) 
                    -> s
                    -> Objective
                    -> x 
                    -> y
greedyFusion' k1 k2 s obj acc = fusedAcc
  where
    (info'@(Info graph _ _), constrM') = k1 acc
    nedges = graph^.fusibleEdges & Set.size
    go :: Int -> Information op -> Information op
    go n info -- loop over all fusible edges. Try to set the current one to fused, if there's still a legal solution, keep it fused and continue.
      | n >= nedges = info
      | otherwise = let
        i:->j = graph^.fusibleEdges&Set.elemAt n
        info'' = info&constr<>~(fused i j .==. int 0)
        in go (n+1) $ if check info'' then info'' else info
    check :: Information op -> Bool
    check info = let
      ilp = makeILP @op obj info
      in isJust $ unsafePerformIO (solve s ilp)
    info = go 0 info'
    ilp                               = makeILP FusedEdges info

    constrM = backendConstruc solution constrM'
    solution                          = solve' ilp
    interpreted                       = interpretSolution solution
    (labelClusters, labelClustersM)   = splitExecs interpreted constrM
    fusedAcc                          = k2 graph labelClusters labelClustersM constrM
    solve' x = unsafePerformIO (solve s x) & \case
      Nothing -> error "Accelerate: No ILP solution found"
      Just y -> y

greedy,no :: (MakesILP op, Pretty.PrettyOp (Cluster op)) => Objective -> OperationAcc op () a -> PartitionedAcc op () a
greedy = greedyFusion gurobiCl
no = noFusion gurobiCl
greedyF, noF :: (MakesILP op, Pretty.PrettyOp (Cluster op)) => Objective -> OperationAfun op () a -> PartitionedAfun op () a
greedyF = greedyFusionF gurobiCl
noF = noFusionF gurobiCl
greedyFusion  :: (MakesILP op, ILPSolver s op, Pretty.PrettyOp (Cluster op)) => s -> Objective -> OperationAcc  op () a -> PartitionedAcc op () a
greedyFusion  = greedyFusion' makeFullGraph  reconstruct
greedyFusionF :: (MakesILP op, ILPSolver s op, Pretty.PrettyOp (Cluster op)) => s -> Objective -> OperationAfun op () a -> PartitionedAfun op () a
greedyFusionF = greedyFusion' makeFullGraphF reconstructF
noFusion      :: (MakesILP op, ILPSolver s op, Pretty.PrettyOp (Cluster op)) => s -> Objective -> OperationAcc  op () a -> PartitionedAcc op () a
noFusion      =     noFusion' makeFullGraph  reconstruct
noFusionF     :: (MakesILP op, ILPSolver s op, Pretty.PrettyOp (Cluster op)) => s -> Objective -> OperationAfun op () a -> PartitionedAfun op () a
noFusionF     =     noFusion' makeFullGraphF reconstructF
