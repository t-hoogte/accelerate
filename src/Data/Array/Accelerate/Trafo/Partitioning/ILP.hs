{-# LANGUAGE MonoLocalBinds #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE FlexibleContexts #-}
module Data.Array.Accelerate.Trafo.Partitioning.ILP where

import Data.Array.Accelerate.Trafo.Partitioning.ILP.Graph
    ( MakesILP, Information(Info), makeFullGraph, Construction, makeFullGraphF, Graph ) 
import Data.Array.Accelerate.Trafo.Partitioning.ILP.Solve
    ( interpretSolution, makeILP, splitExecs, ClusterLs ) 
import Data.Array.Accelerate.Trafo.Partitioning.ILP.Clustering
    ( reconstruct, reconstructF )
import Data.Array.Accelerate.AST.Partitioned
    ( PartitionedAcc, PartitionedAfun, Cluster )
import Data.Array.Accelerate.AST.Operation
    ( OperationAcc, OperationAfun )
import Data.Array.Accelerate.Trafo.Partitioning.ILP.Solver
    ( ILPSolver(solve) )
import Data.Array.Accelerate.Trafo.Partitioning.ILP.MIP
    ( cbc, cplex, glpsol, gurobiCl, lpSolve, scip )

import System.IO.Unsafe (unsafePerformIO)
import Data.Maybe (fromJust)
import Data.Array.Accelerate.Trafo.Partitioning.ILP.Labels (Label)
import Data.Map (Map)
import qualified Data.Array.Accelerate.Pretty.Operation as Pretty


cbcFusion, gurobiFusion, cplexFusion, glpsolFusion, lpSolveFusion, scipFusion 
  :: (MakesILP op, Pretty.PrettyOp (Cluster op)) => OperationAcc op () a -> PartitionedAcc op () a
cbcFusion     = ilpFusion cbc
gurobiFusion  = ilpFusion gurobiCl
cplexFusion   = ilpFusion cplex
glpsolFusion  = ilpFusion glpsol
lpSolveFusion = ilpFusion lpSolve
scipFusion    = ilpFusion scip

cbcFusionF, gurobiFusionF, cplexFusionF, glpsolFusionF, lpSolveFusionF, scipFusionF 
  :: (MakesILP op, Pretty.PrettyOp (Cluster op)) => OperationAfun op () a -> PartitionedAfun op () a
cbcFusionF     = ilpFusionF cbc
gurobiFusionF  = ilpFusionF gurobiCl
cplexFusionF   = ilpFusionF cplex
glpsolFusionF  = ilpFusionF glpsol
lpSolveFusionF = ilpFusionF lpSolve
scipFusionF    = ilpFusionF scip

ilpFusion  :: (MakesILP op, ILPSolver s op, Pretty.PrettyOp (Cluster op)) => s -> OperationAcc  op () a -> PartitionedAcc op () a
ilpFusion  = ilpFusion' makeFullGraph  reconstruct

ilpFusionF :: (MakesILP op, ILPSolver s op, Pretty.PrettyOp (Cluster op)) => s -> OperationAfun op () a -> PartitionedAfun op () a
ilpFusionF = ilpFusion' makeFullGraphF reconstructF

ilpFusion' :: (MakesILP op, ILPSolver s op) 
           => (x -> (Information op, Map Label (Construction op))) 
           -> (Graph -> [ClusterLs] -> Map Label [ClusterLs] -> Map Label (Construction op) -> y) 
           -> s 
           -> x 
           -> y
ilpFusion' k1 k2 s acc = fusedAcc
  where
    (info@(Info graph _ _), constrM) = k1 acc
    ilp                              = makeILP info
    solution                         = solve' ilp
    interpreted                      = interpretSolution solution
    (labelClusters, labelClustersM)  = splitExecs interpreted constrM
    fusedAcc                         = k2 graph labelClusters labelClustersM constrM
    solve' = fromJust . unsafePerformIO . solve s

