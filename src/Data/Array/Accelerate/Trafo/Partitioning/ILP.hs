{-# LANGUAGE MonoLocalBinds #-}
{-# LANGUAGE TypeApplications #-}
module Data.Array.Accelerate.Trafo.Partitioning.ILP where

import Data.Array.Accelerate.Trafo.Partitioning.ILP.Graph
    ( MakesILP, Information(Info), makeFullGraph ) 
import Data.Array.Accelerate.Trafo.Partitioning.ILP.Solve
    ( interpretSolution, makeILP, splitExecs ) 
import Data.Array.Accelerate.Trafo.Partitioning.ILP.Clustering 
    ( reconstruct )
import Data.Array.Accelerate.AST.Partitioned
    ( PartitionedAcc )
import Data.Array.Accelerate.AST.Operation 
    ( OperationAcc )
import Data.Array.Accelerate.Trafo.Partitioning.ILP.Solver
    ( ILPSolver(solve) )
import Data.Array.Accelerate.Trafo.Partitioning.ILP.MIP
    ( cbc, cplex, glpsol, gurobiCl, lpSolve, scip )

import System.IO.Unsafe (unsafePerformIO)
import Data.Maybe (fromJust)


cbcFusion, gurobiFusion, cplexFusion, glpsolFusion, lpSolveFusion, scipFusion 
  :: (MakesILP op) => OperationAcc op () a -> PartitionedAcc op () a
cbcFusion     = ilpFusion cbc
gurobiFusion  = ilpFusion gurobiCl
cplexFusion   = ilpFusion cplex
glpsolFusion  = ilpFusion glpsol
lpSolveFusion = ilpFusion lpSolve
scipFusion    = ilpFusion scip


ilpFusion :: (MakesILP op, ILPSolver s op) => s -> OperationAcc op () a -> PartitionedAcc op () a
ilpFusion s acc = fusedAcc
  where
    (info@(Info graph _ _), constrM) = makeFullGraph acc
    ilp                              = makeILP info
    solution                         = solve' ilp
    interpreted                      = interpretSolution solution
    (labelClusters, labelClustersM)  = splitExecs interpreted constrM
    fusedAcc                         = reconstruct graph labelClusters labelClustersM constrM
    solve' = fromJust . unsafePerformIO . solve s

