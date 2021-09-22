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
import Data.Array.Accelerate.Trafo.Partitioning.ILP.Labels (LabelEnv)


cbcFusion, gurobiFusion, cplexFusion, glpsolFusion, lpSolveFusion, scipFusion 
  :: (MakesILP op) => LabelEnv env -> OperationAcc op env a -> PartitionedAcc op env a
cbcFusion     = ilpFusion cbc
gurobiFusion  = ilpFusion gurobiCl
cplexFusion   = ilpFusion cplex
glpsolFusion  = ilpFusion glpsol
lpSolveFusion = ilpFusion lpSolve
scipFusion    = ilpFusion scip


ilpFusion :: (MakesILP op, ILPSolver s op) => s -> LabelEnv env -> OperationAcc op env a -> PartitionedAcc op env a
ilpFusion s initenv acc = fusedAcc
  where
    (info@(Info graph _ _), constrM) = makeFullGraph initenv acc
    ilp                              = makeILP info
    solution                         = solve' ilp
    interpreted                      = interpretSolution solution
    (labelClusters, labelClustersM)  = splitExecs interpreted constrM
    fusedAcc                         = reconstruct initenv graph labelClusters labelClustersM constrM
    solve' = fromJust . unsafePerformIO . solve s

