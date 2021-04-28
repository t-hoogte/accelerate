{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
module Data.Array.Accelerate.Trafo.Partitioning.ILP where

import Data.Array.Accelerate.Trafo.Partitioning.ILP.Graph
    ( MakesILP, Information(Info), makeFullGraph ) 
import Data.Array.Accelerate.Trafo.Partitioning.ILP.Solve
    ( interpretSolution, makeILP ) 
import Data.Array.Accelerate.Trafo.Partitioning.ILP.Clustering 
    ( reconstruct )
import Data.Array.Accelerate.AST.Partitioned
    ( OperationAcc, PartitionedAcc )
import Data.Array.Accelerate.Trafo.Partitioning.ILP.Solver
    ( ILPSolver(solve) )

import System.IO.Unsafe (unsafePerformIO)
import Data.Maybe (fromJust)

ilpfusion :: forall s op a. (MakesILP op, ILPSolver s op) => OperationAcc op () a -> s -> PartitionedAcc op () a
ilpfusion acc s = fusedAcc
  where
    (info@(Info graph _ _), constrM) = makeFullGraph acc
    ilp                              = makeILP @s info
    solution                         = solve' ilp
    labelClusters                    = interpretSolution @s solution
    fusedAcc                         = reconstruct graph labelClusters constrM
    solve' = fromJust . unsafePerformIO . solve s

