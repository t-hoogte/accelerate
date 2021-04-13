{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
module Data.Array.Accelerate.Trafo.Partitioning.ILP where

import Data.Array.Accelerate.Trafo.Partitioning.ILP.Limp
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

import qualified Data.Map as M
import System.IO.Unsafe (unsafePerformIO)
import Data.Maybe (fromJust)

limpFusion :: MakesILP op => OperationAcc op () a -> PartitionedAcc op () a
limpFusion = ilpfusion @LIMP

ilpfusion :: forall ilp op a. (MakesILP op, ILPSolver ilp op) => OperationAcc op () a -> PartitionedAcc op () a
ilpfusion acc = fusedAcc
  where
    (info@(Info graph _ _), infos, constrM) = makeFullGraph acc
    (ilp, ilps)                             = (makeILP info, M.map makeILP infos)
    (solution, solutions)                   = (solve' ilp, M.map solve' ilps)
    labelClusters                           = interpretSolution @ilp $ solution : M.elems solutions
    fusedAcc                                = _ reconstruct graph labelClusters constrM
    solve' = fromJust . unsafePerformIO . solve @ilp

