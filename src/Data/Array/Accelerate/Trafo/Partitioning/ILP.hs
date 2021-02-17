{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ScopedTypeVariables #-}
module Data.Array.Accelerate.Trafo.Partitioning.ILP where

import Data.Array.Accelerate.Trafo.Partitioning.ILP.Graph
    ( MakesILP, Information(Info), makeFullGraph ) 
import Data.Array.Accelerate.Trafo.Partitioning.ILP.Solve
    ( interpretSolution, makeILP, solveILP ) 
import Data.Array.Accelerate.Trafo.Partitioning.ILP.Clustering 
    ( reconstruct )
import Data.Array.Accelerate.AST.Partitioned
    ( OperationAcc, PartitionedAcc )

import qualified Data.IntMap as M

ilpfusion :: forall op a. MakesILP op => OperationAcc op () a -> PartitionedAcc op () a
ilpfusion acc = fusedAcc
  where
    (info@(Info graph _ _), infos, constrM) = makeFullGraph acc
    (ilp, ilps)                             = (makeILP info, M.map makeILP infos)
    (solution, solutions)                   = (solveILP ilp, M.map solveILP ilps)
    labelClusters                           = interpretSolution $ solution : M.elems solutions
    fusedAcc                                = reconstruct graph labelClusters constrM

