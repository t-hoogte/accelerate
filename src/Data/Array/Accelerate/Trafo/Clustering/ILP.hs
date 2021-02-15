{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ScopedTypeVariables #-}
module Data.Array.Accelerate.Trafo.Clustering.ILP where

import Data.Array.Accelerate.Trafo.Clustering.ILP.Graph
    ( MakesILP, Information(Info), makeFullGraph ) 
import Data.Array.Accelerate.Trafo.Clustering.ILP.Solve
    ( interpretSolution, makeILP, reconstruct, solveILP ) 
import Data.Array.Accelerate.AST.Partitioned
    ( OperationAcc, PartitionedAcc )

import qualified Data.IntMap as M
import Unsafe.Coerce (unsafeCoerce)
import Data.Array.Accelerate.AST.LeftHandSide ( Exists(Exists) )

ilpfusion :: forall op a. MakesILP op => OperationAcc op () a -> PartitionedAcc op () a
ilpfusion acc = fusedAcc
  where
    (info@(Info graph _ _), infos, constrM) = makeFullGraph acc
    (ilp, ilps) = (makeILP info, M.map makeILP infos)
    solution    = (solveILP ilp, M.map solveILP ilps)
    (labelCluster,labelClusters) = interpretSolution solution
    reconstructedAcc = reconstruct graph labelCluster labelClusters constrM
    -- Because we lose some type information by rebuilding the AST from scratch, we use
    -- unsafeCoerce here to tell GHC that the new AST has the same return type.
    -- Type applications allow us to restrict this function to the return type only.
    fusedAcc = case reconstructedAcc of
      Exists res -> unsafeCoerce @(PartitionedAcc op () _) 
                                 @(PartitionedAcc op () a) 
                                 res
