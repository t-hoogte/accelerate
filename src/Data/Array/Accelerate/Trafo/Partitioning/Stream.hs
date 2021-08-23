module Data.Array.Accelerate.Trafo.Partitioning.Stream where

import Data.Array.Accelerate.AST.Partitioned
import Data.Array.Accelerate.AST.Operation



-- Emulate the old 'delayed arrays' approach to fusion TODO
streamfusion :: OperationAcc op () a -> PartitionedAcc op () a
streamfusion = undefined
