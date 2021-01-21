module Data.Array.Accelerate.Trafo.Clustering.Stream
  where

import Data.Array.Accelerate.AST.Partitioned
import Data.Array.Accelerate.AST.Operation (OperationAcc)



-- Emulate the old 'delayed arrays' approach to fusion
streamfusion :: OperationAcc op benv a -> PartitionedAcc op benv a
streamfusion = undefined


