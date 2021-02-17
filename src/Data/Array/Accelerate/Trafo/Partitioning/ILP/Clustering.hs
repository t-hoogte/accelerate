module Data.Array.Accelerate.Trafo.Partitioning.ILP.Clustering where

import Data.Array.Accelerate.Trafo.Partitioning.ILP.Graph
import qualified Data.Set as S
import Data.Array.Accelerate.Trafo.Partitioning.ILP.Labels
import qualified Data.IntMap as M
import Data.Array.Accelerate.AST.Partitioned



-- "open research question"
-- -- Each set of ints corresponds to a set of Constructions, which themselves contain a set of ints (the things they depend on).
-- -- Some of those ints will refer to nodes in previous clusters, others to nodes in this cluster.
-- One pass over these datatypes (back-to-front) should identify the 'output type' of each cluster: which nodes are needed in later clusters?
-- Then, we can construct the clusters front-to-back:
--    identify the nodes that only depend on nodes outside of the cluster, they are the initials
--    the `output type` indicates which nodes we will need to keep: they are all either a final node in the cluster, or get diagonally fused
-- How exactly we can use this information (and a dep. graph) to construct a cluster of ver,hor,diag is not clear.. Will also depend on the exact cluster definition.

reconstruct :: Graph -> [S.Set Label] -> M.IntMap (Construction op) -> PreOpenAcc (Cluster op) () a
reconstruct = undefined


    -- Because we lose some type information by rebuilding the AST from scratch, we use
    -- unsafeCoerce here to tell GHC that the new AST has the same return type.
    -- Type applications allow us to restrict this function to the return type only.
    -- fusedAcc = case reconstructedAcc of
    --   Exists res -> unsafeCoerce @(PartitionedAcc op () _) 
    --                              @(PartitionedAcc op () a) 
    --                              res