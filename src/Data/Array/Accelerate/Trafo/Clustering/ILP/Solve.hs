module Data.Array.Accelerate.Trafo.Clustering.ILP.Solve where

import Data.Array.Accelerate.Trafo.Clustering.ILP.Graph

-- accelerate imports
import Data.Array.Accelerate.AST.LeftHandSide
import Data.Array.Accelerate.AST.Operation
import Data.Array.Accelerate.AST.Partitioned ( Cluster )

-- Data structures
-- M.IntMap is used 
import qualified Data.IntMap as M
-- In this file, order very often subly does matter.
-- To keep this clear, we use S.Set whenever it does not,
-- and [] only when it does. It's also often efficient
-- by removing duplicates.
import qualified Data.Set as S
import Data.List (foldl')


-- GHC imports


-- Limp is a Linear Integer Mixed Programming library.
-- We only use the Integer part (not the Mixed part, 
-- which allows you to add non-integer variables and
-- constraints). It has a backend that binds to CBC, 
-- which is apparently a good one? Does not seem to be
-- actively maintained though.
-- We can always switch to a different ILP library
-- later, the interfaces are all quite similar.
import Numeric.Limp.Program hiding ( Constraint, r )
import Numeric.Limp.Rep.Rep ( Assignment )



makeILP :: Information op -> ILP op
makeILP (Info
          (Graph nodes fuseEdges nofuseEdges)
          backendconstraints
          backendbounds
        ) = combine graphILP
  where
    combine (Program dir fun cons bnds) =
             Program dir fun (cons <> backendconstraints)
                             (bnds <> backendbounds)

    n = S.size nodes
    --                                  _____________________________________
    --                                 | Don't know why the objFun has to be |
    --                             ___ | real, everything else is integral.  |
    --                            |    | Hope this doesn't slow the solver.  |
    --                            v     ‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾
    graphILP = Program Minimise (toR objFun) constraints bounds 

    -- Placeholder, currently maximising the number of vertical/diagonal fusions.
    -- In the future, maybe we want this to be backend-dependent.
    objFun = foldl' (\f (i, j) -> f .+. z1 (Fused i j)) c0 (S.toList fuseEdges)

    constraints = acyclic <> infusible

    -- x_ij <= pi_j - pi_i <= n*x_ij for all fusible edges
    acyclic = foldMap
                (\(i, j) -> Between
                              ( z1 (Fused i j)                  )
                              ( z1 (Pi j) .-. z1 (Pi i)         )
                              ( z  (Fused i j) (fromIntegral n) ))
                fuseEdges

    -- pi_j - pi_i >= 1 for all infusible edges (i,j)
    infusible = foldMap (\(i, j) -> z1 (Pi j) .-. z1 (Pi i) :>= c1)
                        nofuseEdges

    --            0 <= pi_i <= n
    bounds = map (\i -> lowerUpperZ 0 (Pi i) (fromIntegral n))
                 (S.toList nodes)
             <>  -- x_ij \in {0, 1}
             map (\(i, j) -> binary (Fused i j))
                 (S.toList fuseEdges)




-- call the solver. Gets called for each ILP
solveILP :: ILP op -> LIMP Assignment op
solveILP = undefined


-- "open research question"
-- Each set of ints corresponds to a set of unsafeConstructions, which themselves contain a set of ints (the things they depend on).
-- Some of those ints will refer to nodes in previous clusters, others to nodes in this cluster.
-- One pass over these datatypes (back-to-front) should identify the 'output type' of each cluster: which nodes are needed in later clusters?
-- Then, we can construct the clusters front-to-back:
--    identify the nodes that only depend on nodes outside of the cluster, they are the initials
--    the `output type` indicates which nodes we will need to keep: they are all either a final node in the cluster, or get diagonally fused
-- How exactly we can use this information (and a dep. graph) to construct a cluster of ver,hor,diag is not clear.. Will also depend on the exact cluster definition.
reconstruct :: Graph -> [S.Set Int] -> M.IntMap [S.Set Int] -> M.IntMap (UnsafeConstruction op) -> Exists (PreOpenAcc (Cluster op) ())
reconstruct = undefined
