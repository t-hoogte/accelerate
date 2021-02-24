{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ScopedTypeVariables #-}
module Data.Array.Accelerate.Trafo.Partitioning.ILP.Solve where

import Data.Array.Accelerate.Trafo.Partitioning.ILP.Graph
import Data.Array.Accelerate.Trafo.Partitioning.ILP.Labels

import Prelude hiding ( pi )

-- Data structures
-- In this file, order very often subly does matter.
-- To keep this clear, we use S.Set whenever it does not,
-- and [] only when it does. It's also often efficient
-- by removing duplicates.
import qualified Data.Set as S
import qualified Data.Map as M
import Data.List (group, sortOn, foldl')


-- Limp is a Linear Integer Mixed Programming library.
-- We only use the Integer part (not the Mixed part, 
-- which allows you to add non-integer variables and
-- constraints). It has a backend that binds to CBC, 
-- which is apparently a good one? Does not seem to be
-- actively maintained though.
-- We can always switch to a different ILP library
-- later, the interfaces are all quite similar.
import Numeric.Limp.Program hiding ( Constraint, r )
import Numeric.Limp.Rep.IntDouble
import qualified Numeric.Limp.Rep.Rep as LIMP
import Data.Bifunctor (Bifunctor(bimap))



makeILP :: Information op -> ILP op
makeILP (Info
          (Graph nodes fuseEdges' nofuseEdges)
          backendconstraints
          backendbounds
        ) = combine graphILP
  where
    -- Remove any redundant 'fusible' edges
    fuseEdges = fuseEdges' S.\\ nofuseEdges

    combine (Program dir fun cons bnds) =
             Program dir fun (cons <> backendconstraints)
                             (bnds <> backendbounds)

    -- n is used in some of the constraints, as an upperbound on the number of clusters.
    -- We wrap it in the Z newtype here for convenience at use-sites.
    n :: Z IntDouble
    n = Z $ S.size nodes
    --                                  _____________________________________
    --                                 | Don't know why the objFun has to be |
    --                             ___ | real, everything else is integral.  |
    --                            |    | Hope this doesn't slow the solver.  |
    --                            v     ‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾
    graphILP = Program Minimise (toR objFun) myConstraints myBounds 

    -- Placeholder, currently maximising the number of vertical/diagonal fusions.
    -- In the future, maybe we want this to be backend-dependent.
    objFun = foldl' (\f (i, j) -> f .+. fused i j) 
                    c0 
                    (S.toList fuseEdges)

    myConstraints = acyclic <> infusible

    -- x_ij <= pi_j - pi_i <= n*x_ij for all fusible edges
    acyclic = foldMap
                (\(i, j) -> Between
                              ( fused i j       )
                              ( pi j .-. pi i   )
                              ( z (Fused i j) n ))
                fuseEdges

    -- pi_j - pi_i >= 1 for all infusible edges (i,j)
    infusible = foldMap (\(i, j) -> pi j .-. pi i :>= c1)
                        nofuseEdges

    --            0 <= pi_i <= n
    myBounds = map (\i -> lowerUpperZ 0 (Pi i) n)
                   (S.toList nodes)
               <>  -- x_ij \in {0, 1}
               map (\(i, j) -> binary $ Fused i j)
                  (S.toList fuseEdges)

-- call the solver. Gets called for each ILP
solveILP :: ILP op -> Assignment op
solveILP = undefined

-- Extract the fusion information (ordered list of clusters of Labels) (head is the first cluster)
interpretSolution :: forall op. [Assignment op] -> [Labels]
interpretSolution assignments = map (S.fromList . map fst) $ group $ sortOn snd $ map (bimap (\(Pi l)->l) (fromIntegral @_ @Int)) pis
  where
    pis :: [(Variable op, Z IntDouble)]
    pis = concatMap (\(LIMP.Assignment x _) -> M.toList $ M.filterWithKey (const . isPi) x) assignments
    isPi (Pi _) = True
    isPi _      = False
