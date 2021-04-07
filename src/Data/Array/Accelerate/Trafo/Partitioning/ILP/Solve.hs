{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ScopedTypeVariables #-}
module Data.Array.Accelerate.Trafo.Partitioning.ILP.Solve where

import Data.Array.Accelerate.Trafo.Partitioning.ILP.Graph
import Data.Array.Accelerate.Trafo.Partitioning.ILP.Labels

import Prelude hiding ( pi )

-- In this file, order very often subly does matter.
-- To keep this clear, we use S.Set whenever it does not,
-- and [] only when it does. It's also often efficient
-- by removing duplicates.
import qualified Data.Set as S
import qualified Data.Map as M
import Data.List (group, sortOn, foldl')
import Data.Bifunctor (Bifunctor(bimap))
import Data.Array.Accelerate.Trafo.Partitioning.ILP.Solver



makeILP :: forall ilp op. ILPSolver ilp op => Information ilp op -> ILP ilp op
makeILP (Info
          (Graph nodes fuseEdges' nofuseEdges)
          backendconstraints
          backendbounds
        ) = combine graphILP
  where
    -- Remove any redundant 'fusible' edges
    fuseEdges = fuseEdges' S.\\ nofuseEdges

    combine :: ILP ilp op -> ILP ilp op
    combine (ILP dir fun cons bnds) =
             ILP dir fun (cons <> backendconstraints)
                         (bnds <> backendbounds)

    -- n is used in some of the constraints, as an upperbound on the number of clusters.
    n :: Int
    n = S.size nodes

    graphILP = ILP Minimise objFun myConstraints myBounds

    -- Placeholder, currently maximising the number of vertical/diagonal fusions.
    -- In the future, maybe we want this to be backend-dependent.
    objFun :: Expression ilp op
    objFun = foldl' (\f (i, j) -> f .+. fused i j)
                    (int 0)
                    (S.toList fuseEdges)

    myConstraints = acyclic <> infusible

    -- x_ij <= pi_j - pi_i <= n*x_ij for all fusible edges
    acyclic = foldMap
                (\(i, j) -> between
                              ( fused i j       )
                              ( pi j .-. pi i   )
                              ( n .*. Fused i j ))
                fuseEdges

    -- pi_j - pi_i >= 1 for all infusible edges (i,j)
    infusible = foldMap (\(i, j) -> pi j .-. pi i .>=. int 1)
                        nofuseEdges

    myBounds :: Bounds ilp op
    --            0 <= pi_i <= n
    myBounds = foldMap (\i -> lowerUpper 0 (Pi i) n)
                  (S.toList nodes)
               <>  -- x_ij \in {0, 1}
               foldMap (\(i, j) -> binary $ Fused i j)
                  (S.toList fuseEdges)


-- Extract the fusion information (ordered list of clusters of Labels) (head is the first cluster)
interpretSolution :: forall ilp op. ILPSolver ilp op => [Solution ilp op] -> [Labels]
interpretSolution assignments = map (S.fromList . map fst) $ group $ sortOn snd $ map (bimap (\(Pi l)->l) (fromIntegral @_ @Int)) pis
  where
    pis :: [(Var op, Int)]
    pis = concatMap (M.toList . M.filterWithKey (const . isPi)) assignments
    isPi (Pi _) = True
    isPi _      = False
