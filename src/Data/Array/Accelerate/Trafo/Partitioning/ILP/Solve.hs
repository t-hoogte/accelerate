{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
module Data.Array.Accelerate.Trafo.Partitioning.ILP.Solve where


import Data.Array.Accelerate.Trafo.Partitioning.ILP.Graph
import Data.Array.Accelerate.Trafo.Partitioning.ILP.Labels
    (Label, parent, Labels )
import Data.Array.Accelerate.Trafo.Partitioning.ILP.Solver

import Data.List (groupBy, sortOn, foldl')
import Prelude hiding ( pi )

import qualified Data.Map as M

-- In this file, order very often subly does matter.
-- To keep this clear, we use S.Set whenever it does not,
-- and [] only when it does. It's also often efficient
-- by removing duplicates.
import qualified Data.Set as S
import Data.Function ( on )
import Lens.Micro ( _1 )
import Lens.Micro.Extras ( view )
import Data.Maybe (fromJust,  mapMaybe )



-- Makes the ILP. Note that this function 'appears' to ignore the Label levels completely!
-- We could add some assertions, but if all the input is well-formed (no labels, constraints, etc
-- that reward putting non-siblings in the same cluster) this is fine.
makeILP :: forall op. MakesILP op => Information op -> ILP op
makeILP (Info
          (Graph nodes fuseEdges' nofuseEdges)
          backendconstraints
          backendbounds
        ) = combine graphILP
  where
    -- Remove any redundant 'fusible' edges
    fuseEdges = fuseEdges' S.\\ nofuseEdges

    combine :: ILP op -> ILP op
    combine (ILP dir fun cons bnds) =
             ILP dir fun (cons <> backendconstraints)
                         (bnds <> backendbounds)

    -- n is used in some of the constraints, as an upperbound on the number of clusters.
    n :: Int
    n = S.size nodes

    graphILP = ILP Minimise objFun myConstraints myBounds

    -- Placeholder, currently maximising the number of vertical/diagonal fusions.
    -- In the future, maybe we want this to be backend-dependent (add to MakesILP).
    -- Also future: add IPU reward here.
    objFun :: Expression op
    objFun = foldl' (\f (i :-> j) -> f .+. fused i j)
                    (int 0)
                    (S.toList fuseEdges)

    myConstraints = acyclic <> infusible

    -- x_ij <= pi_j - pi_i <= n*x_ij for all fusible edges
    acyclic = foldMap
                (\(i :-> j) -> between
                              ( fused i j       )
                              ( pi j .-. pi i   )
                              ( n .*. Fused i j ))
                fuseEdges

    -- pi_j - pi_i >= 1 for all infusible edges (i,j)
    infusible = foldMap (\(i :-> j) -> pi j .-. pi i .>=. int 1)
                        nofuseEdges

    myBounds :: Bounds op
    --            0 <= pi_i <= n
    myBounds = foldMap (\i -> lowerUpper 0 (Pi i) n)
                  (S.toList nodes)
               <>  -- x_ij \in {0, 1}
               foldMap (\(i :-> j) -> binary $ Fused i j)
                  (S.toList fuseEdges)


-- Extract the fusion information (ordered list of clusters of Labels) (head is the first cluster).
-- Output has the top-level clusters in fst, and the rest in snd.
interpretSolution :: Solution op -> ([Labels], M.Map Label [Labels])
interpretSolution = (\(x:xs) -> (x, M.fromList $ map (\l -> ( fromJust 
                                                            . view parent 
                                                            . S.findMin 
                                                            . head 
                                                            $ l
                                                            , l)) xs))
                  . map ( map S.fromList
                        . partition (view parent)
                        . map fst )
                  . partition snd 
                  . mapMaybe (_1 fromPi)
                  . M.toList
  where
    fromPi (Pi l) = Just l
    fromPi _      = Nothing

    partition f = groupBy ((==) `on` f) . sortOn f
