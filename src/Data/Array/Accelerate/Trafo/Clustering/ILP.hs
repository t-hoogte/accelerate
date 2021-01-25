{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures, RankNTypes #-}
module Data.Array.Accelerate.Trafo.Clustering.ILP where
import qualified Data.IntMap as M
import Data.Array.Accelerate.AST.Operation (Execute)
import Data.Array.Accelerate.AST.Idx ( Idx )
import Data.Array.Accelerate.AST.Partitioned ( PreOpenAcc, Cluster )
import Data.Array.Accelerate.AST.LeftHandSide ( Exists )

import Data.Kind ( Type )

-- In this file, order very often subly does matter.
-- To keep this clear, we use S.Set whenever it does not,
-- and [] only when it does.
import qualified Data.Set as S 

-- Limp is a Linear Integer Mixed Programming library.
-- We only use the Integer part. It has a backend that
-- binds to CBC, which is apparently a good one?
-- We can always switch to a different ILP library
-- later, the interfaces are all quite similar
import qualified Numeric.Limp.Program as P
import qualified Numeric.Limp.Rep.IntDouble as R




-- the graph datatype, including fusible/infusible edges, .., 
-- identifies nodes with unique Ints
type Label = Int

-- | Directed edge (a,b): `a` must be computed [strictly?] before `b`.
type Edge = (Label, Label)


data Graph = Graph
  { nodes          :: S.Set Label
  , fusibleEdges   :: S.Set Edge  -- Can   be fused over, otherwise `a` before `b`.
  , infusibleEdges :: S.Set Edge  -- Can't be fused over, always    `a` before `b`.
  }


-- The graph is the 'common part' of the ILP,
-- each backend has to encode their own constraints
-- describing the fusion rules.
data Information op = Information Graph (S.Set (Constraint op))


class MakesILP op where
  -- Variables needed to express backend-specific fusion rules.
  type BackendVar op
  
  -- todo: maybe we can extract more commonality from this, making the class more complicated but instances smaller/easier
  mkGraph :: PreOpenAcc (Execute op) () a-> Information op

  -- for efficient reconstruction - important that the numbers match the numbers in mkGraph. Can fuse the two to ensure,
  -- or do a separate 'labelling' pass first (:: Execute op -> LabelledExe op).
  mkMap :: PreOpenAcc (Execute op) () a -> M.IntMap (UnsafeConstruction op)


data Variable op
  = Pi    Label                     -- For acyclic ordering of clusters
  | Fused Label Label               -- 0 is fused (same cluster), 1 is unfused. We do *not* have one of these for all pairs!
  | BackendSpecific (BackendVar op) -- Variables needed to express backend-specific fusion rules.


-- We have integer variables, and no reals.
type ILP        op = P.Program    (Variable   op) () R.IntDouble
type Constraint op = P.Constraint (Variable   op) () R.IntDouble


-- Describes how, given a list of indices into 'env', we can reconstruct an 'Execute op env'.
-- as the name suggests, this cannot be done 'safely': we're in the business of constructing 
-- a strongly typed AST from untyped ILP output.
-- note that 'a list of indices' is akin to a weakening (that possibly reorders the env too)
-- todo: not all Idxs need to have the same 'a', so `list` should be `hlist` or tuplist :)
data UnsafeConstruction (op :: Type -> Type) = forall a. UnsafeConstruction (S.Set Int) (forall env. [Idx a env] -> Execute op env)

-- A program can result in multiple ILPs, for example, the body of an 'awhile' cannot be fused with anything outside of it.
-- you `can` encode this in the ILP, but since the solutions are independant of each other it should be much more efficient
-- to solve them separately. This avoids many 'infusible edges', and significantly reduces the search space. The extracted
-- subtree gets encoded as a sort of 'foreign call', preventing all fusion.
makeILPs :: Information op -> (ILP op, M.IntMap (ILP op))
makeILPs (Information graph backendcons) = somehowCombine graphILPs backendcons
  where
    somehowCombine = undefined -- Put all backend-specific constraints into each ILP? Or can we be smarter,
                               -- only adding ones that somehow 'matter' for the ILPs? Is the solver smart
                               -- enough, and will it disregard these other constraints? What if the backend
                               -- somehow needs the values that the backend-specific variables take in the
                               -- solution, then we need to find out which solution is the relevant one?
    graphILPs :: forall op. (ILP op, M.IntMap (ILP op))
    graphILPs = undefined -- Formula's from the papers, such that:
                          --  - clusters are acyclic (w.r.t. infusible edges and non-fused fusible edges)
                          --  - infusible edges are respected
                          --  - number of clusters is minimised
                          -- 
                          -- New stuff: control flow cannot be fused, so we make separate ILPs for e.g.
                          -- then-branch and else-branch. In the future, a possible optimisation is to 
                          -- generate code for the awhile-condition twice: once maybe fused after the body, 
                          -- once maybe fused after input. For now, condition and body are both treated
                          -- as 'foreign calls', like if-then-else.
                          -- The IntMap maps from a label to the corresponding ILP (only for things treated
                          -- as 'foreign calls', like control flow).
                      

-- call the solver, and interpret the result as a list (in order of execution) of clusters (sets of nodes).
-- gets called for each ILP
solveILP :: ILP op -> [S.Set Int]
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
