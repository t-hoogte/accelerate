{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures, RankNTypes #-}
module Data.Array.Accelerate.Trafo.Clustering.ILP where
import qualified Data.IntMap as M
import Data.Array.Accelerate.AST.Operation (PreOpenAcc, Execute)
import Data.Kind
import Data.Array.Accelerate.AST.Idx
import qualified Data.Set as S
import Data.Array.Accelerate.AST.Partitioned
import Data.Array.Accelerate.AST.LeftHandSide

-- the graph datatype, including fusible/infusible edges, .., 
-- identifies nodes with unique Ints
data Graph


class MakesILP op where
  -- todo: maybe can extract more commonality from this, making the class more complicated but instances smaller/easier
  mkGraph :: PreOpenAcc (Execute op) () a-> Graph

  -- for efficient reconstruction - important that the numbers match the numbers in mkGraph
  mkMap :: PreOpenAcc (Execute op) () a -> M.IntMap (UnsafeConstruction op)


-- Describes how, given a list of indices into 'env', we can reconstruct an 'Execute op env'.
-- as the name suggests, this cannot be done 'safely': we're in the business of constructing 
-- a strongly typed AST from untyped ILP output.
-- note that 'a list of indices' is akin to a weakening (that possibly reorders the env too)
-- todo: not all Idxs need to have the same 'a', so `list` should be `hlist` or tuplist :)
data UnsafeConstruction (op :: Type -> Type) = forall a. UnsafeConstruction (S.Set Int) (forall env. [Idx a env] -> Execute op env)

-- todo: choose suitable library/bindings to solver
data ILP

-- A program can result in multiple ILPs, for example, the body of an 'awhile' cannot be fused with anything outside of it.
-- you `can` encode this in the ILP, but since the solutions are independant of each other it should be much more efficient
-- to solve them separately. This avoids many 'infusible edges', and significantly reduces the search space. The extracted
-- subtree gets encoded as a sort of 'foreign call', preventing all fusion.
makeILPs :: Graph -> [ILP]
makeILPs = undefined

-- call the solver, and interpret the result as a list (in order of execution) of clusters (sets of nodes).
-- gets called for each ILP
solveILP :: ILP -> [S.Set Int]
solveILP = undefined

-- Order all lists of clusters in a logical way
combineSets :: [[S.Set Int]] -> [S.Set Int]
combineSets = undefined 

-- "open research question"
-- Each set of ints corresponds to a set of unsafeConstructions, which themselves contain a set of ints (the things they depend on).
-- Some of those ints will refer to nodes in previous clusters, others to nodes in this cluster.
-- One pass over these datatypes (back-to-front) should identify the 'output type' of each cluster: which nodes are needed in later clusters?
-- Then, we can construct the clusters front-to-back.
reconstruct :: [S.Set Int] -> M.IntMap (UnsafeConstruction op) -> Exists (PreOpenAcc (Cluster op) ())
reconstruct = undefined
