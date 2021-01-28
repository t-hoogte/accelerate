{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE PatternSynonyms #-}

module Data.Array.Accelerate.Trafo.Clustering.ILP where

import Data.Array.Accelerate.AST.Operation
import Data.Array.Accelerate.AST.Idx
import Data.Array.Accelerate.AST.Partitioned ( Cluster )
import Data.Array.Accelerate.AST.LeftHandSide

import qualified Data.IntMap as M
import Data.List (foldl')
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
import Numeric.Limp.Program hiding ( Constraint )
import Numeric.Limp.Rep.Rep ( Assignment )
import Numeric.Limp.Rep.IntDouble ( IntDouble )
import Data.Array.Accelerate.Representation.Type


-- before we do the ILP pass, we label each 'Exec' node
data LabelledOp op args = LabelledOp Label (op args)
-- with the Operation-base acc, that might not be enough..
-- kind of need to label each array, so each Use/Unit too?
-- Don't need to label Allocs, we only care about the dependencies.
-- so.. probably need to back the recursive knot into the Operation
-- ast too, so we can label everything?

labelAcc :: PreOpenAcc op env a -> PreOpenAcc (LabelledOp op) env a
labelAcc = undefined


-- the graph datatype, including fusible/infusible edges, ..,
-- identifies nodes with unique Ints
type Label = Int

-- | Directed edge (a,b): `b` depends on `a`.
type Edge = (Label, Label)

-- TODO: at some point, set fusibleEdges := fusibleEdges \\ infusibleEdges. Makes ILP smaller.
data Graph = Graph
  { graphNodes     :: S.Set Label
  , fusibleEdges   :: S.Set Edge  -- Can   be fused over, otherwise `a` before `b`.
  , infusibleEdges :: S.Set Edge  -- Can't be fused over, always    `a` before `b`.
  }
instance Semigroup Graph where
  Graph n f i <> Graph n' f' i' = Graph (n <> n') (f <> f') (i <> i')
instance Monoid Graph where
  mempty = Graph mempty mempty mempty

-- The graph is the 'common part' of the ILP,
-- each backend has to encode their own constraints
-- describing the fusion rules.
data Information op = Information Graph (Constraint op) [ Bounds (Variable op) () IntDouble ]
instance Semigroup (Information op) where
  Information g c b <> Information g' c' b' = Information (g <> g') (c <> c') (b <> b')
instance Monoid (Information op) where
  mempty = Information mempty mempty mempty

-- | Keeps track of which argument belongs to which labels
data LabelArgs args where
  LabelArgsNil :: LabelArgs ()
  (:>>:)       :: S.Set Label -> LabelArgs t -> LabelArgs (s -> t)

-- | Keeps track of which array in the environment belongs to which label
data LabelEnv env where
  LabelEnvNil  :: LabelEnv ()
  (:>>>:)      :: S.Set Label -> LabelEnv t -> LabelEnv (t, s)

addLhsLabels :: LeftHandSide s v env env' -> S.Set Label -> LabelEnv env -> LabelEnv env'
addLhsLabels LeftHandSideWildcard{} _ lenv = lenv
addLhsLabels LeftHandSideSingle{}   l lenv = l :>>>: lenv 
addLhsLabels (LeftHandSidePair x y) l lenv = addLhsLabels y l (addLhsLabels x l lenv)

mkLabelArgs :: Args env args -> LabelEnv env -> LabelArgs args
mkLabelArgs ArgsNil _ = LabelArgsNil
mkLabelArgs (arg :>: args) e = getLabelsArg arg e :>>: mkLabelArgs args e
  where
    getLabelsArg :: Arg env t -> LabelEnv env -> S.Set Label
    getLabelsArg (ArgVar tup)                  env = getLabelsTup tup env
    getLabelsArg (ArgExp x)                    env = undefined -- call function that I still have to write
    getLabelsArg (ArgFun fun)                  env = undefined -- call function that I still have to write
    getLabelsArg (ArgArray _ _ shVars bufVars) env = getLabelsTup shVars env `S.union` getLabelsTup bufVars env

getLabelsTup :: TupR (Var a env) b -> LabelEnv env -> S.Set Label
getLabelsTup TupRunit                     _   = S.empty
getLabelsTup (TupRsingle var) env = getLabelsVar var env
getLabelsTup (TupRpair x y)               env = getLabelsTup x env `S.union` getLabelsTup y env

getLabelsVar :: Var s env t -> LabelEnv env -> S.Set Label
getLabelsVar (varIdx -> idx) lenv = getLabelsIdx idx lenv

getLabelsIdx :: Idx env a -> LabelEnv env -> S.Set Label
getLabelsIdx ZeroIdx (i :>>>: _) = i
getLabelsIdx (SuccIdx idx) (_ :>>>: env) = getLabelsIdx idx env

class MakesILP op where
  -- Variables needed to express backend-specific fusion rules.
  type BackendVar op

  -- Control flow cannot be fused, so we make separate ILPs for e.g.
  -- then-branch and else-branch. In the future, a possible optimisation is to
  -- generate code for the awhile-condition twice: once maybe fused after the body,
  -- once maybe fused after input. For now, condition and body are both treated
  -- as 'foreign calls', like if-then-else.
  -- The IntMap maps from a label to the corresponding ILP (only for things treated
  -- as 'foreign calls', like control flow).
  -- A program can result in multiple ILPs, for example, the body of an 'awhile' cannot be fused with anything outside of it.
  -- you `can` encode this in the ILP, but since the solutions are independant of each other it should be much more efficient
  -- to solve them separately. This avoids many 'infusible edges', and significantly reduces the search space. The extracted
  -- subtree gets encoded as a sort of 'foreign call', preventing all fusion.
  -- todo: maybe we can extract more commonality from this, making the class more complicated but instances smaller/easier
  mkGraph :: op args -> LabelArgs args -> Label -> Information op

  -- for efficient reconstruction
  mkMap :: PreOpenAcc (LabelledOp op) () a -> M.IntMap (UnsafeConstruction op)


-- TODO doublecheck much of this, it's tricky:
-- in the Operation-based AST, everything is powered by side effects.
-- this makes a full-program analysis like this much more difficult,
-- luckily the Args give us all the information we really require.
-- For each node, we get the set of incoming edges and the set
-- of outgoing edges. Let-bindings are easy, but the array-level
-- control flow (acond and awhile) compensate: their bodies form separate
-- graphs.
mkFullGraph :: MakesILP op 
            => PreOpenAcc (LabelledOp op) aenv a 
            -> LabelEnv aenv 
            -> ( S.Set Label -- ingoing edges
               , S.Set Label -- outgoing edges
               , Information op, M.IntMap (Information op) )
mkFullGraph (Exec (LabelledOp l op) args) lenv = undefined

mkFullGraph _ _ = undefined
-- mkFullGraph (Return groundvars) _ = undefined -- what is this? does this do anything?
-- mkFullGraph (Compute expr)      _ = undefined -- how is this even typecorrect? What does it mean?
-- mkFullGraph (Exec (LabelledOp l op) args) lenv = ( S.singleton l, mkGraph op (mkLabelArgs args lenv) l, M.empty )
-- mkFullGraph (Alet lhs u bnd scp) lenv = 
--   let (label1, info1, infomap1) = mkFullGraph bnd lenv
--       (label2, info2, infomap2) = mkFullGraph scp (addLhsLabels lhs label1 lenv) 
--   in ( label2
--      , info1 <> info2
--        -- If we encounter any duplicate keys here, that's a bad sign
--      , M.unionWith (error "oops") infomap1 infomap2 ) 
-- mkFullGraph (Alloc shr sct expv) lenv = ( getLabelsTup expv lenv, mempty, mempty )
-- mkFullGraph (Use sct buf) lenv = ( mempty, mempty, mempty )
-- mkFullGraph (Unit evar) lenv = ( getLabelsVar evar lenv, mempty, mempty )

-- -- now these are problematic: should we duplicate the informations and put them in the map with all the labels?
-- mkFullGraph (Acond c t e) lenv = undefined -- ifthenelse
-- mkFullGraph (Awhile us c b s) lenv = undefined -- while

data Variable op
  = Pi    Label                     -- For acyclic ordering of clusters
  | Fused Label Label               -- 0 is fused (same cluster), 1 is unfused. We do *not* have one of these for all pairs!
  | BackendSpecific (BackendVar op) -- Variables needed to express backend-specific fusion rules.


-- We have integer variables, and no reals.
type ILP        op = Program      (Variable op) () IntDouble
type Constraint op = P.Constraint (Variable op) () IntDouble


-- Describes how, given a list of indices into 'env', we can reconstruct an 'Execute op env'.
-- as the name suggests, this cannot be done 'safely': we're in the business of constructing
-- a strongly typed AST from untyped ILP output.
-- note that 'a list of indices' is akin to a weakening (that possibly reorders the env too)
-- todo: not all Idxs need to have the same 'a', so `list` should be `hlist` or tuplist :)
-- todo: figure out how this works with 'args'
data UnsafeConstruction (op :: Type -> Type) = forall a. UnsafeConstruction (S.Set Int) (forall args. [Idx a args] -> op args)


makeILP :: Information op -> ILP op
makeILP (Information
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
    infusible = foldMap (\(i, j) -> (z1 (Pi j) .-. z1 (Pi i)) :>= c1)
                        nofuseEdges

    --            0 <= pi_i <= n
    bounds = map (\i -> lowerUpperZ 0 (Pi i) (fromIntegral n))
                 (S.toList nodes)
             <>  -- x_ij \in {0, 1}
             map (\(i, j) -> binary (Fused i j))
                 (S.toList fuseEdges)




-- call the solver. Gets called for each ILP
solveILP :: ILP op -> Assignment (Variable op) () IntDouble
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
