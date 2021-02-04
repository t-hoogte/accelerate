{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE EmptyCase #-}
{-# LANGUAGE TupleSections #-}
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
-- and [] only when it does. It's also often efficient
-- by removing duplicates.
import qualified Data.Set as S

-- Limp is a Linear Integer Mixed Programming library.
-- We only use the Integer part (not the Mixed part, 
-- which allows you to add non-integer variables and
-- constraints). It has a backend that binds to CBC, 
-- which is apparently a good one? Does not seem to be
-- actively maintained though.
-- We can always switch to a different ILP library
-- later, the interfaces are all quite similar.
import qualified Numeric.Limp.Program as P
import Numeric.Limp.Program hiding ( Constraint, r )
import Numeric.Limp.Rep.Rep ( Assignment )
import Numeric.Limp.Rep.IntDouble ( IntDouble )
import Data.Array.Accelerate.Representation.Type
import Unsafe.Coerce (unsafeCoerce)


-- -- before we do the ILP pass, we label each 'Exec' node
-- data LabelledOp op args = LabelledOp Label (op args)
-- -- with the Operation-base acc, that might not be enough..
-- -- kind of need to label each array, so each Use/Unit too?
-- -- Don't need to label Allocs, we only care about the dependencies.
-- -- so.. probably need to back the recursive knot into the Operation
-- -- ast too, so we can label everything?

-- labelAcc :: PreOpenAcc op env a -> PreOpenAcc (LabelledOp op) env a
-- labelAcc = undefined


-- identifies nodes with unique Ints. and tracks their dependencies
type Label =  Int

-- identifies elements of the environment with unique Ints.
-- newtype'd to avoid confusing them with Label (above).
newtype ELabel = ELabel Int
  deriving (Show, Eq, Ord, Num)

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
-- describing the fusion rules. The bounds is a [] instead of S.Set
-- for practical reasons (no Ord instance, LIMP expects a list) only.
data Information op = Info Graph (Constraint op) [ Bounds (Variable op) () IntDouble ]
instance Semigroup (Information op) where
  Info g c b <> Info g' c' b' = Info (g <> g') (c <> c') (b <> b')
instance Monoid (Information op) where
  mempty = Info mempty mempty mempty

-- | Keeps track of which argument belongs to which labels
data LabelArgs args where
  LabelArgsNil :: LabelArgs ()
  (:>>:)       :: S.Set Label -> LabelArgs t -> LabelArgs (s -> t)

-- | Keeps track of which array in the environment belongs to which label
data LabelEnv env where
  LabelEnvNil  :: LabelEnv ()
  (:>>>:)      :: (ELabel, S.Set Label) -> LabelEnv t -> LabelEnv (t, s)

addLhsLabels :: LeftHandSide s v env env' -> ELabel -> S.Set Label -> LabelEnv env -> (ELabel, LabelEnv env')
addLhsLabels LeftHandSideWildcard{} e _ lenv = (e, lenv)
addLhsLabels LeftHandSideSingle{}   e l lenv = (e + 1, (e, l) :>>>: lenv)
addLhsLabels (LeftHandSidePair x y) e l lenv = let (e' , lenv' ) = addLhsLabels x e  l lenv
                                               in addLhsLabels y e' l lenv'

weakLhsEnv :: LeftHandSide s v env env' -> LabelEnv env' -> LabelEnv env
weakLhsEnv LeftHandSideSingle{} (_:>>>: env) = env
weakLhsEnv LeftHandSideWildcard{} env = env
weakLhsEnv (LeftHandSidePair l r) env = weakLhsEnv l (weakLhsEnv r env)

emptyLabelEnv :: LabelEnv env -> LabelEnv env
emptyLabelEnv LabelEnvNil = LabelEnvNil
emptyLabelEnv ((e,_):>>>:env) = (e, mempty) :>>>: emptyLabelEnv env

getAllLabelsEnv :: LabelEnv env -> S.Set Label
getAllLabelsEnv LabelEnvNil = mempty
getAllLabelsEnv ((_,set) :>>>: lenv) = set <> getAllLabelsEnv lenv

getLabelArgs :: Args env args -> LabelEnv env -> LabelArgs args
getLabelArgs ArgsNil _ = LabelArgsNil
getLabelArgs (arg :>: args) e = getLabelsArg arg e :>>: getLabelArgs args e

getLabelsArg :: Arg env t -> LabelEnv env -> S.Set Label
getLabelsArg (ArgVar tup)                  env = getLabelsTup tup    env
getLabelsArg (ArgExp expr)                 env = getLabelsExp expr   env
getLabelsArg (ArgFun fun)                  env = getLabelsFun fun    env
getLabelsArg (ArgArray _ _ shVars bufVars) env = getLabelsTup shVars env <> getLabelsTup bufVars env

getLabelsTup :: TupR (Var a env) b -> LabelEnv env -> S.Set Label
getLabelsTup TupRunit                     _   = mempty
getLabelsTup (TupRsingle var) env = getLabelsVar var env
getLabelsTup (TupRpair x y)               env = getLabelsTup x env <> getLabelsTup y env

getLabelsVar :: Var s env t -> LabelEnv env -> S.Set Label
getLabelsVar (varIdx -> idx) lenv = getLabelsIdx idx lenv

getLabelsIdx :: Idx env a -> LabelEnv env -> S.Set Label
getLabelsIdx ZeroIdx ((_,ls) :>>>: _) = ls
getLabelsIdx (SuccIdx idx) (_ :>>>: env) = getLabelsIdx idx env

getELabelIdx :: Idx env a -> LabelEnv env -> ELabel
getELabelIdx ZeroIdx ((e,_) :>>>: _) = e
getELabelIdx (SuccIdx idx) (_ :>>>: env) = getELabelIdx idx env

getLabelsExp :: OpenExp x env y -> LabelEnv env -> S.Set Label
getLabelsExp = undefined -- TODO traverse everything, look for Idxs

getLabelsFun :: OpenFun x env y -> LabelEnv env -> S.Set Label
getLabelsFun (Body expr) lenv = getLabelsExp expr lenv
getLabelsFun (Lam _ fun) lenv = getLabelsFun fun  lenv

updateLabelEnv :: Args env args -> LabelEnv env -> Label -> LabelEnv env
updateLabelEnv ArgsNil lenv _ = lenv
updateLabelEnv (arg :>: args) lenv l = case arg of
  -- CHECK we only look at the 'Buffer' vars here, not the 'shape' ones. Is that ok?
  ArgArray Out _ _ vars -> updateLabelEnv args (insertAtVars vars lenv l) l
  ArgArray Mut _ _ vars -> updateLabelEnv args (insertAtVars vars lenv l) l
  _ -> updateLabelEnv args lenv l

insertAtVars :: TupR (Var a env) b -> LabelEnv env -> Label -> LabelEnv env
insertAtVars TupRunit lenv _ = lenv
insertAtVars (TupRpair x y) lenv l = insertAtVars x (insertAtVars y lenv l) l
insertAtVars (TupRsingle (varIdx -> idx)) ((e,lset) :>>>: lenv) l = case idx of
  ZeroIdx -> (e, S.insert l lset) :>>>: lenv
  SuccIdx idx' ->       (e, lset) :>>>: insertAtVars (TupRsingle (Var undefined idx')) lenv l
insertAtVars (TupRsingle (varIdx -> idx)) LabelEnvNil _ = case idx of {}

-- | Like `getLabelArgs`, but ignores the `Out` arguments
getInputArgLabels :: Args env args -> LabelEnv env -> S.Set Label
getInputArgLabels ArgsNil _ = mempty
getInputArgLabels (arg :>: args) lenv = getInputArgLabels args lenv <> case arg of
  ArgArray Out _ _ _ -> mempty
  _ -> getLabelsArg arg lenv

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
  -- mkMap :: PreOpenAcc (LabelledOp op) () a -> M.IntMap (UnsafeConstruction op)


-- TODO doublecheck much of this, it's tricky:
-- in the Operation-based AST, everything is powered by side effects.
-- this makes a full-program analysis like this much more difficult,
-- luckily the Args give us all the information we really require.
-- For each node, we get the set of incoming edges and the set
-- of outgoing edges. Let-bindings are easy, but the array-level
-- control flow (acond and awhile) compensate: their bodies form separate
-- graphs.
-- We can practically ignore 'Return' nodes.
-- let bindings are more tricky, because of the side effects. Often,
-- a let will not add to the environment but instead mutate it.
-- I'm still not convinced 'Compute' nodes can even be used
-- things with labels include:
-- - Control flow (a label for each branch, treated as a separate ILP) (acond & awhile)
-- - Exec
-- - Use
-- - Alloc? Difficult case: if you include it, are the edges fusible? Do we
--    need to include a binary in the ILP describing whether the alloc is fused away?
--    probably yes, and then the edges are infusible if they exist
--    but maybe no need to label it, if we can infer them afterwards?
-- - Unit

-- this function will also need to produce the 'reconstruction' lookup map,
-- to ensure that the labels we generate are consistent between the lookup map
-- and the graph. I'll do that Later (TM)
mkFullGraph :: MakesILP op 
            => PreOpenAcc op aenv a 
            -> LabelEnv aenv -- for each array in the environment, 
            -- the source labels of the currently open outgoing edges.
            -> Label -- the next fresh label to use
            -> ELabel -- the next fresh ELabel to use
            -> ( 
              --    S.Set Label -- incoming edges
              --  , S.Set Label -- outgoing edges
                ( Information op, M.IntMap (Information op))
              , LabelEnv aenv -- like input, but adjusted for side-effects
              , S.Set Label -- source labels of currently open outgoing edges of 'a'
              , Label -- the next fresh label to use
              , ELabel -- the next fresh ELabel to use
               -- , reconstruction thing
              )

-- Exec case: think about the exact type of mkGraph, and adjust accordingly.
-- clear responsibility on who makes the graph!

-- For all input arguments (that is, everything except `Out` buffers), we add fusible edges. If that's
-- not strict enough, the backend can add infusible edges, but this is a sound (or complete? not both!)
-- lowerbound on fusibility: these inputs have to exist to evaluate the op.
mkFullGraph (Exec op args) lenv l e = let fuseedges = S.map (, l) $ getInputArgLabels args lenv in
  ( (mkGraph op (getLabelArgs args lenv) l <> Info (Graph (S.singleton l) fuseedges mempty) mempty mempty, mempty)
  , updateLabelEnv args lenv l -- add labels for `Out` and `Mut` args.
  , mempty
  , l + 1
  , e)
mkFullGraph (Alet lhs u bnd scp) lenv l e = -- replace ticks with numbers? think of actual names for variables???
  let (bndInfo, lenv'  , lbnd, l' , e'  ) = mkFullGraph bnd lenv   l  e
      (e'', lenv'') = addLhsLabels lhs e' lbnd lenv'
      (scpInfo, lenv''', lscp, l'', e''') = mkFullGraph scp lenv'' l' e''
  in  (bndInfo <> scpInfo
      , weakLhsEnv lhs lenv'''
      , lscp
      , l''
      , e''')
mkFullGraph (Return  vars) lenv l e = ( (mempty, mempty), lenv, getLabelsTup vars lenv, l, e)
mkFullGraph (Compute expr) lenv l e = ( (mempty, mempty), lenv, getLabelsExp expr lenv, l, e)
mkFullGraph (Alloc shr scty vars) lenv l e = ( (mempty, mempty), lenv, mempty, l, e) -- unless we can't infer alloc...
mkFullGraph Use{} lenv l e = 
  ( (Info (Graph (S.singleton l) mempty mempty) mempty mempty, mempty)
  , undefined, S.singleton l, l+1, e)
-- gets a variable from the env, puts it in a singleton buffer.
-- Here I'm assuming this fuses nicely, and doesn't even need a new label 
-- (reuse the one that belongs to the variable). If not, change!
mkFullGraph (Unit var) lenv l e = ( (mempty, mempty), undefined, getLabelsVar var lenv, l, e)
-- NOTE: We explicitly add infusible edges from every label in `lenv` to this Acond.
-- This makes the previous let-bindings strict: even if some result is only used in one
-- branch, we now require it to be present before we evaluate the condition.
-- I think this is safe: if a result is only used in one branch, it should be let-bound
-- within that branch. Note that this also means we ignore the contents of 'cond' for the graph.
-- We also add edges from the Acond to the true-branch, and from the true-branch to the false-branch?
-- TODO check if this is right/needed/if passing even more fresh labels down is correct.
mkFullGraph (Acond cond tbranch fbranch) lenv l e = let tlabel = l+1
                                                        flabel = l+2
                                                        emptyEnv = emptyLabelEnv lenv
                                                        ( (tinfo, tinfoM), _, _, l' , e' ) = mkFullGraph tbranch emptyEnv (l+3) e
                                                        ( (finfo, finfoM), _, _, l'', e'') = mkFullGraph fbranch emptyEnv l'    e'
                                                        nonfuse = S.map (,l) (getAllLabelsEnv lenv) <> S.fromList [(l, tlabel), (tlabel, flabel)]
                                                    in ( (Info (Graph (S.fromList [l, l+1, l+2]) mempty nonfuse) mempty mempty
                                                         , M.fromList [(tlabel, tinfo), (flabel, finfo)] <> tinfoM <> finfoM)
                                                       , emptyEnv, S.singleton l, l''+1, e'')
mkFullGraph _ _ _ _ = undefined


-- mkFullGraph (Return groundvars) _ = undefined -- what is this? does this do anything?
-- mkFullGraph (Compute expr)      _ = undefined -- how is this even typecorrect? What does it mean?
-- mkFullGraph (Exec (LabelledOp l op) args) lenv = ( S.singleton l, mkGraph op (getLabelArgs args lenv) l, M.empty )
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

-- | Contains three things:
-- - Operation - works on arguments (backend-specific, we don't touch it during this whole pass)
-- - Args      - describes how to get the arguments from the old environment
-- - LabelEnv  - stores ELabels, which allow us to re-index the Args into the new environment
data UnsafeConstruction (op :: Type -> Type) = forall env args. UnsafeConstruction (LabelEnv env) (Args env args) (op args)


-- | Uses unsafeCoerce to convince the typechecker that we have found what we were looking for.
-- If we don't screw up with the ELabels, this is safe...
mkReindexPartial :: LabelEnv env -> LabelEnv env' -> ReindexPartial Maybe env env'
mkReindexPartial lenv lenv' = findIdx . flip getELabelIdx lenv
  where findIdx = go lenv'
        go :: LabelEnv e -> ELabel -> Maybe (Idx e a)
        go ((e,_) :>>>: env) e'
          -- here we have to convince GHC that the top element in the environment 
          -- really does have the same type as the one we were searching for.
          | e == e' = Just $ unsafeCoerce ZeroIdx
          | otherwise = SuccIdx <$> go env e'
        go LabelEnvNil _ = Nothing

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
