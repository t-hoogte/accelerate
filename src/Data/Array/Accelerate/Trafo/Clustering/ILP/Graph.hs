{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Data.Array.Accelerate.Trafo.Clustering.ILP.Graph where

import Data.Array.Accelerate.Trafo.Clustering.ILP.Labels

-- accelerate imports
import Data.Array.Accelerate.AST.Idx ( Idx(..) )
import Data.Array.Accelerate.AST.Operation

-- Data structures
-- In this file, order very often subly does matter.
-- To keep this clear, we use S.Set whenever it does not,
-- and [] only when it does. It's also often efficient
-- by removing duplicates.
import qualified Data.Set as S
import qualified Data.IntMap as M


-- GHC imports
import Data.Kind ( Type )
import Unsafe.Coerce (unsafeCoerce)


-- Limp is a Linear Integer Mixed Programming library.
-- We only use the Integer part (not the Mixed part, 
-- which allows you to add non-integer variables and
-- constraints). It has a backend that binds to CBC, 
-- which is apparently a good one? Does not seem to be
-- actively maintained though.
-- We can always switch to a different ILP library
-- later, the interfaces are all quite similar.
import qualified Numeric.Limp.Program as LIMP
import qualified Numeric.Limp.Rep     as LIMP
import Numeric.Limp.Program hiding ( Bounds, Constraint, Program, Linear, r )
import Numeric.Limp.Rep ( IntDouble )
import Data.Array.Accelerate.Array.Buffer
import Data.Array.Accelerate.Type


-- | We have Int variables represented by @Variable op@, and no real variables.
-- These type synonyms instantiate the @z@, @r@ and @c@ type variables in Limp.
type LIMP  datatyp op   = datatyp (Variable op) () IntDouble
type LIMP' datatyp op a = datatyp (Variable op) () IntDouble a

type Assignment op = LIMP  LIMP.Assignment op
type Bounds     op = LIMP  LIMP.Bounds     op
type Constraint op = LIMP  LIMP.Constraint op
type ILP        op = LIMP  LIMP.Program    op
type Linear op res = LIMP' LIMP.Linear op res

-- | Directed edge (a,b): `b` depends on `a`.
type Edge = (Label, Label)


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
data Information op = Info Graph (Constraint op) [Bounds op]
instance Semigroup (Information op) where
  Info g c b <> Info g' c' b' = Info (g <> g') (c <> c') (b <> b')
instance Monoid (Information op) where
  mempty = Info mempty mempty mempty



data Variable op
  = Pi    Label                     -- For acyclic ordering of clusters
  | Fused Label Label               -- 0 is fused (same cluster), 1 is unfused. We do *not* have one of these for all pairs!
  | BackendSpecific (BackendVar op) -- Variables needed to express backend-specific fusion rules.

-- convenience synonyms
pi :: Label -> Linear op 'KZ
pi l = z1 $ Pi l
fused :: Label -> Label -> Linear op 'KZ
fused x y = z1 $ Fused x y


class MakesILP op where
  -- Variables needed to express backend-specific fusion rules.
  type BackendVar op

  -- | This function only needs to do the backend-specific things, that is, things which depend on the definition of @op@.
  -- That includes "BackendVar op's" and all their constraints/bounds, but also some (in)fusible edges.
  -- As a conveniece, fusible edges have already been made from all (incoming) labels in the LabelArgs to the current label. 
  -- These can be 'strengthened' by adding a corresponding infusible edge, in which case the fusible edge will later be optimised away.
  mkGraph :: op args -> LabelArgs args -> Label -> Information op

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
-- subtree gets encoded as a sort of 'foreign call', preventing all fusion. TODO test with 'nested foreign functions':
-- Does the algorithm work if a while contains other Awhile or Acond nodes in its condition or body?

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


makeFullGraph :: MakesILP op
              => PreOpenAcc op () a
              -> (Information op, M.IntMap (Information op), M.IntMap (Construction op))
makeFullGraph acc = (info, infoM, constrM)
  where ((info, infoM), _, _, _, _, constrM) = mkFullGraph acc LabelEnvNil 1 (ELabel 1)

-- TODO: This function would be cleaner with a datatype and State monad
-- replacing the tuples and explicit passing of every argument
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
              -- for reconstructing the AST later. We generate this and the graph in one pass, 
              , M.IntMap (Construction op) -- to guarantee that the labels match.
              )

-- For all input arguments (that is, everything except `Out` buffers), we add fusible edges. If that's
-- not strict enough, the backend can add infusible edges, but this is a sound
-- lowerbound on fusibility: these inputs may never be computed _after_ the op.
-- Excessive fusible edges are filtered out before we feed them to the ILP solver.
mkFullGraph (Exec op args) lenv l e =
  let fuseedges = S.map (, l) $ getInputArgLabels args lenv
  in ( (mkGraph op (getLabelArgs args lenv) l <> Info (Graph (S.singleton l) fuseedges mempty) mempty mempty, mempty)
     , updateLabelEnv args lenv l -- add labels for `Out` and `Mut` args.
     , mempty
     , l + 1
     , e
     , M.singleton l $ CExe lenv args op)
mkFullGraph (Alet lhs u bnd scp) lenv l e = -- we throw away the uniquenessess information here, that's Future Work
  let (bndInfo, lenv'  , lbnd, l' , e'  , c ) = mkFullGraph bnd lenv   l  e
      (e'', lenv'') = addLhsLabels lhs e' lbnd lenv'
      (scpInfo, lenv''', lscp, l'', e''', c') = mkFullGraph scp lenv'' l' e''
  in  (bndInfo <> scpInfo
      , weakLhsEnv lhs lenv'''
      , lscp
      , l''
      , e'''
      , c <> c')
mkFullGraph (Return vars)          lenv l e = ( (mempty, mempty), lenv, getLabelsTup vars lenv, l, e, mempty)
mkFullGraph (Compute expr)         lenv l e = ( (mempty, mempty), lenv, getLabelsExp expr lenv, l, e, mempty)
mkFullGraph (Alloc shr scty shvar) lenv l e = ( (mempty, mempty), lenv, mempty                , l, e, mempty) -- unless we can't infer alloc...
mkFullGraph (Use sctype buff) lenv l e =
  ( (Info (Graph (S.singleton l) mempty mempty) mempty mempty, mempty)
  , lenv, S.singleton l, l+1, e
  , M.singleton l $ CUse sctype buff)
-- gets a variable from the env, puts it in a singleton buffer.
-- Here I'm assuming this fuses nicely, and doesn't even need a new label 
-- (reuse the one that belongs to the variable). Might need to add a label
-- to avoid obfuscating the AST though. Change when needed.
mkFullGraph (Unit var) lenv l e = ( (mempty, mempty), lenv, getLabelsVar var lenv, l, e, mempty)

-- NOTE: We explicitly add infusible edges from every label in `lenv` to this Acond.
-- This makes the previous let-bindings strict: even if some result is only used in one
-- branch, we now require it to be present before we evaluate the condition.
-- I think this is safe: if a result is only used in one branch, it should be let-bound
-- within that branch already. Note that this also means we ignore the contents of 'cond' for the graph.
-- We also add edges from the Acond to the true-branch, and from the true-branch to the false-branch?
-- TODO check if this is right/needed/if passing even more fresh labels down is correct.
mkFullGraph (Acond cond tbranch fbranch) lenv l e = let tlabel = l+1
                                                        flabel = l+2
                                                        emptyEnv = emptyLabelEnv lenv
                                                        ( (tinfo, tinfoM), _, _, l' , e' , c ) = mkFullGraph tbranch emptyEnv (l+3) e
                                                        ( (finfo, finfoM), _, _, l'', e'', c') = mkFullGraph fbranch emptyEnv l'    e'
                                                        nonfuse = S.map (,l) (getAllLabelsEnv lenv) <> S.fromList [(l, tlabel), (tlabel, flabel)]
                                                    in ( (Info (Graph (S.fromList [l .. l+2]) mempty nonfuse) mempty mempty
                                                         , M.fromList [(tlabel, tinfo), (flabel, finfo)] <> tinfoM <> finfoM)
                                                       , emptyEnv, S.singleton l, l'', e''
                                                       , M.insert l (CITE lenv cond tlabel flabel) c <> c')
-- like Acond. The biggest difference is that 'cond' is a function instead of an expression here.
-- In fact, for the graph, we use 'startvars' much like we used 'cond' in Acond, and we use
-- 'cond' and 'bdy' much like we used 'tbranch' and 'fbranch'.
mkFullGraph (Awhile u cond bdy startvars) lenv l e = let clabel = l+1
                                                         blabel = 1+2
                                                         emptyEnv = emptyLabelEnv lenv
                                                         ( (cinfo, cinfoM), _, _, l' , e' , c ) = mkFullGraphF cond emptyEnv (l+3) e
                                                         ( (binfo, binfoM), _, _, l'', e'', c') = mkFullGraphF bdy  emptyEnv l'    e'
                                                         nonfuse = S.map (,l) (getAllLabelsEnv lenv) <> S.fromList [(l, clabel), (clabel, blabel)]
                                                     in ( (Info (Graph (S.fromList [l .. l+2]) mempty nonfuse) mempty mempty
                                                          , M.fromList [(clabel, cinfo), (blabel, binfo)] <> cinfoM <> binfoM)
                                                        , emptyEnv, S.singleton l, l'', e''
                                                        , M.insert l (CWhl lenv u clabel blabel startvars) c <> c')

-- | Like mkFullGraph, but for @PreOpenAfun@.
mkFullGraphF :: MakesILP op
             => PreOpenAfun op aenv a
             -- For each array in the environment, the source labels 
             -> LabelEnv aenv -- of the currently open outgoing edges.
             -> Label -- the next fresh label to use
             -> ELabel -- the next fresh ELabel to use
             -> (
                  ( Information op, M.IntMap (Information op))
                , LabelEnv aenv -- like input, but adjusted for side-effects
                , S.Set Label -- source labels of currently open outgoing edges of 'a'
                , Label -- the next fresh label to use
                , ELabel -- the next fresh ELabel to use
                , M.IntMap (Construction op)
                )
mkFullGraphF = \case
  Abody acc  -> mkFullGraph acc
  Alam lhs f -> \lenv l e -> let (e', lenv') = addLhsLabels lhs e mempty lenv -- it's a function, so we can fill the extra environment with mempties
                                 ((info, infoM),                lenv'', lset, l', e'', c) = mkFullGraphF f lenv' l e'
                             in  ((info, infoM), weakLhsEnv lhs lenv'', lset, l', e'', c)

-- | Information to construct AST nodes. Generally, constructors contain
-- both actual information, and a LabelEnv of the original environment
-- which helps to re-index into the new environment later.
data Construction (op :: Type -> Type) where
  CExe :: LabelEnv env -> Args env args -> op args                                  -> Construction op
  CUse ::                 ScalarType e -> Buffer e                                  -> Construction op
  CITE :: LabelEnv env -> ExpVar env PrimBool -> Label -> Label                     -> Construction op
  CWhl :: LabelEnv env -> Uniquenesses a      -> Label -> Label -> GroundVars env a -> Construction op

constructExe :: LabelEnv env' -> LabelEnv env 
             -> Args env args -> op args 
             -> Maybe (PreOpenAcc op env' ())
constructExe lenv' lenv args op = Exec op <$> reindexArgs (mkReindexPartial lenv lenv') args
constructUse :: ScalarType e -> Buffer e 
             -> PreOpenAcc op env (Buffer e)
constructUse = Use
constructITE :: LabelEnv env' -> LabelEnv env 
             -> ExpVar env PrimBool -> PreOpenAcc op env' a -> PreOpenAcc op env' a 
             -> Maybe (PreOpenAcc op env' a)
constructITE lenv' lenv cond tbranch fbranch = Acond <$> reindexVar (mkReindexPartial lenv lenv') cond 
                                                     <*> pure tbranch 
                                                     <*> pure fbranch
constructWhl :: LabelEnv env' -> LabelEnv env 
             -> Uniquenesses a -> PreOpenAfun op env' (a -> PrimBool) -> PreOpenAfun op env' (a -> a) -> GroundVars env a 
             -> Maybe (PreOpenAcc op env' a)
constructWhl lenv' lenv u cond body start = Awhile u cond body <$> reindexVars (mkReindexPartial lenv lenv') start



-- | Makes a ReindexPartial, which allows us to transform indices in @env@ into indices in @env'@.
-- We cannot guarantee the index is present in env', so we use the partiality of ReindexPartial by
-- returning a Maybe. Uses unsafeCoerce to re-introduce type information implied by the ELabels.
mkReindexPartial :: LabelEnv env -> LabelEnv env' -> ReindexPartial Maybe env env'
mkReindexPartial lenv lenv' idx = go lenv'  
  where
    -- The ELabel in the original environment
    e = getELabelIdx idx lenv
    go :: forall e a. LabelEnv e -> Maybe (Idx e a)
    go ((e',_) :>>>: env) -- e' is the ELabel in the new environment
      -- Here we have to convince GHC that the top element in the environment 
      -- really does have the same type as the one we were searching for.
      -- Some literature does this stuff too: 'effect handlers in haskell, evidently'
      -- and 'a monadic framework for delimited continuations' come to mind.
      -- Basically: standard procedure if you're using Ints as a unique identifier
      -- and want to re-introduce type information. :)
      -- Type applications allow us to restrict unsafeCoerce to the return type.
      | e == e' = Just $ unsafeCoerce @(Idx e _) @(Idx e a) ZeroIdx
      -- Recurse if we did not find e' yet.
      | otherwise = SuccIdx <$> go env
    -- If we hit the end, the Elabel was not present in the environment.
    -- That probably means we'll error out at a later point, but maybe there is
    -- a case where we try multiple options? No need to worry about it here.
    go LabelEnvNil = Nothing
