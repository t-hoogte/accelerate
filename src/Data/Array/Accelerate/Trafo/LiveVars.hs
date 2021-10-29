{-# LANGUAGE InstanceSigs         #-}
{-# LANGUAGE GADTs                #-}
{-# LANGUAGE LambdaCase           #-}
{-# LANGUAGE MultiWayIf           #-}
{-# LANGUAGE RankNTypes           #-}
{-# LANGUAGE ScopedTypeVariables  #-}
{-# LANGUAGE TypeOperators        #-}
{-# OPTIONS_HADDOCK hide #-}
-- |
-- Module      : Data.Array.Accelerate.Trafo.LiveVars
-- Copyright   : [2012..2020] The Accelerate Team
-- License     : BSD3
--
-- Maintainer  : Trevor L. McDonell <trevor.mcdonell@gmail.com>
-- Stability   : experimental
-- Portability : non-portable (GHC extensions)
--
-- Utilties for creating a dead variable / (strongly) live
-- variable analysis on one of our IRs.
--

module Data.Array.Accelerate.Trafo.LiveVars
  ( ReEnv(..), reEnvIdx, reEnvIndices, reEnvIndices', reEnvVar, reEnvVars
  , Liveness(..), dead, LivenessEnv, emptyLivenessEnv
  , setLive, setIndicesLive, setVarsLive, setLivenessImplies, setLivenessImplications, isLive
  , strengthenLiveness, dropLivenessEnv, pushLivenessEnv
  , bind, BindLiveness(..), bindSub, BindLivenessSub(..)
  , ReturnImplication(..), ReturnImplications, noReturnImplications
  , strengthenReturnImplications, droppedReturnImplications, propagateReturnLiveness
  , joinReturnImplications, joinReturnImplication
  , SubTupR(..), subTupR, subTupUnit, DeclareSubVars(..), declareSubVars
  , LVAnalysis(..), LVAnalysisFun(..), LVAnalysis'(..), allDead, expectJust
  , subTupExp, subTupFun
  ) where

import Data.Array.Accelerate.AST.Environment
import Data.Array.Accelerate.AST.Exp
import Data.Array.Accelerate.AST.Idx
import Data.Array.Accelerate.AST.IdxSet ( IdxSet(..) )
import qualified Data.Array.Accelerate.AST.IdxSet as IdxSet
import Data.Array.Accelerate.AST.Var
import Data.Array.Accelerate.AST.LeftHandSide
import Data.Array.Accelerate.Representation.Type
import Data.Array.Accelerate.Trafo.Var
import Data.Array.Accelerate.Trafo.Exp.Substitution
import Data.Array.Accelerate.Trafo.Substitution
import Data.Array.Accelerate.Trafo.SkipEnvironment
import Data.Array.Accelerate.Error

import Data.List (foldl')
import Data.Maybe
import Data.Type.Equality

data ReEnv env subenv where
  ReEnvEnd  :: ReEnv () ()
  ReEnvSkip :: ReEnv env subenv -> ReEnv (env, t) subenv
  ReEnvKeep :: ReEnv env subenv -> ReEnv (env, t) (subenv, t)

reEnvIdx :: ReEnv env subenv -> env :?> subenv
reEnvIdx (ReEnvKeep _) ZeroIdx      = Just ZeroIdx
reEnvIdx (ReEnvKeep r) (SuccIdx ix) = SuccIdx <$> reEnvIdx r ix
reEnvIdx (ReEnvSkip r) (SuccIdx ix) = reEnvIdx r ix
reEnvIdx _             _            = Nothing

reEnvIndices :: ReEnv env subenv -> [Exists (Idx env)] -> [Exists (Idx subenv)]
reEnvIndices re = mapMaybe $ \(Exists idx) -> Exists <$> reEnvIdx re idx

reEnvIndices' :: ReEnv env subenv -> [Idx env t] -> [Idx subenv t]
reEnvIndices' re = mapMaybe $ reEnvIdx re

reEnvVar :: ReEnv env subenv -> Var s env t -> Maybe (Var s subenv t)
reEnvVar re (Var tp idx) = Var tp <$> reEnvIdx re idx

reEnvVars :: ReEnv env subenv -> Vars s env t -> Maybe (Vars s subenv t)
reEnvVars re = traverseTupR $ reEnvVar re

-- During the analysis, a variable is either known to be live, or unknown
-- whether it is live or dead. In the last case, we store a list of implied
-- indices which are also live if this variable appears to be live.
--
-- Note that type argument 't' is not used, but it is needed to give Liveness
-- the correct kind to be used in 'Env', as defined in 'LivenessEnv'.
data Liveness env t where
  Live :: Liveness env t

  -- Not sure if this is live, but if it is then the given set of indices is also live,
  -- i.e. the liveness of this variable implies the liveness of others.
  Unknown :: IdxSet env -> Liveness env t

dead :: Liveness env t
dead = Unknown IdxSet.empty

instance Sink Liveness where
  weaken _ Live        = Live
  weaken k (Unknown s) = Unknown $ IdxSet.map (weaken k) s

instance SEnvValue Liveness where
  weakenSEnvValue _    Live        = Live
  weakenSEnvValue skip (Unknown s) = Unknown $ skipWeakenIdxSet skip s

  weakenSEnvValue' _    Live        = Live
  weakenSEnvValue' skip (Unknown s) = Unknown $ skipWeakenIdxSet' skip s

  strengthenSEnvValue :: forall env1 env2 t. SEnv Liveness env1 -> Skip env1 env2 -> Liveness env1 t -> Liveness env2 t
  strengthenSEnvValue _   _    Live        = Live
  strengthenSEnvValue env skip (Unknown s) = Unknown $ go s
    where
      skip' = skipReverse skip

      go :: IdxSet env1 -> IdxSet env2
      go set
        = IdxSet.union remaining
        $ dropped IdxSet.>>= go'
        where
          dropped = skipTakeIdxSet' skip' set
          remaining = skipStrengthenIdxSet skip set

      go' :: Idx env1 t' -> IdxSet env2
      go' idx = case sprj idx env of
        Live -> IdxSet.empty
        Unknown set -> go set

newtype LivenessEnv env = LivenessEnv (SEnv Liveness env)
-- TODO: Instead of using Env, use a specialized Env which makes it cheaper to
-- weaken and strengthen the environment (with an LHS). This would require an
-- approach similar to WEnv, but with something like Skip instead of a (:>),
-- as the latter doesn't provide a way to strengthen.
-- Such environment prevents doing many maps over the entire environment.
--

emptyLivenessEnv :: LivenessEnv ()
emptyLivenessEnv = LivenessEnv SEmpty

setLive :: forall env t. Idx env t -> LivenessEnv env -> LivenessEnv env
setLive idx (LivenessEnv env) = foldl' (\e (Exists idx') -> setLive idx' e) (LivenessEnv env') implied
  where
    (env', implied) = sprjUpdate f idx env

    f :: Liveness env t -> (Liveness env t, [Exists (Idx env)])
    f Live = (Live, [])
    f (Unknown i) = (Live, IdxSet.toList i)

setIndicesLive :: [Exists (Idx env)] -> LivenessEnv env -> LivenessEnv env
setIndicesLive indices env = foldl' (\e (Exists idx) -> setLive idx e) env indices

setVarsLive :: Vars s env t -> LivenessEnv env -> LivenessEnv env
setVarsLive vars env = foldl' (\e (Exists var) -> setLive (varIdx var) e) env $ flattenTupR vars

setLivenessImplies :: Idx env t -> IdxSet env -> LivenessEnv env -> LivenessEnv env
setLivenessImplies idx implied (LivenessEnv env)
  | live = foldl' (\e (Exists idx') -> setLive idx' e) (LivenessEnv env') $ IdxSet.toList implied
  | otherwise = LivenessEnv env'
  where
    (env', live) = sprjUpdate f idx env
    f Live = (Live, True)
    f (Unknown implied') = (Unknown $ IdxSet.union implied implied', False)


setLivenessImplications :: IdxSet env -> IdxSet env -> LivenessEnv env -> LivenessEnv env
setLivenessImplications indices implied env = foldl' (\e (Exists idx) -> setLivenessImplies idx implied e) env $ IdxSet.toList indices

isLive :: LivenessEnv env -> Idx env t -> Bool
isLive (LivenessEnv env) idx
  | Live <- sprj idx env = True
  | otherwise            = False

strengthenLiveness :: forall env' env t. LivenessEnv env' -> env' :?> env -> Liveness env' t -> Liveness env t
strengthenLiveness env k (Unknown implies) = Unknown implies'
  where
    ReturnImplication implies' = strengthenReturnImplications env k $ ReturnImplication implies
strengthenLiveness _   _ Live = Live

strengthenReturnImplications :: forall env' env t. LivenessEnv env' -> env' :?> env -> ReturnImplication env' t -> ReturnImplication env t
strengthenReturnImplications (LivenessEnv env) k (ReturnImplication implies) = ReturnImplication $ implies IdxSet.>>= go
  where
    go :: Idx env' s -> IdxSet env
    go idx
      | Just idx' <- k idx = IdxSet.singleton idx'
      | Unknown implies' <- sprj idx env = implies' IdxSet.>>= go
      | otherwise = IdxSet.empty

droppedReturnImplications :: LeftHandSide s t env env' -> ReturnImplication env' v -> ReturnImplication env' v
droppedReturnImplications lhs (ReturnImplication implies) = ReturnImplication $ IdxSet.intersect implies $ lhsIndices lhs

dropLivenessEnv :: forall s t env env'. LeftHandSide s t env env' -> LivenessEnv env' -> LivenessEnv env
dropLivenessEnv lhs lenv@(LivenessEnv env) = LivenessEnv $ strengthenSEnv (lhsSkip' lhs) env

pushLivenessEnv :: forall s t env env'. LeftHandSide s t env env' -> ReturnImplications env t -> LivenessEnv env -> LivenessEnv env'
pushLivenessEnv lhs bodyImplications (LivenessEnv env) = LivenessEnv $ go lhs bodyImplications $ weakenSEnv (lhsSkip' lhs) env
  where
    go :: LeftHandSide s t' env1 env2 -> ReturnImplications env t' -> SEnv' Liveness env' env1 -> SEnv' Liveness env' env2
    go (LeftHandSideSingle _)   (TupRsingle (ReturnImplication set)) e = SPush e $ Unknown $ IdxSet.skip' lhs set
    go (LeftHandSideWildcard _) _                                    e = e
    go (LeftHandSidePair l1 l2) (TupRpair i1 i2)                     e = go l2 i2 $ go l1 i1 e
    go (LeftHandSidePair l1 l2) (TupRsingle (ReturnImplication set)) e = go l2 (TupRsingle $ ReturnImplication set) $ go l1 (TupRsingle $ ReturnImplication set) e
    go _                        _                                    _ = internalError "Tuple mismatch"

-- Similar to LeftHandSide, but LeftHandSideSingle is annotated with a boolean
-- denoting whether the variable is live.
--
data LHSLiveness s t env env' where
  LHSLivenessWildcard :: (TupR s t) -> LHSLiveness s t env env
  LHSLivenessSingle   :: Bool -> s t -> LHSLiveness s t env (env, t)
  LHSLivenessPair     :: LHSLiveness s t1 env env'
                      -> LHSLiveness s t2 env' env''
                      -> LHSLiveness s (t1, t2) env env''

-- Creates an LHSLiveness where the bindings with Live are marked as live.
-- Note that in 'bind' we still need to mark more bindings live, as they
-- can be implied by live free variables (following from ReEnv).
--
envToLHSLiveness
  :: SEnv' Liveness env'' env'
  -> LeftHandSide s t env env'
  -> (SEnv' Liveness env'' env, LHSLiveness s t env env')
envToLHSLiveness env (LeftHandSideWildcard tp) = (env, LHSLivenessWildcard tp)
envToLHSLiveness env (LeftHandSideSingle tp)   = (env', LHSLivenessSingle live tp)
  where
    (env', v) = senvTop env
    live
      | Live <- v = True
      | otherwise = False
envToLHSLiveness env (LeftHandSidePair l1 l2)  = (env'', LHSLivenessPair l1' l2')
  where
    (env',  l2') = envToLHSLiveness env  l2
    (env'', l1') = envToLHSLiveness env' l1

propagateLiveness :: SEnv' Liveness env' env -> ReEnv env subenv -> Skip' env' env -> LHSLiveness s t env env' -> LHSLiveness s t env env'
propagateLiveness env re skip lhs = snd $ lhsMarkLive (reEnvImpliedLiveness env re skip) lhs

-- Returns the set of indices between env' and env1 which are implied to be
-- live by the variables which were not known to be live in the SEnv but are
-- live according to the ReEnv.
-- Only indices between env' and env1 (as specified by Skip) are returned. This
-- is used by propagateLiveness to only gather the freshly bound indices in the
-- LeftHandSide. Initially, Skip env' env1 will then correspond with
-- `LeftHandSide s t env1 env'`; but env' will change in recursive calls of
-- this function. By only returning a set of the indices in this range, we not
-- only reduce the cost of unions, but we can now also stop the recursion
-- earlier when we have found (enough) SSkips as we are then guaranteed that we
-- don't find new implied indices in the range.
--
reEnvImpliedLiveness :: SEnv' Liveness env' env -> ReEnv env subenv -> Skip' env' env1 -> IdxSet env'
reEnvImpliedLiveness (SSkip skip' env)             re             skip = case joinSkips' skip skip' of
  Right _ -> IdxSet.empty -- No need to traverse further
  Left skip'' -> skipWeakenIdxSet' skip' $ reEnvImpliedLiveness env re skip''
reEnvImpliedLiveness (SPush env _)                 (ReEnvSkip re) skip
  -- Variable is not live
  = reEnvImpliedLiveness env re skip
reEnvImpliedLiveness (SPush env (Unknown implied)) (ReEnvKeep re) skip
  -- Variable became live, propagate liveness
  = skipTakeIdxSet' skip implied `IdxSet.union` reEnvImpliedLiveness env re skip
reEnvImpliedLiveness (SPush env Live)              (ReEnvKeep re) skip
  -- Variable was already live, no need to propagate new liveness information
  = reEnvImpliedLiveness env re skip
reEnvImpliedLiveness SEmpty                        ReEnvEnd       skip = IdxSet.empty

lhsMarkLive :: IdxSet env' -> LHSLiveness s t env env' -> (IdxSet env, LHSLiveness s t env env')
lhsMarkLive (IdxSet PEnd) lhs
  = (IdxSet PEnd, lhs)
lhsMarkLive (IdxSet set)  (LHSLivenessSingle live1 tp)
  = (IdxSet set', LHSLivenessSingle (live1 || live2) tp)
  where
    (live2, set') = case set of
      PPush s _ -> (True,  s)
      PNone s   -> (False, s)
      PEnd      -> (False, PEnd)
lhsMarkLive set           (LHSLivenessWildcard tp)
  = (set, LHSLivenessWildcard tp)
lhsMarkLive set           (LHSLivenessPair l1 l2)
  = (set'', LHSLivenessPair l1' l2')
  where
    (set',  l2') = lhsMarkLive set l2
    (set'', l1') = lhsMarkLive set' l1

bind :: LeftHandSide s t env env' -> ReEnv env subenv -> LivenessEnv env' -> BindLiveness s t env' subenv
bind lhs re (LivenessEnv env) = go lhs2 re
  where
    (env', lhs1) = envToLHSLiveness env lhs
    lhs2 = propagateLiveness env' re (lhsSkip' lhs) lhs1

    go :: LHSLiveness s t env1 env2 -> ReEnv env1 subenv1 -> BindLiveness s t env2 subenv1
    go (LHSLivenessWildcard tp)     re' = BindLiveness (LeftHandSideWildcard tp) re'
    go (LHSLivenessSingle True  tp) re' = BindLiveness (LeftHandSideSingle tp) (ReEnvKeep re')
    go (LHSLivenessSingle False tp) re' = BindLiveness (LeftHandSideWildcard $ TupRsingle tp) (ReEnvSkip re')
    go (LHSLivenessPair l1 l2)      re'
      | BindLiveness l1' re''  <- go l1 re'
      , BindLiveness l2' re''' <- go l2 re''
      = BindLiveness (leftHandSidePair l1' l2') re'''

-- Captures the existentional subenv'
data BindLiveness s t env' subenv where
  BindLiveness
    :: LeftHandSide s t subenv subenv'
    -> ReEnv env' subenv'
    -> BindLiveness s t env' subenv

bindSub :: LeftHandSide s t env env' -> ReEnv env subenv -> LivenessEnv env' -> BindLivenessSub s t env' subenv
bindSub lhs re (LivenessEnv env) = go lhs2 re
  where
    (env', lhs1) = envToLHSLiveness env lhs
    lhs2 = propagateLiveness env' re (lhsSkip' lhs) lhs1

    go :: LHSLiveness s t env1 env2 -> ReEnv env1 subenv1 -> BindLivenessSub s t env2 subenv1
    go (LHSLivenessWildcard TupRunit) re' = BindLivenessSub SubTupRkeep (LeftHandSideWildcard TupRunit) (LeftHandSideWildcard TupRunit) re'
    go (LHSLivenessWildcard tp)       re' = BindLivenessSub SubTupRskip (LeftHandSideWildcard tp) (LeftHandSideWildcard TupRunit) re'
    go (LHSLivenessSingle True  tp)   re' = BindLivenessSub SubTupRkeep (LeftHandSideSingle tp) (LeftHandSideSingle tp) (ReEnvKeep re')
    go (LHSLivenessSingle False tp)   re' = BindLivenessSub SubTupRskip (LeftHandSideWildcard $ TupRsingle tp) (LeftHandSideWildcard TupRunit) (ReEnvSkip re')
    go (LHSLivenessPair l1 l2)        re'
      | BindLivenessSub subTup1 l1' l1'' re''  <- go l1 re'
      , BindLivenessSub subTup2 l2' l2'' re''' <- go l2 re''
      = if
          | LeftHandSideWildcard _ <- l1''
          , LeftHandSideWildcard _ <- l2''
          -> BindLivenessSub SubTupRskip (leftHandSidePair l1' l2') (LeftHandSideWildcard TupRunit) re'''

          | SubTupRkeep <- subTup1
          , SubTupRkeep <- subTup2
          -> BindLivenessSub SubTupRkeep (leftHandSidePair l1' l2') (LeftHandSidePair l1'' l2'') re'''

          | otherwise
          -> BindLivenessSub (SubTupRpair subTup1 subTup2) (leftHandSidePair l1' l2') (LeftHandSidePair l1'' l2'') re'''

propagateReturnLiveness :: SubTupR t t' -> ReturnImplications env t -> LivenessEnv env -> LivenessEnv env
propagateReturnLiveness SubTupRskip         _                env = env
propagateReturnLiveness SubTupRkeep         ret              env
  = foldl' (\e (Exists (ReturnImplication set)) -> setIndicesLive (IdxSet.toList set) e) env $ flattenTupR ret
propagateReturnLiveness (SubTupRpair s1 s2) (TupRpair r1 r2) env
  = propagateReturnLiveness s1 r1 $ propagateReturnLiveness s2 r2 env
propagateReturnLiveness (SubTupRpair _ _)   _                _   = internalError "Pair impossible"

-- Captures the existentionals subenv' and t'
data BindLivenessSub s t env' subenv where
  BindLivenessSub
    :: SubTupR t t'
    -> LeftHandSide s t  subenv subenv'
    -> LeftHandSide s t' subenv subenv'
    -> ReEnv env' subenv'
    -> BindLivenessSub s t env' subenv

data DeclareSubVars s t t' env where
  DeclareSubVars :: LeftHandSide s t env env'
                 -> (env :> env')
                 -> (forall env''. env' :> env'' -> Vars s env'' t')
                 -> DeclareSubVars s t t' env

declareSubVars :: TupR s t -> SubTupR t t' -> DeclareSubVars s t t' env
declareSubVars tp SubTupRkeep
  | DeclareVars lhs k vars <- declareVars tp = DeclareSubVars lhs k vars
declareSubVars tp SubTupRskip
  = DeclareSubVars (LeftHandSideWildcard tp) weakenId (const TupRunit)
declareSubVars (TupRpair t1 t2) (SubTupRpair s1 s2)
  | DeclareSubVars lhs1 subst1 a1 <- declareSubVars t1 s1
  , DeclareSubVars lhs2 subst2 a2 <- declareSubVars t2 s2
  = DeclareSubVars (LeftHandSidePair lhs1 lhs2) (subst2 .> subst1) $ \k -> a1 (k .> subst2) `TupRpair` a2 k
declareSubVars _ _ = internalError "Tuple mismatch"

-- For an IR parameterized over the result type, implement a function of this
-- type:
--
-- stronglyLiveVariables :: LivenessEnv env -> SomeAcc env t -> LVAnalysis SomeAcc env t
--
-- If the IR does have a result type, but we cannot change that type, then use:
--
-- stronglyLiveVariables :: LivenessEnv env -> SomeAcc env t -> LVAnalysisFun SomeAcc env t
--
-- For an IR which is not parameterized over the result type, but only over the
-- environment, implement a function of this type:
--
-- stronglyLiveVariables :: LivenessEnv env -> SomeAcc env -> LVAnalysis' SomeAcc env

-- If this part of the returned value is returned, then this set of variables is live
newtype ReturnImplication env t = ReturnImplication (IdxSet env)
type ReturnImplications env = TupR (ReturnImplication env)

noReturnImplications :: ReturnImplications env t
noReturnImplications = TupRsingle $ ReturnImplication IdxSet.empty

joinReturnImplication :: ReturnImplication env t -> ReturnImplication env t -> ReturnImplication env t
joinReturnImplication (ReturnImplication a) (ReturnImplication b) = ReturnImplication $ IdxSet.union a b

joinReturnImplications :: ReturnImplications env t -> ReturnImplications env t -> ReturnImplications env t
joinReturnImplications (TupRsingle (ReturnImplication left))   right = mapTupR (joinReturnImplication $ ReturnImplication left) right
joinReturnImplications left   (TupRsingle (ReturnImplication right)) = mapTupR (joinReturnImplication $ ReturnImplication right) left
joinReturnImplications (TupRpair l1 l2)       (TupRpair r1 r2)       = joinReturnImplications l1 r1 `TupRpair` joinReturnImplications l2 r2
joinReturnImplications TupRunit               TupRunit               = TupRunit

data SubTupR t t' where
  SubTupRskip :: SubTupR t ()

  SubTupRkeep :: SubTupR t t

  SubTupRpair :: SubTupR t1 t1'
              -> SubTupR t2 t2'
              -> SubTupR (t1, t2) (t1', t2')

subTupR :: SubTupR t t' -> TupR s t -> TupR s t'
subTupR SubTupRskip         _                = TupRunit
subTupR SubTupRkeep         t                = t
subTupR (SubTupRpair s1 s2) (TupRpair t1 t2) = subTupR s1 t1 `TupRpair` subTupR s2 t2
subTupR _                   _                = internalError "Tuple mismatch"

subTupUnit :: SubTupR () t' -> t' :~: ()
subTupUnit SubTupRskip = Refl
subTupUnit SubTupRkeep = Refl

data LVAnalysis ir env t where
  LVAnalysis
    :: LivenessEnv env
    -> ReturnImplications env t
    -- Depending on the binding, it may or may not be possible to restrict the
    -- term to only the used parts of the tuple.
    -> (forall subenv t'. ReEnv env subenv -> SubTupR t t' -> Either (ir subenv t) (ir subenv t'))
    -> LVAnalysis ir env t

data LVAnalysisFun ir env t where
  LVAnalysisFun
    :: LivenessEnv env
    -> (forall subenv. ReEnv env subenv -> ir subenv t)
    -> LVAnalysisFun ir env t

data LVAnalysis' ir env where
  LVAnalysis'
    :: LivenessEnv env
    -> (forall subenv. ReEnv env subenv -> ir subenv)
    -> LVAnalysis' ir env

allDead :: ReEnv env subenv -> IdxSet env -> Bool
allDead re set = all (\(Exists idx) -> isNothing $ reEnvIdx re idx) $ IdxSet.toList set

expectJust :: HasCallStack => Maybe a -> a
expectJust (Just a) = a
expectJust Nothing  = internalError "Substitution in live variable analysis failed. A variable which was assumed to be dead appeared to be live."

-- Utilities for expressions
subTupExp :: IsArrayInstr arr => SubTupR t t' -> PreOpenExp arr env t -> PreOpenExp arr env t'
subTupExp SubTupRkeep expr = expr
subTupExp SubTupRskip _    = Nil
subTupExp subTup      expr
  | DeclareSubVars lhs _ vars <- declareSubVars (expType expr) subTup
  = Let lhs expr $ expVars $ vars weakenId

subTupFun :: IsArrayInstr arr => SubTupR t t' -> PreOpenFun arr env (s -> t) -> PreOpenFun arr env (s -> t')
subTupFun subTup (Lam lhs (Body body)) = Lam lhs $ Body $ subTupExp subTup body
subTupFun _      _                     = internalError "Function impossible"
