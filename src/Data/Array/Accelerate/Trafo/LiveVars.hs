{-# LANGUAGE GADTs                #-}
{-# LANGUAGE LambdaCase           #-}
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
  , bind, BindLiveness(..)
  , LVAnalysis(..), LVAnalysis'(..)
  ) where

import Data.Array.Accelerate.AST.Environment
import Data.Array.Accelerate.AST.Idx
import Data.Array.Accelerate.AST.IdxSet ( IdxSet(..) )
import Data.Array.Accelerate.AST.Var
import qualified Data.Array.Accelerate.AST.IdxSet as IdxSet
import Data.Array.Accelerate.AST.LeftHandSide
import Data.Array.Accelerate.Representation.Type
import Data.Array.Accelerate.Trafo.Exp.Substitution
import Data.Array.Accelerate.Trafo.Substitution

import Data.List (foldl')
import Data.Maybe

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

newtype LivenessEnv env = LivenessEnv (Env (Liveness env) env)

emptyLivenessEnv :: LivenessEnv ()
emptyLivenessEnv = LivenessEnv Empty

setLive :: forall env t. Idx env t -> LivenessEnv env -> LivenessEnv env
setLive idx (LivenessEnv env) = foldl' (\e (Exists idx') -> setLive idx' e) (LivenessEnv env') implied
  where
    (env', implied) = prjUpdate' f idx env

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
    (env', live) = prjUpdate' f idx env
    f Live = (Live, True)
    f (Unknown implied') = (Unknown $ IdxSet.union implied implied', False)


setLivenessImplications :: IdxSet env -> IdxSet env -> LivenessEnv env -> LivenessEnv env
setLivenessImplications indices implied env = foldl' (\e (Exists idx) -> setLivenessImplies idx implied e) env $ IdxSet.toList indices

isLive :: LivenessEnv env -> Idx env t -> Bool
isLive (LivenessEnv env) idx
  | Live <- prj' idx env = True
  | otherwise            = False

strengthenLiveness :: forall env' env t. LivenessEnv env' -> env' :?> env -> Liveness env' t -> Liveness env t
strengthenLiveness (LivenessEnv env) k (Unknown implies) = Unknown $ implies IdxSet.>>= go
  where
    go :: Idx env' s -> IdxSet env
    go idx
      | Just idx' <- k idx = IdxSet.singleton idx'
      | Unknown implies' <- prj' idx env = implies' IdxSet.>>= go
      | otherwise = IdxSet.empty
strengthenLiveness _   _ Live              = Live

dropLivenessEnv :: forall s t env env'. LeftHandSide s t env env' -> LivenessEnv env' -> LivenessEnv env
dropLivenessEnv lhs lenv@(LivenessEnv env) = LivenessEnv $ mapEnv (strengthenLiveness lenv k) $ go lhs env
  where
    k :: env' :?> env
    k = strengthenWithLHS lhs

    go :: LeftHandSide s t' env1 env2 -> Env (Liveness env') env2 -> Env (Liveness env') env1
    go (LeftHandSideSingle _)   (Push e _) = e
    go (LeftHandSideWildcard _) e          = e
    go (LeftHandSidePair l1 l2) e          = go l1 $ go l2 e

pushLivenessEnv :: forall s t env env'. LeftHandSide s t env env' -> LivenessEnv env -> LivenessEnv env'
pushLivenessEnv lhs (LivenessEnv env) = LivenessEnv $ go lhs $ mapEnv (weaken k) env
  where
    k :: env :> env'
    k = weakenWithLHS lhs

    go :: LeftHandSide s t' env1 env2 -> Env (Liveness env') env1 -> Env (Liveness env') env2
    go (LeftHandSideSingle _) e = Push e dead
    go (LeftHandSideWildcard _) e = e
    go (LeftHandSidePair l1 l2) e = go l2 $ go l1 e

-- Similar to LeftHandSide, but LeftHandSideSingle is annotated with a boolean
-- denoting whether the variable is live.
--
data LHSLiveness s t env env' where
  LHSLivenessWildcard :: TupR s t -> LHSLiveness s t env env
  LHSLivenessSingle   :: Bool -> s t -> LHSLiveness s t env (env, t)
  LHSLivenessPair     :: LHSLiveness s t1 env env'
                      -> LHSLiveness s t2 env' env''
                      -> LHSLiveness s (t1, t2) env env''

-- Creates an LHSLiveness where the bindings with Live are marked as live.
-- Note that in 'bind' we still need to mark more bindings live, as they
-- can be implied by live free variables (following from ReEnv).
--
envToLHSLiveness
  :: Env (Liveness env'') env'
  -> LeftHandSide s t env env'
  -> (Env (Liveness env'') env, LHSLiveness s t env env')
envToLHSLiveness env             (LeftHandSideWildcard tp) = (env, LHSLivenessWildcard tp)
envToLHSLiveness (Push env Live) (LeftHandSideSingle tp)   = (env, LHSLivenessSingle True tp)
envToLHSLiveness (Push env _)    (LeftHandSideSingle tp)   = (env, LHSLivenessSingle False tp)
envToLHSLiveness env             (LeftHandSidePair l1 l2)  = (env'', LHSLivenessPair l1' l2')
  where
    (env',  l2') = envToLHSLiveness env  l2
    (env'', l1') = envToLHSLiveness env' l1

propagateLiveness :: Env (Liveness env') env -> ReEnv env subenv -> LHSLiveness s t env1 env' -> LHSLiveness s t env1 env'
propagateLiveness (Push env _)                 (ReEnvSkip re) lhs = propagateLiveness env re lhs
propagateLiveness (Push env (Unknown implied)) (ReEnvKeep re) lhs = propagateLiveness env re $ snd $ lhsMarkLive implied lhs
propagateLiveness (Push env Live)              (ReEnvKeep re) lhs = propagateLiveness env re lhs
propagateLiveness Empty                        ReEnvEnd       lhs = lhs

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
    lhs2 = propagateLiveness env' re lhs1

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

-- For an IR parameterized over the result type, implement a function of this
-- type:
--
-- stronglyLiveVariables :: LivenessEnv env -> SomeAcc env t -> LVAnalysis ir env t
--
-- For an IR which is not parameterized over the result type, but only over the
-- environment, implement a function of this type:
--
-- stronglyLiveVariables :: LivenessEnv env -> SomeAcc env -> LVAnalysis' ir env

data LVAnalysis ir env t where
  LVAnalysis
    :: LivenessEnv env
    -> (forall subenv. ReEnv env subenv -> ir subenv t)
    -> LVAnalysis ir env t

data LVAnalysis' ir env where
  LVAnalysis'
    :: LivenessEnv env
    -> (forall subenv. ReEnv env subenv -> ir subenv)
    -> LVAnalysis' ir env

