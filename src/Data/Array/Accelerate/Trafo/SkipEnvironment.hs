{-# LANGUAGE EmptyCase           #-}
{-# LANGUAGE GADTs               #-}
{-# LANGUAGE LambdaCase          #-}
{-# LANGUAGE RankNTypes          #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications    #-}
{-# LANGUAGE TypeOperators       #-}
{-# OPTIONS_HADDOCK hide #-}
{-# LANGUAGE PatternSynonyms #-}
-- |
-- Module      : Data.Array.Accelerate.AST.SkipEnvironment
-- Copyright   : [2008..2020] The Accelerate Team
-- License     : BSD3
--
-- Maintainer  : Trevor L. McDonell <trevor.mcdonell@gmail.com>
-- Stability   : experimental
-- Portability : non-portable (GHC extensions)
--

module Data.Array.Accelerate.Trafo.SkipEnvironment
  ( SEnv, SEnv'(..), SEnvValue(..), sempty, spush, spush', sprj, weakenSEnv1, weakenSEnv,
    strengthenSEnv, sprjUpdate, senvTop,
    Skip'(..), joinSkips',
    skipWeakenPartialEnv, skipWeakenPartialEnv',
    skipWeakenIdxSet, skipWeakenIdxSet',
    skipStrengthenPartialEnv, skipStrengthenPartialEnv',
    skipStrengthenIdxSet, skipStrengthenIdxSet',
    skipTakePartialEnv', skipTakeIdxSet',
    lhsSkip', skipReverse, skipWeakenIdx'
  ) where

import Data.Array.Accelerate.AST.Environment
import Data.Array.Accelerate.AST.Idx
import Data.Array.Accelerate.AST.IdxSet (IdxSet(..))
import Data.Array.Accelerate.AST.LeftHandSide

-- Similar to Skip, but weakening happens on the other side, similar to the
-- difference between weakenSucc and weakenSucc'
--
data Skip' env env' where
  SkipSucc' :: Skip' env env' -> Skip' (env, t) env'
  SkipNone' :: Skip' env env

chainSkip' :: Skip' env1 env2 -> Skip' env2 env3 -> Skip' env1 env3
chainSkip' (SkipSucc' skipL) skipR = SkipSucc' $ chainSkip' skipL skipR
chainSkip' SkipNone'         skipR = skipR

chainSkip'' :: Skip env1 env2 -> Skip' env2 env3 -> Skip env1 env3
chainSkip'' skipL (SkipSucc' skipR) = chainSkip'' (SkipSucc skipL) skipR
chainSkip'' skipL SkipNone'         = skipL

skipReverse :: forall env1 env2. Skip env1 env2 -> Skip' env1 env2
skipReverse = (`go` SkipNone')
  where
    go :: Skip env1 env -> Skip' env env2 -> Skip' env1 env2
    go (SkipSucc s) accum = go s (SkipSucc' accum)
    go SkipNone     accum = accum

skipWeakenIdx' :: Skip' env env' -> env' :> env
skipWeakenIdx' (SkipSucc' s) = weakenSucc' $ skipWeakenIdx' s
skipWeakenIdx' SkipNone'     = weakenId

type SEnv f env = SEnv' f env env

data SEnv' f env' env where
  SEmpty :: SEnv' f env' ()
  SPush  :: SEnv' f env' env -> f env' t -> SEnv' f env'      (env, t)
  SSkip  :: Skip' env2 env1 -> SEnv' f env1 env -> SEnv' f env2 env

class SEnvValue f where
  -- Instead of using (:>) in weaken, we use Skip and Skip' here. This way we
  -- can weaken an IdxSet more efficiently.
  -- We have a variant with Skip and one with Skip' to prevent reversing the
  -- Skip during traversals.
  weakenSEnvValue  :: Skip  env1 env2 -> f env2 t -> f env1 t
  weakenSEnvValue' :: Skip' env1 env2 -> f env2 t -> f env1 t

  strengthenSEnvValue :: SEnv f env1 -> Skip env1 env2 -> f env1 t -> f env2 t

sempty :: SEnv f ()
sempty = SEmpty

spush :: SEnv f env -> f (env, t) t -> SEnv f (env, t)
spush env v = SPush (weakenSEnv1 env) v

spush' :: SEnv' f env' env -> f env' t -> SEnv' f env' (env, t)
spush' = SPush

-- We assume that doing weakenSEnvValue multiple times is cheaper than doing it
-- once and combining the Skips with chainSkip'.
sprj :: SEnvValue f => Idx envB t -> SEnv' f envA envB -> f envA t
sprj idx (SSkip s env) = weakenSEnvValue' s $ sprj idx env
sprj ZeroIdx (SPush _ v) = v
sprj (SuccIdx idx) (SPush env _) = sprj idx env

sprjUpdate :: forall f env t a. SEnvValue f => (f env t -> (f env t, a)) -> Idx env t -> SEnv f env -> (SEnv f env, a)
sprjUpdate f = go SkipNone
  where
    -- We must remove all SSkips until we arrive at the given index.
    go :: Skip env env1 -> Idx env' t -> SEnv' f env1 env' -> (SEnv' f env env', a)
    go skip idx (SSkip skip' env) = go (chainSkip'' skip skip') idx env
    go skip ZeroIdx (SPush env v) = (SPush env' v', a)
      where
        env' = weakenSEnv (skipReverse skip) env
        (v', a) = f $ weakenSEnvValue skip v
    go skip (SuccIdx idx) (SPush env v) = (SPush env' v', a)
      where
        (env', a) = go skip idx env
        v' = weakenSEnvValue skip v

senvTop :: SEnvValue f => SEnv' f env' (env, t) -> (SEnv' f env' env, f env' t)
senvTop (SPush env v) = (env, v)
senvTop (SSkip skip env) = (weakenSEnv skip env', weakenSEnvValue' skip v)
  where
    (env', v) = senvTop env

weakenSEnv1 :: SEnv' f env1 env -> SEnv' f (env1, t) env
weakenSEnv1 (SSkip s env) = SSkip (SkipSucc' s) env
weakenSEnv1 env           = SSkip (SkipSucc' SkipNone') env

weakenSEnv :: Skip' env1 env2 -> SEnv' f env2 env -> SEnv' f env1 env
weakenSEnv SkipNone' env            = env
weakenSEnv s1       (SSkip s2 env) = SSkip (chainSkip' s1 s2) env
weakenSEnv s1       env            = SSkip s1 env

strengthenSEnv :: SEnvValue f => Skip' env1 env2 -> SEnv f env1 -> SEnv f env2
strengthenSEnv skip initialEnv = strengthenSEnv' SkipNone initialEnv skip $ go skip initialEnv -- strengthenSEnv' SkipNone env skip env
  where
    go :: Skip' env env' -> SEnv' f env1 env -> SEnv' f env1 env'
    go SkipNone'     env            = env
    go (SkipSucc' s) (SPush env _)  = go s env
    go s             (SSkip s' env) = SSkip s' $ go s env

-- Note that we use Skip instead of Skip' for initialSkip. This way we can use
-- chainSkip'' instead of chainSkip'. chainSkip' recurses on the first argument
-- causing that the traversal would do quadratic work on constructing Skip'
-- objects. chainSkip'' recurses on the second argument, which prevents us from
-- recursing repeatedly on initialSkip (in each recursive call, except the base
-- cases).
--
strengthenSEnv' :: SEnvValue f => Skip env0 env1 -> SEnv f env0 -> Skip' env1 env2 -> SEnv' f env1 env -> SEnv' f env2 env
strengthenSEnv' _ _ SkipNone' env = env
strengthenSEnv' _ _ _ SEmpty = SEmpty
strengthenSEnv' initialSkip initialEnv s (SSkip s' env) = case joinSkips' s' s of
  Left l  -> SSkip l env
  Right r -> strengthenSEnv' (chainSkip'' initialSkip s') initialEnv r env
strengthenSEnv' initialSkip initialEnv s (SPush env v)
  = SPush (strengthenSEnv' initialSkip initialEnv s env)
  $ strengthenSEnvValue initialEnv (chainSkip'' initialSkip s)
  $ weakenSEnvValue initialSkip v

-- Returns `Right SkipNone'` if env2 ~ env3
joinSkips' :: Skip' env1 env2 -> Skip' env1 env3 -> Either (Skip' env3 env2) (Skip' env2 env3)
joinSkips' SkipNone'     r             = Right r
joinSkips' l             SkipNone'     = Left l
joinSkips' (SkipSucc' l) (SkipSucc' r) = joinSkips' l r

skipWeakenPartialEnv :: Skip env1 env2 -> PartialEnv f env2 -> PartialEnv f env1
skipWeakenPartialEnv SkipNone     env = env
skipWeakenPartialEnv (SkipSucc s) env = skipWeakenPartialEnv s $ partialEnvSkip env

skipWeakenPartialEnv' :: Skip' env1 env2 -> PartialEnv f env2 -> PartialEnv f env1
skipWeakenPartialEnv' SkipNone'     env = env
skipWeakenPartialEnv' (SkipSucc' s) env = partialEnvSkip $ skipWeakenPartialEnv' s env

skipWeakenIdxSet :: Skip env1 env2 -> IdxSet env2 -> IdxSet env1
skipWeakenIdxSet s (IdxSet env) = IdxSet $ skipWeakenPartialEnv s env

skipWeakenIdxSet' :: Skip' env1 env2 -> IdxSet env2 -> IdxSet env1
skipWeakenIdxSet' s (IdxSet env) = IdxSet $ skipWeakenPartialEnv' s env

skipStrengthenPartialEnv :: Skip env1 env2 -> PartialEnv f env1 -> PartialEnv f env2
skipStrengthenPartialEnv SkipNone     env = env
skipStrengthenPartialEnv (SkipSucc s) env = partialEnvTail $ skipStrengthenPartialEnv s env

skipStrengthenPartialEnv' :: Skip' env1 env2 -> PartialEnv f env1 -> PartialEnv f env2
skipStrengthenPartialEnv' SkipNone'     env = env
skipStrengthenPartialEnv' (SkipSucc' s) env = skipStrengthenPartialEnv' s $ partialEnvTail env

skipStrengthenIdxSet :: Skip env1 env2 -> IdxSet env1 -> IdxSet env2
skipStrengthenIdxSet s (IdxSet env) = IdxSet $ skipStrengthenPartialEnv s env

skipStrengthenIdxSet' :: Skip' env1 env2 -> IdxSet env1 -> IdxSet env2
skipStrengthenIdxSet' s (IdxSet env) = IdxSet $ skipStrengthenPartialEnv' s env

skipTakePartialEnv' :: Skip' env1 env2 -> PartialEnv f env1 -> PartialEnv f env1
skipTakePartialEnv' SkipNone' env = env
skipTakePartialEnv' (SkipSucc' _) PEnd          = PEnd
skipTakePartialEnv' (SkipSucc' s) (PPush env v) = PPush (skipTakePartialEnv' s env) v
skipTakePartialEnv' (SkipSucc' s) (PNone env)   = PNone (skipTakePartialEnv' s env)

skipTakeIdxSet' :: Skip' env1 env2 -> IdxSet env1 -> IdxSet env1
skipTakeIdxSet' s (IdxSet env) = IdxSet $ skipTakePartialEnv' s env

lhsSkip' :: forall s t env1 env2. LeftHandSide s t env1 env2 -> Skip' env2 env1
lhsSkip' = (`go` SkipNone')
  where
    go :: LeftHandSide s t' env env' -> Skip' env env1 -> Skip' env' env1
    go (LeftHandSideSingle _)   accum = SkipSucc' accum
    go (LeftHandSideWildcard _) accum = accum
    go (LeftHandSidePair l1 l2) accum = go l2 $ go l1 accum
