{-# LANGUAGE ConstraintKinds     #-}
{-# LANGUAGE FlexibleInstances   #-}
{-# LANGUAGE GADTs               #-}
{-# LANGUAGE KindSignatures      #-}
{-# LANGUAGE LambdaCase          #-}
{-# LANGUAGE MultiWayIf          #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE PatternGuards       #-}
{-# LANGUAGE RankNTypes          #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell     #-}
{-# LANGUAGE TupleSections       #-}
{-# LANGUAGE TypeApplications    #-}
{-# LANGUAGE TypeFamilies        #-}
{-# LANGUAGE TypeOperators       #-}
{-# LANGUAGE ViewPatterns        #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}
{-# OPTIONS_HADDOCK hide #-}
-- |
-- Module      : Data.Array.Accelerate.Trafo.Schedule.Uniform.Simplify
-- Copyright   : [2012..2020] The Accelerate Team
-- License     : BSD3
--
-- Maintainer  : Trevor L. McDonell <trevor.mcdonell@gmail.com>
-- Stability   : experimental
-- Portability : non-portable (GHC extensions)
--

module Data.Array.Accelerate.Trafo.Schedule.Uniform.Simplify (
  simplifyFun, simplify, emptySimplifyEnv,

  -- Utilities
  spawnUnless, spawn, spawns, serial,

  -- Construction DSL
  BuildSchedule, BuildScheduleFun, funConstruct,
  buildAcond, buildAwhile, buildEffect, buildSpawn,
  buildLet, buildReturn, buildSeq,
  buildFunBody, buildFunLam,
) where
import Debug.Trace
import Data.Array.Accelerate.AST.Environment
import Data.Array.Accelerate.AST.Idx
import Data.Array.Accelerate.AST.IdxSet (IdxSet)
import qualified Data.Array.Accelerate.AST.IdxSet           as IdxSet
import qualified Data.Array.Accelerate.AST.CountEnv         as CountEnv
import Data.Array.Accelerate.AST.LeftHandSide
import Data.Array.Accelerate.AST.Schedule.Uniform
import Data.Array.Accelerate.Error
import Data.Array.Accelerate.Representation.Array
import Data.Array.Accelerate.Representation.Type
import Data.Array.Accelerate.Trafo.Exp.Simplify             ( simplifyExp )
import Data.Array.Accelerate.Trafo.Exp.Substitution
import Data.Array.Accelerate.Trafo.Operation.Substitution   ( weakenArrayInstr )
import Data.Array.Accelerate.Trafo.Substitution             hiding ( weakenArrayInstr )
import Data.Array.Accelerate.Trafo.WeakenedEnvironment
import Data.Array.Accelerate.Trafo.Schedule.Uniform.Substitution ()
import Data.Array.Accelerate.Type
import Data.Maybe
import Data.List
    ( foldl',
      find,
      isSubsequenceOf,
      (\\),
      nub,
      partition,
      sort,
      mapAccumR )
import qualified Data.List as List
import Control.Monad
import Data.Bifunctor (first)

data InfoEnv env = InfoEnv
  (WEnv Info env)
  -- List of signals that we waited on after resolving the last signal.
  -- Also includes the index of the signals that we resolved last.
  (IdxSet env)

emptySimplifyEnv :: InfoEnv ()
emptySimplifyEnv = InfoEnv wempty IdxSet.empty

data Info env t where
  InfoSignalResolver
    :: Maybe (Idx env Signal)
    -> Info env SignalResolver

  InfoSignalResolved
    :: Info env Signal

  InfoSignalImplies
    -- When this signal is resolved, the following signals will also be resolved
    :: [Idx env Signal]
    -> Info env Signal

  InfoSignalInstead
    -- Instead of waiting on this signal, wait on the following signals
    :: [Idx env Signal]
    -> Info env Signal

  InfoRefWrite
    :: Maybe (Idx env (Ref t))
    -> Info env (OutputRef t)

  InfoRef
    :: Maybe (Idx env t)
    -> Info env (Ref t)

  InfoScalar
    :: ScalarType t
    -- If aliased, this points to a variable of the same value.
    -- This field will only point to variables defined earlier in the program
    -- and can thus not form unification cycles.
    -> Maybe (Idx env t)
    -> Info env t

  InfoBuffer
    -- If aliased, this points to a variable of the same value.
    -- This field will only point to variables defined earlier in the program
    -- and can thus not form unification cycles.
    :: Maybe (Idx env (Buffer t))
    -> Info env (Buffer t)

instance Sink Info where
  weaken k (InfoSignalResolver signal) = InfoSignalResolver $ fmap (weaken k) signal
  weaken _ InfoSignalResolved = InfoSignalResolved
  weaken k (InfoSignalImplies signals) = InfoSignalImplies $ map (weaken k) signals
  weaken k (InfoSignalInstead signals) = InfoSignalInstead $ map (weaken k) signals
  weaken k (InfoRefWrite ref) = InfoRefWrite $ fmap (weaken k) ref
  weaken k (InfoRef value) = InfoRef $ fmap (weaken k) value
  weaken k (InfoScalar tp alias) = InfoScalar tp $ fmap (weaken k) alias
  weaken k (InfoBuffer    alias) = InfoBuffer    $ fmap (weaken k) alias

-- When the first signal is resolved, all the signals in the list will have
-- been resolved as well.
data SignalImplication env = SignalImplication (Idx env Signal) (IdxSet env)

strengthenImplication :: LeftHandSide s t env env' -> SignalImplication env' -> Maybe (SignalImplication env)
strengthenImplication lhs (SignalImplication idx implies)
  | Just idx' <- strengthenWithLHS lhs idx
  , implies' <- IdxSet.drop' lhs implies
  , not $ IdxSet.isEmpty implies' = Just $ SignalImplication idx' implies'
  | otherwise = Nothing -- idx doesn't exist in env, or implies' became empty.

simplifyFun :: InfoEnv env -> UniformScheduleFun kernel env f -> UniformScheduleFun kernel env f
simplifyFun env (Slam lhs fn) = Slam lhs $ simplifyFun (bindEnv lhs env) fn
simplifyFun env (Sbody body)  = Sbody $ simplify env body

simplify :: InfoEnv env -> UniformSchedule kernel env -> UniformSchedule kernel env
simplify env schedule = snd $ simplify' env schedule

simplify' :: InfoEnv env -> UniformSchedule kernel env -> ([SignalImplication env], UniformSchedule kernel env)
-- Spawn
simplify' env s@Spawn{} = simplifySpawns env s
-- Effects
simplify' env (Effect effect next) = (implications1 ++ implications2, instr next')
  where
    (implications1, env', instr) = simplifyEffect env effect
    (implications2, next') = simplify' env' next
-- Bindings
simplify' env (Alet lhs binding next) = (mapMaybe (strengthenImplication lhs) implications, schedule)
  where
    binding' = case binding of
      RefRead{} -> binding -- We don't have to apply the substitution here, as the substitution doesn't affect references
      _ -> weaken (substitute env) binding

    binding'' = case binding' of
      Compute e -> Compute $ simplifyExp e
      _ -> binding'

    env' = bindingEnv lhs binding'' env

    (implications, next') = simplify' env' next

    schedule = case binding'' of
      Compute e -> bindExp lhs (simplifyExp e) next'
      _ -> Alet lhs binding'' next'
-- Control flow
simplify' _ Return = ([], Return)
simplify' env (Acond condition true false next)
  | Return <- true'
  , Return <- false' = simplify' env next
  | otherwise = (implications ++ implicationsNext, Acond condition' true' false' next')
  where
    condition' = weaken (substitute env) condition

    -- We cannot directly propagate the signal implications from the true and
    -- the false branch, as such implication only holds if we went into that
    -- branch. We can act on those implications if they follow from both
    -- branches, i.e. take the intersection of the implications. Currently we
    -- just ignore these implications, as I expect we won't often find any
    -- implications from both branches and then it's a waste of time to compute
    -- those intersections.
    --
    (implicationsTrue,  true')  = simplify' env true
    (implicationsFalse, false') = simplify' env false
    implications = intersectSignalImplications implicationsTrue implicationsFalse
    env' = propagate implications env
    (implicationsNext,  next')  = simplify' env' next
simplify' env (Awhile io body initial next) = Awhile io (simplifyFun env body) (mapTupR (weaken $ substitute env) initial) <$> simplify' env next

intersectSignalImplications :: [SignalImplication env] -> [SignalImplication env] -> [SignalImplication env]
intersectSignalImplications as bs = mapMaybe f as
  where
    f (SignalImplication idx set) = case find (\(SignalImplication idx' _) -> idx == idx') bs of
      Just (SignalImplication _ set') -> Just $ SignalImplication idx $ IdxSet.intersect set set'
      Nothing -> Nothing

simplifyEffect :: InfoEnv env -> Effect kernel env -> ([SignalImplication env], InfoEnv env, UniformSchedule kernel env -> UniformSchedule kernel env)
simplifyEffect env (Exec md kernel args) = ([], env, Effect $ Exec md kernel $ mapArgs (weaken $ substitute env) args)
simplifyEffect env (SignalAwait awaits) = ([], env', instr)
  where
    (env', instr) = await' env awaits
simplifyEffect env (SignalResolve resolvers) = (implications, env', Effect $ SignalResolve resolvers)
  where
    (env', implications) = resolves' env resolvers
simplifyEffect env (RefWrite ref value) = ([], env', Effect $ RefWrite ref value')
  where
    value' = weaken (substitute env) value
    env' = refWrite env (varIdx ref) (varIdx value')

infoFor :: Idx env t -> InfoEnv env -> Info env t
infoFor ix (InfoEnv env _) = wprj ix env

setInfo :: Idx env t -> Info env t -> InfoEnv env -> InfoEnv env
setInfo ix info (InfoEnv env signals) = InfoEnv (wupdate (const info) ix env) signals

bindEnv :: BLeftHandSide t env env' -> InfoEnv env -> InfoEnv env'
bindEnv lhs (InfoEnv env' awaitedSignals) = InfoEnv (go lhs $ weaken k env') $ IdxSet.skip' lhs awaitedSignals
  where
    k = weakenWithLHS lhs

    go :: BLeftHandSide t env1 env1' -> WEnv' Info env' env1 -> WEnv' Info env' env1'
    go (LeftHandSideWildcard _) env1 = env1
    go (LeftHandSideSingle t)   env1 = wpush' env1 $ case t of
      BaseRsignal                    -> InfoSignalImplies []
      BaseRsignalResolver            -> InfoSignalResolver Nothing
      BaseRref _                     -> InfoRef Nothing
      BaseRrefWrite _                -> InfoRefWrite Nothing
      BaseRground (GroundRbuffer _)  -> InfoBuffer Nothing
      BaseRground (GroundRscalar tp) -> InfoScalar tp Nothing
    go (LeftHandSidePair l1 l2) env1 = go l2 $ go l1 env1

bindingEnv :: BLeftHandSide t env env' -> Binding env t -> InfoEnv env -> InfoEnv env'
bindingEnv lhs@(LeftHandSideSingle _) (RefRead ref) env = refRead (bindEnv lhs env) (weaken (weakenSucc weakenId) $ varIdx ref) ZeroIdx
bindingEnv (LeftHandSideSingle _ `LeftHandSidePair` LeftHandSideSingle _) (NewSignal _) (InfoEnv env awaitedSignals)
  = InfoEnv (wpush2 env (InfoSignalImplies []) (InfoSignalResolver $ Just $ SuccIdx ZeroIdx)) awaitedSignals'
  where
    awaitedSignals' = IdxSet.skip $ IdxSet.skip awaitedSignals
bindingEnv (LeftHandSideSingle _ `LeftHandSidePair` LeftHandSideSingle _) (NewRef _) (InfoEnv env awaitedSignals)
  = InfoEnv (wpush2 env (InfoRef Nothing) (InfoRefWrite $ Just $ SuccIdx ZeroIdx)) awaitedSignals'
  where
    awaitedSignals' = IdxSet.skip $ IdxSet.skip awaitedSignals
bindingEnv (LeftHandSideSingle (BaseRground (GroundRscalar tp))) (Compute (ArrayInstr (Parameter var) Nil)) (InfoEnv env awaitedSignals)
  = InfoEnv (wpush env (InfoScalar tp $ Just $ SuccIdx $ varIdx var)) awaitedSignals'
  where
    awaitedSignals' = IdxSet.skip awaitedSignals
bindingEnv lhs _ env = bindEnv lhs env

propagate :: forall env. [SignalImplication env] -> InfoEnv env -> InfoEnv env
propagate implications infoEnv@(InfoEnv env awaitedSignals) = InfoEnv (foldl' add env implications) awaitedSignals
  where
    add :: WEnv Info env -> SignalImplication env -> WEnv Info env
    add env1 (SignalImplication signal implied) = wupdate (f $ map toSignal $ IdxSet.toList implied) signal env1

    f :: [Idx env Signal] -> Info env Signal -> Info env Signal
    f newImplied (InfoSignalImplies implied) = InfoSignalImplies (newImplied' ++ implied)
      where
        newImplied' = filter (`notElem` implied) newImplied
    f _ info = info

    toSignal :: Exists (Idx env) -> Idx env Signal
    toSignal (Exists idx) = case infoFor idx infoEnv of
      InfoSignalImplies _ -> idx
      InfoSignalInstead _ -> idx
      InfoSignalResolved  -> idx
      _                   -> internalError "Expected this index to point to a Signal"

-- On a schedule of this form:
--   spawn { await [s1, s2]; resolve [s3']}
--   next
--
-- We will replace 'await [s3]' with 'await [s1, s2]'.
-- This function will, given the spawned schedule, update the InfoEnv
-- to remember that s3 should be replaced with [s1, s2].
findSignalReplacements :: forall kernel env. UniformSchedule kernel env -> InfoEnv env -> InfoEnv env
findSignalReplacements = go []
  where
    go :: [Idx env Signal] -> UniformSchedule kernel env -> InfoEnv env -> InfoEnv env
    go signals (Effect (SignalAwait awaits)      next) env = go (awaits ++ signals) next env
    go signals (Effect (SignalResolve resolvers) next) env = go signals next $ foldl' (add signals) env resolvers
    go _ _ env = env

    add :: [Idx env Signal] -> InfoEnv env -> Idx env SignalResolver -> InfoEnv env
    add signals env resolver
      | InfoSignalResolver (Just signal) <- infoFor resolver env
      = setInfo signal (InfoSignalInstead signals) env
      | otherwise = env

resolve' :: forall env. InfoEnv env -> Idx env SignalResolver -> (InfoEnv env, [SignalImplication env])
resolve' env@(InfoEnv env' awaitedSignals) resolver
  | InfoSignalResolver (Just signal) <- infoFor resolver env =
    ( InfoEnv (wupdate (const InfoSignalResolved) signal env') (IdxSet.insert signal awaitedSignals)
    , if IdxSet.isEmpty awaitedSignals then [] else [SignalImplication signal awaitedSignals]
    )
  | otherwise =
    ( env
    , []
    )


resolves' :: forall env. InfoEnv env -> [Idx env SignalResolver] -> (InfoEnv env, [SignalImplication env])
resolves' env@(InfoEnv env' awaitedSignals) resolvers = case signals of
  [] -> (env, [])
  _  -> (InfoEnv env'' $ IdxSet.union awaitedSignals $ IdxSet.fromList' signals, implications)
  where
    signals = [ signal | resolver <- resolvers, InfoSignalResolver (Just signal) <- [infoFor resolver env] ]
    signalsSet = IdxSet.fromList' signals
    implications = map (\idx -> SignalImplication idx (IdxSet.remove idx signalsSet `IdxSet.union` awaitedSignals)) signals
    env'' = foldl' (flip (wupdate (const InfoSignalResolved))) env' signals

await' :: forall kernel env. InfoEnv env -> [Idx env Signal] -> (InfoEnv env, UniformSchedule kernel env -> UniformSchedule kernel env)
await' env@(InfoEnv env' awaitedSignals) signals =
  ( InfoEnv env1' (IdxSet.fromList' allMinimal' `IdxSet.union` awaitedSignals)
  , await allMinimal'
  )
  where
    (allResolved, allMinimal) = foldl' add (IdxSet.empty, IdxSet.empty) signals
    -- We cannot directly convert the IdxSet to a list, as the IdxSet doesn't
    -- provide type information about the memberents and doesn't guarantee that
    -- all members are Signals. By filtering 'signals' we do get that type
    -- safety.
    allMinimal' = filter (`IdxSet.member` allMinimal) signals

    env1' = foldl' (\e (Exists i) -> wupdate setResolved i e) env' $ IdxSet.toList allResolved

    setResolved :: Info env t -> Info env t
    setResolved (InfoSignalImplies _) = InfoSignalResolved
    setResolved info                  = info

    -- Incrementally build a set of signals which we should wait on.
    -- First argument contains a set of resolved signals and the minimal set of
    -- signals from the first k signals (0 <= k < length signals) and the
    -- second argument is the kth signal. This function will add this signal if
    -- it wasn't already implied by the other signals.
    -- Returns a set of resolved signals and the minimal set of signals of the
    -- first (k+1)th signals.
    add :: (IdxSet env, IdxSet env) -> Idx env Signal -> (IdxSet env, IdxSet env)
    add (resolved, minimal) idx
      | InfoSignalInstead instead <- infoFor idx env
        -- Instead of waiting on this signal, we must wait on the given signals
        -- in 'instead'.
        = foldl' add (resolved, minimal) instead
      | InfoSignalResolved <- infoFor idx env
        = (resolved, minimal) -- Was already resolved in the state
      | idx `IdxSet.member` resolved
        = (resolved, minimal) -- Already resolved by a previous signal
      | otherwise
        -- This signal wasn't implied by another signal yet. This signal may
        -- imply signals which were already in 'minimal', so we remove them
        -- here.
        = (resolved `IdxSet.union` reachable, IdxSet.insert idx $ minimal IdxSet.\\ reachable)
      where
        reachable = traverseImplied resolved IdxSet.empty idx

    -- DFS
    traverseImplied :: IdxSet env -> IdxSet env -> Idx env Signal -> IdxSet env
    traverseImplied resolved visited idx
      | idx `IdxSet.member` visited = visited
      | idx `IdxSet.member` resolved = IdxSet.insert idx visited
      | otherwise = foldl' (traverseImplied resolved) (IdxSet.insert idx visited) (findImplications env idx)

findImplications :: InfoEnv env -> Idx env Signal -> [Idx env Signal]
findImplications env idx = case infoFor idx env of
  InfoSignalInstead instead -> instead
  InfoSignalImplies implies -> implies
  _                         -> []

refWrite :: forall env t. InfoEnv env -> Idx env (OutputRef t) -> Idx env t -> InfoEnv env
refWrite env@(InfoEnv env' awaitedSignals) outputRef value
  | InfoRefWrite (Just ref) <- infoFor outputRef env
  = InfoEnv (wupdate (const $ InfoRef $ Just value) ref env') awaitedSignals
refWrite env _ _ = env

refRead :: forall env t. InfoEnv env -> Idx env (Ref t) -> Idx env t -> InfoEnv env
refRead env@(InfoEnv env' awaitedSignals) ref lhs
  -- If we know which value (variable) was written to this ref,
  -- then replace all occurences of the lhs with that variable.
  --
  | InfoRef (Just value) <- infoFor ref env
  = let
      f :: Info env t -> Info env t
      f (InfoScalar tp _) = InfoScalar tp (Just value)
      f (InfoBuffer    _) = InfoBuffer    (Just value)
      f info              = info
    in
      InfoEnv (wupdate f lhs env') awaitedSignals
  -- Otherwise, we store in the environment that this variable
  -- contains the content of this ref. If the program reads from this ref
  -- again, then we can substitute that variable with this one.
  --
  | otherwise
  = InfoEnv (wupdate (const $ InfoRef $ Just lhs) ref env') awaitedSignals

-- Substitutions for scalars and buffers, caused by aliasing through writing to
-- a reference. This substitution doesn't affect signal (resolvers) and
-- (writable) references.
-- This substitution only assures that we use the original declaration instead
-- of the alias. It does not remove the definition of the alias, a later pass
-- should remove that (with a (strongly) live variable analysis).
--
substitute :: InfoEnv env -> env :> env
substitute env = Weaken $ \idx -> case infoFor idx env of
  InfoScalar _ (Just idx') -> idx'
  InfoBuffer   (Just idx') -> idx'
  _                        -> idx

simplifySpawns :: InfoEnv env -> UniformSchedule kernel env -> ([SignalImplication env], UniformSchedule kernel env)
simplifySpawns env schedule
  | SplitTrivials _ k trivial branches'' <- splitTrivials weakenId branches'
  = (signalImplications, trivial $ spawnsGroupCommonAwait k env $ map reorder branches'')
  where
    branches = collectSpawns schedule
    -- Signal implications are only propagated in one direction (namely from
    -- the left branch to the right branch of a Spawn). Schedules must thus be
    -- created in a form where we are most likely to learn information about
    -- signals, i.e. for a let-declaration in PartitionedAcc we must compile
    -- the binding to become the left branch and the body the right branch as
    -- that will allow us to learn something from signals resolved in the
    -- binding and waited on in the body.
    ((_, signalImplications), branches') = mapAccumR simplifyBranch (env1, []) branches

    simplifyBranch
      :: (InfoEnv env, [SignalImplication env])
      -> UniformSchedule kernel env
      -> ((InfoEnv env, [SignalImplication env]), UniformSchedule kernel env)
    simplifyBranch (env2, implications) s = ((env2', implications' ++ implications), s')
      where
        (implications', s') = simplify' env2 s
        env2' = propagate implications' env2

    env1 = foldl' (flip findSignalReplacements) env branches

data SplitTrivials kernel env where
  SplitTrivials
    :: env :> env'
    -> env' :?> env
    -- The trivial part of the start of the schedule
    -> (UniformSchedule kernel env' -> UniformSchedule kernel env)
    -- The remaining parts of the schedule
    -> [UniformSchedule kernel env']
    -> SplitTrivials kernel env

-- Splits a list of schedules in their trivial initial parts and the remainders.
splitTrivials :: env :> env' -> [UniformSchedule kernel env] -> SplitTrivials kernel env'
splitTrivials k (a : as)
  | SplitTrivial  k1 k1' trivial1 remaining1 <- splitTrivial $ weaken' k a
  , SplitTrivials k2 k2' trivial2 remaining2 <- splitTrivials (k1 .> k) as
  = SplitTrivials (k2 .> k1) (k1' <=< k2') (trivial1 . trivial2) (weaken' k2 remaining1 : remaining2)
splitTrivials _ [] = SplitTrivials weakenId Just id []

data SplitTrivial kernel env where
  SplitTrivial
    :: env :> env'
    -> env' :?> env
    -- The trivial part of the start of the schedule
    -> (UniformSchedule kernel env' -> UniformSchedule kernel env)
    -- The remaining part of the schedule
    -> UniformSchedule kernel env'
    -> SplitTrivial kernel env

-- Splits a schedule in its trivial initial part and the remainder.
splitTrivial :: UniformSchedule kernel env -> SplitTrivial kernel env
splitTrivial (Effect effect next)
  | trivialEffect effect
  , SplitTrivial k k' trivial next' <- splitTrivial next
  = SplitTrivial k k' (Effect effect . trivial) next'
splitTrivial (Alet lhs bnd next)
  | trivialBinding bnd
  , SplitTrivial k k' trivial next' <- splitTrivial next
  = SplitTrivial (k .> weakenWithLHS lhs) (strengthenWithLHS lhs <=< k') (Alet lhs bnd . trivial) next'
splitTrivial (Acond condition true false next)
  | trivialSchedule true
  , trivialSchedule false
  , SplitTrivial k k' trivial next' <- splitTrivial next
  = SplitTrivial k k' (Acond condition true false . trivial) next'
splitTrivial schedule
  = SplitTrivial weakenId Just id schedule

collectSpawns :: UniformSchedule kernel env -> [UniformSchedule kernel env]
collectSpawns = (`go` [])
  where
    go :: UniformSchedule kernel env -> [UniformSchedule kernel env] -> [UniformSchedule kernel env]
    go (Spawn s1 s2) = go s2 . go s1
    go u = (u :)

spawnsGroupCommonAwait :: forall kernel env env'. env' :?> env -> InfoEnv env -> [UniformSchedule kernel env'] -> UniformSchedule kernel env'
spawnsGroupCommonAwait k env = serializeDependentSpawns k env . go . map (\b -> let (signals, b') = directlyAwaits1 b in (IdxSet.fromList' signals, b'))
  where
    go :: [(IdxSet env', UniformSchedule kernel env')] -> [UniformSchedule kernel env']
    go [] = []
    go [(_, s)] = [s]
    go branches
      -- No signals found which are awaited by some branches.
      -- Now check if there signals waited by all branches
      | [] <- awaitedByAllList = branches''
      | otherwise = [await awaitedByAllList $ serializeDependentSpawns k env branches'']
      where
        toBranch :: (IdxSet env', UniformSchedule kernel env') -> UniformSchedule kernel env'
        toBranch (set, branch) = await (map toSignal $ IdxSet.toList set) branch

        awaitedByAll :: IdxSet env'
        awaitedByAll = case branches of
          [] -> IdxSet.empty
          ((b,_):bs) -> foldl' (\s (s', _) -> IdxSet.intersect s s') b bs

        -- To get the type information that the indices are indeed signals,
        -- we filter the list of signals of the first branch, instead of using
        -- IdxSet.toList. The latter would not guarantee that the indices are
        -- signals.
        awaitedByAllList :: [Idx env' Signal]
        awaitedByAllList = case branches of
          [] -> []
          ((_, b) : _) -> filter (`IdxSet.member` awaitedByAll) $ fst $ directlyAwaits1 b

        -- Remove the signals which occur in every branch
        branches' :: [(IdxSet env', UniformSchedule kernel env')]
        branches' = map (\(s, b) -> (s IdxSet.\\ awaitedByAll, b)) branches

        -- Now we try to group branches, by checking if a signal occurs in some
        -- (at least 2) but not all branches.
        counts = mconcat $ map (CountEnv.fromIdxSet . fst) branches'

        -- Maximum number of branches in which a common signal occurs
        commonCount = CountEnv.maxCount counts

        -- Signal which occurs in the most number of branches
        commonSignal =  IdxSet.first $ CountEnv.findWithCount counts commonCount

        branches'' :: [UniformSchedule kernel env']
        branches''
          | False -- @IVO???
          , commonCount >= 2
          , Just (Exists signal) <- commonSignal
          , False
          -- common is the list of branches which wait on this signal, and
          -- uncommon is the list of branches which do not wait on the signal.
          , (common, uncommon) <- partition (\(s, _) -> signal `IdxSet.member` s) branches'
          , common' <- map (first (IdxSet.remove signal)) common
          = go uncommon ++ [await [toSignal $ Exists signal] $ serializeDependentSpawns k env $ go common']

          | otherwise
          -- No signals found which are awaited by some branches.
          -- Now check if there signals waited by all branches
          = map toBranch branches'

        toSignal :: Exists (Idx env') -> Idx env' Signal
        toSignal (Exists idx)
          | Just idx' <- k idx = case infoFor idx' env of
            InfoSignalImplies _ -> idx
            InfoSignalInstead _ -> idx
            InfoSignalResolved  -> idx
            _                   -> internalError "Expected this index to point to a Signal"
        toSignal _ = internalError "Expected this index to point to a Signal"

-- Returns the set of indices of signal resolvers (not signals) which are
-- resolved at the end of this schedule.
resolvesAtEnd :: UniformSchedule kernel env -> IdxSet env
resolvesAtEnd (Effect (SignalResolve resolvers) Return)
                                  = IdxSet.fromList' resolvers
resolvesAtEnd Return              = IdxSet.empty
resolvesAtEnd (Alet lhs _ next)   = IdxSet.drop' lhs $ resolvesAtEnd next
resolvesAtEnd (Effect _ next)     = resolvesAtEnd next
resolvesAtEnd (Acond _ _ _ next)  = resolvesAtEnd next
resolvesAtEnd (Awhile _ _ _ next) = resolvesAtEnd next
-- In a Spawn, we traverse only the right subterm. This matches with the
-- inlining done in 'serial'.
resolvesAtEnd (Spawn _ next)      = resolvesAtEnd next

serializeDependentSpawns :: forall kernel env env'. env' :?> env -> InfoEnv env -> [UniformSchedule kernel env'] -> UniformSchedule kernel env'
serializeDependentSpawns k env branches = go branches []
  where
    -- Takes a list of branches which are not processed yet and a list of
    -- already processed branches. We still need to have access to the
    -- processed branches as they still may be serialized with another
    -- branch.
    go :: [UniformSchedule kernel env'] -> [UniformSchedule kernel env'] -> UniformSchedule kernel env'
    go []     accum = spawns $ reverse accum -- Accumulator was in reverse order.
    go (a:as) accum
      | [] <- signals     = go as  (a  : accum)
      | [] <- successors
      , [] <- successors' = go as  (a  : accum)
      | otherwise         = go as' (a' : accum')
      where
        resolvesSet = resolvesAtEnd a
        signals = sort $ mapMaybe findSignal $ IdxSet.toList resolvesSet
        (successors, as') = partition directlyFollows as
        (successors', accum') = partition directlyFollows accum

        a' = serial [a, go successors successors']

        findSignal :: Exists (Idx env') -> Maybe (Idx env Signal)
        findSignal (Exists idx')
          | Just idx <- k idx'
          , InfoSignalResolver msignal <- infoFor idx env
          = msignal
        findSignal _ = Nothing

        directlyFollows :: UniformSchedule kernel env' -> Bool
        directlyFollows other = signals `isSubsequenceOf` sort (mapMaybe k otherSignals)
          where
            otherSignals = fst $ directlyAwaits1 other

-- Utilities

-- Forks the two schedules, unless the second schedule directly awaits on all the signals in the given list.
-- In such case, we try to execute them serial.
spawnUnless :: UniformSchedule kernel fenv -> UniformSchedule kernel fenv -> Maybe [Idx fenv Signal] -> UniformSchedule kernel fenv
spawnUnless Return s      _      = s
spawnUnless s      Return _      = s
spawnUnless s1     s2     awaits
  | Just awaits' <- awaits
  , sort awaits' `isSubsequenceOf` sort signals2''
    = await intersection $ serial [await signals1'' s1', await signals2'' s2']
  | trivialSchedule s1'
    = await intersection $ serial [await signals1'' s1', await signals2'' s2']
  | trivialSchedule s2'
    = await intersection $ serial [await signals1'' s2', await signals2'' s1']
  | otherwise
    = await intersection $ Spawn (await signals1'' s1') (await signals2'' s2')
  where
    (signals1, s1') = directlyAwaits1 $ reorder s1
    signals1' = nub signals1
    signals1'' = signals1' \\ intersection
    (signals2, s2') = directlyAwaits1 $ reorder s2
    signals2' = nub signals2
    signals2'' = signals2' \\ intersection
    intersection = signals1' `List.intersect` signals2'

spawn :: UniformSchedule kernel fenv -> UniformSchedule kernel fenv -> UniformSchedule kernel fenv
spawn s1 s2 = spawnUnless s1 s2 Nothing

spawns :: [UniformSchedule kernel fenv] -> UniformSchedule kernel fenv
spawns = spawns' . filter notReturn
  where
    notReturn Return = False
    notReturn _ = True

spawns' :: [UniformSchedule kernel fenv] -> UniformSchedule kernel fenv
spawns' [] = Return
spawns' [u] = u
spawns' (u:us) = Spawn u (spawns' us)

serial :: forall kernel fenv. [UniformSchedule kernel fenv] -> UniformSchedule kernel fenv
serial = go weakenId
  where
    go :: forall fenv1. fenv :> fenv1 -> [UniformSchedule kernel fenv] -> UniformSchedule kernel fenv1
    go _  [] = Return
    go k1 (u:us) = trav k1 (weaken' k1 u)
      where
        trav :: forall fenv'. fenv :> fenv' -> UniformSchedule kernel fenv' -> UniformSchedule kernel fenv'
        trav k = \case
          Return -> go k us
          Alet lhs bnd u' -> Alet lhs bnd $ trav (weakenWithLHS lhs .> k) u'
          Effect effect u' -> Effect effect $ trav k u'
          Acond cond true false u' -> Acond cond true false $ trav k u'
          Awhile io f input u' -> Awhile io f input $ trav k u'
          Spawn u' u'' -> Spawn u' (trav k u'')

bindExp
    :: BLeftHandSide bnd env env'
    -> Exp env bnd
    -> UniformSchedule kernel env'
    -> UniformSchedule kernel env
bindExp lhs bnd next =
  case lhs of
    LeftHandSideWildcard{} -> next
    LeftHandSideSingle{}   -> Alet lhs (Compute bnd) next
    LeftHandSidePair l1 l2 ->
      case bnd of
        Pair e1 e2 -> bindExp l1 e1
                    $ bindExp l2 (weakenArrayInstr (weakenWithLHS l1) e2) next
        _          -> Alet lhs (Compute bnd) next

-- TODO: Move fork combining and/or InfoEnv into this utility?
data BuildSchedule kernel env =
  BuildSchedule{
    -- Sorted, without duplicates
    directlyAwaits :: [Idx env Signal],
    trivial :: Bool,
    -- Constructs a schedule, but doesn't wait on the directlyAwaits signals.
    -- constructFull adds that.
    construct
      :: forall env'.
         env :> env'
      -> BuildEnv env'
      -> Continuation kernel env'
      -> UniformSchedule kernel env'
  }

data BuildEnv env =
  BuildEnv{
    buildEnvResolved :: IdxSet env -- Set of resolved signals
  }

instance Sink' (BuildSchedule kernel) where
  weaken' k schedule =
    BuildSchedule{
      directlyAwaits = sort $ map (weaken k) $ directlyAwaits schedule,
      trivial = trivial schedule,
      construct = \k' -> construct schedule (k' .> k)
    }

newtype BuildScheduleFun kernel env t =
  BuildScheduleFun{
    funConstruct
      :: forall env'.
         env :> env'
      -> UniformScheduleFun kernel env' t
  }

-- Constructs a schedule, and waits on the directlyAwaits signals.
constructFull
  :: BuildSchedule kernel env
  -> env :> env'
  -> BuildEnv env'
  -> Continuation kernel env'
  -> UniformSchedule kernel env'
constructFull schedule k env cont
  | null $ directlyAwaits schedule = construct schedule k env cont
  | signals' <-
    -- Don't wait on already resolved signals
    filter (\idx -> not (idx `IdxSet.member` buildEnvResolved env))
      $ map (weaken k)
      $ directlyAwaits schedule
  , env' <- BuildEnv $ IdxSet.union (IdxSet.fromList' signals') $ buildEnvResolved env
    = (if null signals' then id else Effect $ SignalAwait signals')
      $ construct schedule k env' cont

data Continuation kernel env where
  ContinuationEnd
    :: Continuation kernel env

  ContinuationDo
    :: env1 :> env
    -> BuildSchedule kernel env1
    -> env2 :> env
    -> Continuation kernel env2
    -> Continuation kernel env

instance Sink' (Continuation kernel) where
  weaken' _ ContinuationEnd = ContinuationEnd
  weaken' k1 (ContinuationDo k2 b k3 c) = ContinuationDo (k1 .> k2) b (k1 .> k3) c

buildReturn :: BuildSchedule kernel env
buildReturn = BuildSchedule{
    directlyAwaits = [],
    trivial = True,
    construct = \_ env -> \case
      ContinuationEnd -> Return
      ContinuationDo k2 build k3 cont -> constructFull build k2 env $ weaken' k3 cont
  }

buildLet
  :: forall kernel t env1 env2.
     BLeftHandSide t env1 env2
  -> Binding env1 t
  -> BuildSchedule kernel env2
  -> BuildSchedule kernel env1
buildLet lhs binding body
  | trivialBinding binding || null (directlyAwaits body) =
    BuildSchedule{
      directlyAwaits = map (fromMaybe (internalError "Illegal schedule: deadlock") . strengthenWithLHS lhs) $ directlyAwaits body,
      trivial = trivialBinding binding && trivial body,
      construct = constructLet False
    }
  | otherwise =
    BuildSchedule{
      directlyAwaits = [],
      trivial = False,
      construct = constructLet True
    }
  where
    constructLet
      :: Bool
      -> env1 :> env1'
      -> BuildEnv env1'
      -> Continuation kernel env1'
      -> UniformSchedule kernel env1'
    constructLet shouldAwait k env cont
      | Exists lhs' <- rebuildLHS lhs
      , k' <- sinkWithLHS lhs lhs' k
      , binding' <- weaken k binding =
        Alet lhs' binding'
          $ constructFull (if shouldAwait then body else body{ directlyAwaits = [] }) k'
            (buildEnvExtend lhs' binding' env)
          $ weaken' (weakenWithLHS lhs') cont

buildEnvExtend :: BLeftHandSide t env1 env2 -> Binding env1 t -> BuildEnv env1 -> BuildEnv env2
buildEnvExtend lhs _ (BuildEnv resolved) = BuildEnv $ IdxSet.skip' lhs resolved

buildEffect
  :: Effect kernel env
  -> BuildSchedule kernel env
  -> BuildSchedule kernel env
buildEffect (SignalResolve []) next = next
buildEffect (SignalAwait signals) next =
  BuildSchedule{
    directlyAwaits = sort signals `mergeDedup` directlyAwaits next,
    trivial = trivial next,
    construct = construct next
  }
buildEffect effect next
  | canPostpone || null (directlyAwaits next) =
    BuildSchedule{
      directlyAwaits = directlyAwaits next,
      trivial = trivialEffect effect && trivial next,
      construct = \k env cont ->
        Effect (weaken' k effect)
          $ construct next k env cont
    }
  | otherwise =
    BuildSchedule{
      directlyAwaits = [],
      trivial = False,
      construct = \k env cont ->
        Effect (weaken' k effect)
          $ constructFull next k env cont
    }
  where
    -- Write may be postponed: a write doesn't do synchronisation,
    -- that is done by a signal(resolver).
    canPostpone
      | RefWrite{} <- effect = True
      | otherwise = False

buildSeq :: BuildSchedule kernel env -> BuildSchedule kernel env -> BuildSchedule kernel env
buildSeq a b =
  BuildSchedule {
    directlyAwaits = directlyAwaits a,
    trivial = trivial a && trivial b && directlyAwaits b `isSubsequenceOf` directlyAwaits a,
    construct = \k env cont ->
      construct a k env $ ContinuationDo k b weakenId cont
  }

buildSpawn :: BuildSchedule kernel env -> BuildSchedule kernel env -> BuildSchedule kernel env
buildSpawn a b
  | trivial a && directlyAwaits a `isSubsequenceOf` directlyAwaits b =
    buildSeq a b
  | trivial b && directlyAwaits b `isSubsequenceOf` directlyAwaits a =
    buildSeq b a
  | otherwise =
    BuildSchedule{
      directlyAwaits = directlyAwaits a `sortedIntersection` directlyAwaits b,
      trivial = False,
      construct = \k env cont ->
        Spawn
          (constructFull a{directlyAwaits = directlyAwaits a `sortedMinus` directlyAwaits b} k env cont)
          (constructFull b{directlyAwaits = directlyAwaits b `sortedMinus` directlyAwaits a} k env ContinuationEnd)
    }

buildAcond
  :: ExpVar env PrimBool
  -> BuildSchedule kernel env -- True branch
  -> BuildSchedule kernel env -- False branch
  -> BuildSchedule kernel env -- Operations after the if-then-else
  -> BuildSchedule kernel env
buildAcond var true false next =
  BuildSchedule{
    directlyAwaits = directlyAwaits true `sortedIntersection` directlyAwaits false,
    trivial = False,
    construct = \k env cont -> Acond
      (weaken k var)
      (constructFull  true{directlyAwaits = directlyAwaits true `sortedMinus` directlyAwaits false} k env ContinuationEnd)
      (constructFull false{directlyAwaits = directlyAwaits false `sortedMinus` directlyAwaits true} k env ContinuationEnd)
      (constructFull next k env cont)
  }

buildAwhile
  :: InputOutputR input output
  -> BuildScheduleFun kernel env (input -> Output PrimBool -> output -> ())
  -> BaseVars env input
  -> BuildSchedule kernel env -- Operations after the while loop
  -> BuildSchedule kernel env
buildAwhile io step initial next =
  BuildSchedule{
    directlyAwaits = [], -- TODO: Compute this based on the use of the initial state and free variables of step.
    trivial = False,
    construct = \k env cont -> Awhile
      io
      (funConstruct step k)
      (mapTupR (weaken k) initial)
      (constructFull next k env cont)
  }

buildFunLam
  :: BLeftHandSide t env1 env2
  -> BuildScheduleFun kernel env2 f
  -> BuildScheduleFun kernel env1 (t -> f)
buildFunLam lhs body =
  BuildScheduleFun{
    funConstruct = \k -> case rebuildLHS lhs of
      Exists lhs' -> Slam lhs' $ funConstruct body (sinkWithLHS lhs lhs' k)
  }

buildFunBody :: BuildSchedule kernel env -> BuildScheduleFun kernel env ()
buildFunBody body =
  BuildScheduleFun{
    funConstruct = \k -> Sbody $ constructFull body k (BuildEnv IdxSet.empty) ContinuationEnd
  }

-- Assumes that the input arrays are sorted,
-- with no duplicates.
-- Creates a sorted list containing all elements of the two input list.
-- If an element is present in both input lists, it will be added only
-- once to the output.
mergeDedup :: Ord a => [a] -> [a] -> [a]
mergeDedup as@(a:as') bs@(b:bs')
  | a == b    = a : mergeDedup as' bs'
  | a <  b    = a : mergeDedup as' bs
  | otherwise = b : mergeDedup as  bs'
mergeDedup as [] = as
mergeDedup [] bs = bs

-- Constructs the intersection of two lists,
-- assuming they are sorted and have no duplicates.
sortedIntersection :: Ord a => [a] -> [a] -> [a]
sortedIntersection as@(a:as') bs@(b:bs')
  | a == b    = a : sortedIntersection as' bs'
  | a <  b    = sortedIntersection as' bs
  | otherwise = sortedIntersection as  bs'
sortedIntersection _ _ = []

-- Constructs the difference of two lists,
-- assuming they are sorted and have no duplicates.
-- It returns all elements present in the first list,
-- but not in the second
sortedMinus :: Ord a => [a] -> [a] -> [a]
sortedMinus as@(a:as') bs@(b:bs')
  | a == b    = sortedMinus as' bs'
  | a <  b    = a : sortedMinus as' bs
  | otherwise = sortedMinus as  bs'
sortedMinus as [] = as
sortedMinus [] _  = []
