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
  forkUnless, fork, forks, serial,
) where

import Data.Array.Accelerate.Analysis.Match
import Data.Array.Accelerate.AST.Environment
import Data.Array.Accelerate.AST.Idx
import Data.Array.Accelerate.AST.IdxSet (IdxSet)
import qualified Data.Array.Accelerate.AST.IdxSet           as IdxSet
import Data.Array.Accelerate.AST.CountEnv (CountEnv)
import qualified Data.Array.Accelerate.AST.CountEnv         as CountEnv
import Data.Array.Accelerate.AST.LeftHandSide
import Data.Array.Accelerate.AST.Kernel
import Data.Array.Accelerate.AST.Schedule
import Data.Array.Accelerate.AST.Schedule.Uniform
import Data.Array.Accelerate.AST.Var
import Data.Array.Accelerate.Error
import Data.Array.Accelerate.Representation.Array
import Data.Array.Accelerate.Representation.Shape
import Data.Array.Accelerate.Representation.Type
import Data.Array.Accelerate.Trafo.Exp.Simplify             ( simplifyExp )
import Data.Array.Accelerate.Trafo.Exp.Substitution
import Data.Array.Accelerate.Trafo.Operation.Substitution   ( strengthenArrayInstr, weakenArrayInstr )
import Data.Array.Accelerate.Trafo.Substitution             hiding ( weakenArrayInstr )
import Data.Array.Accelerate.Trafo.Var
import Data.Array.Accelerate.Trafo.WeakenedEnvironment
import Data.Array.Accelerate.Trafo.Schedule.Uniform.Substitution
import Data.Array.Accelerate.Type
import Data.Kind
import Data.Maybe
import Data.List
import qualified Data.List as List
import Control.Monad
import Control.DeepSeq
import qualified Data.Array.Accelerate.AST.Environment as Env


import Data.Array.Accelerate.Pretty.Operation

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
-- Forks
simplify' env s@Fork{} = simplifyForks env s
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
simplifyEffect env (Exec kernel args) = ([], env, Effect $ Exec kernel $ mapArgs (weaken $ substitute env) args)
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
    go (LeftHandSidePair l1 l2) env1
      | env2 <- go l1 env1
      = go l2 env2

bindingEnv :: BLeftHandSide t env env' -> Binding env t -> InfoEnv env -> InfoEnv env'
bindingEnv lhs@(LeftHandSideSingle _) (RefRead ref) env = refRead (bindEnv lhs env) (weaken (weakenSucc weakenId) $ varIdx ref) ZeroIdx
bindingEnv (LeftHandSideSingle _ `LeftHandSidePair` LeftHandSideSingle _) NewSignal (InfoEnv env awaitedSignals)
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
propagate implications infoEnv@(InfoEnv env awaitedSignals) = (InfoEnv (foldl' add env implications) awaitedSignals)
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
    env'' = foldl' (\e idx -> wupdate (const InfoSignalResolved) idx e) env' signals

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

simplifyForks :: InfoEnv env -> UniformSchedule kernel env -> ([SignalImplication env], UniformSchedule kernel env)
simplifyForks env schedule
  | SplitTrivials _ k trivial branches'' <- splitTrivials weakenId branches'
  = (signalImplications, trivial $ forksGroupCommonAwait k env $ map reorder branches'')
  where
    branches = collectForks schedule
    -- Signal implications are only propagated in one direction (namely from
    -- the left branch to the right branch of a Fork). Schedules must thus be
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

collectForks :: UniformSchedule kernel env -> [UniformSchedule kernel env]
collectForks = (`go` [])
  where
    go :: UniformSchedule kernel env -> [UniformSchedule kernel env] -> [UniformSchedule kernel env]
    go (Fork s1 s2) = go s2 . go s1
    go u = (u :)

forksGroupCommonAwait :: forall kernel env env'. env' :?> env -> InfoEnv env -> [UniformSchedule kernel env'] -> UniformSchedule kernel env'
forksGroupCommonAwait k env = serializeDependentForks k env . go . map (\b -> let (signals, b') = directlyAwaits b in (IdxSet.fromList' signals, b'))
  where
    go :: [(IdxSet env', UniformSchedule kernel env')] -> [UniformSchedule kernel env']
    go [] = []
    go [(_, s)] = [s]
    go branches
      -- No signals found which are awaited by some branches.
      -- Now check if there signals waited by all branches
      | [] <- awaitedByAllList = branches''
      | otherwise = [await awaitedByAllList $ serializeDependentForks k env branches'']
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
          ((_, b) : _) -> filter (`IdxSet.member` awaitedByAll) $ fst $ directlyAwaits b

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
          | False
          , commonCount >= 2
          , Just (Exists signal) <- commonSignal
          , False
          -- common is the list of branches which wait on this signal, and
          -- uncommon is the list of branches which do not wait on the signal.
          , (common, uncommon) <- partition (\(s, _) -> signal `IdxSet.member` s) branches'
          , common' <- map (\(s, b) -> (IdxSet.remove signal s, b)) common
          = go uncommon ++ [await [toSignal $ Exists signal] $ serializeDependentForks k env $ go common']
          
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
-- In a Fork, we traverse only the left subterm. This matches with the
-- inlining done in 'serial'.
resolvesAtEnd (Fork next _)       = resolvesAtEnd next

serializeDependentForks :: forall kernel env env'. env' :?> env -> InfoEnv env -> [UniformSchedule kernel env'] -> UniformSchedule kernel env'
serializeDependentForks k env branches = go branches []
  where
    -- Takes a list of branches which are not processed yet and a list of
    -- already processed branches. We still need to have access to the
    -- processed branches as they still may be serialized with another
    -- branch.
    go :: [UniformSchedule kernel env'] -> [UniformSchedule kernel env'] -> UniformSchedule kernel env'
    go []     accum = forks $ reverse accum -- Accumulator was in reverse order.
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
            otherSignals = fst $ directlyAwaits other

-- Utilities

-- Forks the two schedules, unless the second schedule directly awaits on all the signals in the given list.
-- In such case, we try to execute them serial.
forkUnless :: UniformSchedule kernel fenv -> UniformSchedule kernel fenv -> Maybe [Idx fenv Signal] -> UniformSchedule kernel fenv
forkUnless Return s      _      = s
forkUnless s      Return _      = s
forkUnless s1     s2     awaits
  | Just awaits' <- awaits
  , sort awaits' `isSubsequenceOf` sort signals2''
    = await intersection $ serial [await signals1'' s1', await signals2'' s2']
  | trivialSchedule s1'
    = await intersection $ serial [await signals1'' s1', await signals2'' s2']
  | trivialSchedule s2'
    = await intersection $ serial [await signals1'' s2', await signals2'' s1']
  | otherwise
    = await intersection $ Fork (await signals1'' s1') (await signals2'' s2')
  where
    (signals1, s1') = directlyAwaits $ reorder s1
    signals1' = nub signals1
    signals1'' = signals1' \\ intersection
    (signals2, s2') = directlyAwaits $ reorder s2
    signals2' = nub signals2
    signals2'' = signals2' \\ intersection
    intersection = List.intersect signals1' signals2'

fork :: UniformSchedule kernel fenv -> UniformSchedule kernel fenv -> UniformSchedule kernel fenv
fork s1 s2 = forkUnless s1 s2 Nothing

forks :: [UniformSchedule kernel fenv] -> UniformSchedule kernel fenv
forks = forks' . filter notReturn
  where
    notReturn Return = False
    notReturn _ = True

forks' :: [UniformSchedule kernel fenv] -> UniformSchedule kernel fenv
forks' [] = Return
forks' [u] = u
forks' (u:us) = Fork (forks' us) u

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
          Fork u' u'' -> Fork (trav k u') u''

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

