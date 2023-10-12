{-# LANGUAGE ConstraintKinds     #-}
{-# LANGUAGE FlexibleInstances   #-}
{-# LANGUAGE GADTs               #-}
{-# LANGUAGE KindSignatures      #-}
{-# LANGUAGE LambdaCase          #-}
{-# LANGUAGE MultiWayIf          #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE PatternGuards       #-}
{-# LANGUAGE PatternSynonyms     #-}
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
-- Module      : Data.Array.Accelerate.Trafo.Schedule.Uniform.Future
-- Copyright   : [2012..2020] The Accelerate Team
-- License     : BSD3
--
-- Maintainer  : Trevor L. McDonell <trevor.mcdonell@gmail.com>
-- Stability   : experimental
-- Portability : non-portable (GHC extensions)
--

module Data.Array.Accelerate.Trafo.Schedule.Uniform.Future (
  Future(..), FutureEnv(..), Lock(..), pattern Move, pattern Borrow,
  withRef, buildRead, weakenEither,
  fprj, fenvDrop, fenvDrop1, fenvFSkipMany, fenvPushLHS,
  chainFuture, ChainFuture(..), chainFutureEnvironmentSeqIf, chainFutureEnvironment, ChainFutureEnv(..),
  subFutureEnvironment, restrictEnvForLHS,
  MaybeSignal, MaybeSignalResolver, buildAwait,
  lhsSignal, lhsRef,
) where


import Data.Array.Accelerate.Analysis.Match
import Data.Array.Accelerate.AST.Environment
import Data.Array.Accelerate.AST.Idx
import Data.Array.Accelerate.AST.IdxSet (IdxSet(..))
import qualified Data.Array.Accelerate.AST.IdxSet           as IdxSet
import Data.Array.Accelerate.AST.LeftHandSide
import Data.Array.Accelerate.AST.Kernel
import Data.Array.Accelerate.AST.Schedule
import Data.Array.Accelerate.AST.Schedule.Uniform hiding ( directlyAwaits )
import Data.Array.Accelerate.AST.Var
import Data.Array.Accelerate.Error
import Data.Array.Accelerate.Representation.Array
import Data.Array.Accelerate.Representation.Ground
import Data.Array.Accelerate.Representation.Shape
import Data.Array.Accelerate.Representation.Type
import Data.Array.Accelerate.Trafo.Exp.Substitution
import Data.Array.Accelerate.Trafo.Operation.Substitution   (strengthenArrayInstr)
import Data.Array.Accelerate.Trafo.Substitution
import Data.Array.Accelerate.Trafo.Var
import Data.Array.Accelerate.Trafo.Schedule.Partial
import Data.Array.Accelerate.Trafo.Schedule.Uniform.LiveVars
import Data.Array.Accelerate.Trafo.Schedule.Uniform.Simplify
import Data.Array.Accelerate.Trafo.Schedule.Uniform.Substitution
import Data.Array.Accelerate.Trafo.SkipEnvironment (Skip'(..), lhsSkip')
import Data.Array.Accelerate.Type
import Data.Array.Accelerate.AST.Partitioned (PartitionedAcc, PartitionedAfun)
import qualified Data.Array.Accelerate.AST.Partitioned as C
import Data.Kind
import Data.Maybe
import Data.String
import Formatting hiding (left, right)
import Data.List
    ( groupBy, nubBy, sort, group, (\\), isSubsequenceOf )
import Prelude hiding (id, (.), read)
import Control.Category
import Control.DeepSeq
import qualified Data.Array.Accelerate.AST.Environment as Env
import Control.Concurrent
import Data.IORef
import System.IO.Unsafe (unsafePerformIO)

import Data.Array.Accelerate.Pretty.Operation
import Data.Functor.Identity

data Future fenv t where
  FutureScalar :: ScalarType t
               -> MaybeSignal fenv
               -> Either (Idx fenv t) (Idx fenv (Ref t))
               -> Future fenv t

  -- A buffer has signals and resolvers grouped in Locks to synchronize
  -- read and write access to the buffer.
  -- The Ref may be read when the read signal is resolved.
  -- Informal properties / invariants:
  --  - If the read signal is resolved, then we may read from
  --    the array.
  --  - If the signals of the read and write access are both
  --    resolved, then we may destructively update the array.
  --  - The read resolver may only be resolved after the read
  --    signal is resolved.
  --  - The write resolver may only be resolved after both
  --    the read and write signals are resolved.
  --  - If the write lock is move, then the read lock should also be move.
  --    (See datatype Lock for the meaning of move and borrow)
  FutureBuffer :: ScalarType t
               -> Either (Idx fenv (Buffer t)) (Idx fenv (Ref (Buffer t)))
               -> Lock fenv -- Read access
               -> Maybe (Lock fenv) -- Write access, if needed
               -> Future fenv (Buffer t)

withRef
  :: forall kernel fenv t.
     GroundR t
  -> Either (Idx fenv t) (Idx fenv (Ref t))
  -> (forall fenv'. Skip fenv' fenv -> BaseVar fenv' t -> BuildSchedule kernel fenv')
  -> BuildSchedule kernel fenv
withRef tp (Left idx) f = f @fenv SkipNone $ Var (BaseRground tp) idx
withRef tp (Right ref) f =
  buildLet (LeftHandSideSingle $ BaseRground tp) (RefRead (Var (BaseRref tp) ref))
  $ f @(fenv, t) (SkipSucc SkipNone) $ Var (BaseRground tp) ZeroIdx

buildRead :: GroundR t -> Idx fenv (Ref t) -> BuildSchedule kernel (fenv, t) -> BuildSchedule kernel fenv
buildRead tp ref = buildLet
  (LeftHandSideSingle $ BaseRground tp)
  (RefRead $ Var (BaseRref tp) ref)

-- We call a lock with a resolver a borrow lock, and one without a move lock.
data Lock fenv =
  Lock {
    lockSignal :: MaybeSignal fenv,
    lockResolver :: MaybeSignalResolver fenv
  }

pattern Borrow :: MaybeSignal fenv -> Idx fenv SignalResolver -> Lock fenv
pattern Borrow signal resolver = Lock signal (Just resolver)
pattern Move :: MaybeSignal fenv -> Lock fenv
pattern Move signal = Lock signal Nothing
{-# COMPLETE Borrow, Move #-}

instance Sink' Lock where
  weaken' k (Lock s r) = Lock (weaken k <$> s) (weaken k <$> r)

instance Sink Future where
  weaken k (FutureScalar tp signal ref) = FutureScalar tp (weaken k <$> signal) (weakenEither k ref)
  weaken k (FutureBuffer tp ref read write)
    = FutureBuffer
        tp
        (weakenEither k ref)
        (weaken' k read)
        (weaken' k <$> write)

weakenEither :: (Sink a, Sink b) => env :> env' -> Either (a env t) (b env s) -> Either (a env' t) (b env' s)
weakenEither k (Left a) = Left $ weaken k a
weakenEither k (Right b) = Right $ weaken k b

data FutureEnv fenv genv where
  FEnvEnd
    :: FutureEnv fenv genv
  FEnvFSkip
    :: FutureEnv fenv genv -> FutureEnv (fenv, t) genv
  FEnvGSkip
    :: FutureEnv fenv genv -> FutureEnv fenv (genv, t)
  FEnvPush
    :: FutureEnv fenv genv
    -> Future fenv t
    -> FutureEnv fenv (genv, t)

fprj :: forall fenv genv t. Idx genv t -> FutureEnv fenv genv -> Maybe (Future fenv t)
fprj = \idx env -> go idx env SkipNone
  where
    go :: Idx genv' t -> FutureEnv fenv' genv' -> Skip fenv fenv' -> Maybe (Future fenv t)
    go idx           (FEnvFSkip env)     skip = go idx env (SkipSucc skip)
    go ZeroIdx       (FEnvPush _ future) skip = Just $ weaken (skipWeakenIdx skip) future
    go (SuccIdx idx) (FEnvPush env _)    skip = go idx env skip
    go (SuccIdx idx) (FEnvGSkip env)     skip = go idx env skip
    go _             _                   _    = Nothing

fenvDrop :: Skip genv genv' -> FutureEnv fenv genv -> FutureEnv fenv genv'
fenvDrop SkipNone env = env
fenvDrop (SkipSucc skip) env = fenvDrop1 $ fenvDrop skip env

fenvDrop1 :: FutureEnv fenv (genv', t) -> FutureEnv fenv genv'
fenvDrop1 (FEnvFSkip env) = FEnvFSkip $ fenvDrop1 env
fenvDrop1 (FEnvGSkip env) = env
fenvDrop1 (FEnvPush env _) = env
fenvDrop1 FEnvEnd = FEnvEnd

fenvFSkipMany :: Skip fenv' fenv -> FutureEnv fenv genv -> FutureEnv fenv' genv
fenvFSkipMany (SkipSucc skip) env = fenvFSkipMany skip $ FEnvFSkip env
fenvFSkipMany SkipNone env = env

fenvGSkip :: FutureEnv fenv genv -> FutureEnv fenv (genv, t)
fenvGSkip FEnvEnd = FEnvEnd
fenvGSkip env = FEnvGSkip env

fenvWeakenF :: Skip fenv' fenv -> FutureEnv fenv genv -> FutureEnv fenv' genv
fenvWeakenF SkipNone env = env
fenvWeakenF (SkipSucc skip) env = fenvWeakenF skip (FEnvFSkip env)

fRemoveBuffers :: FutureEnv fenv genv -> FutureEnv fenv genv
fRemoveBuffers FEnvEnd = FEnvEnd
fRemoveBuffers (FEnvFSkip env) = FEnvFSkip $ fRemoveBuffers env
fRemoveBuffers (FEnvGSkip env) = FEnvGSkip $ fRemoveBuffers env
fRemoveBuffers (FEnvPush env FutureBuffer{}) = FEnvGSkip env
fRemoveBuffers (FEnvPush env future) = FEnvPush (fRemoveBuffers env) future

-- Assumes that both left-hand-sides have the same shape.
fenvPushLHS :: GLeftHandSide t genv genv' -> GLeftHandSide t fenv fenv' -> Uniquenesses t -> FutureEnv fenv genv -> FutureEnv fenv' genv'
fenvPushLHS (LeftHandSideSingle (GroundRscalar tp)) (LeftHandSideSingle _) _ env =
  FEnvFSkip env `FEnvPush` FutureScalar tp Nothing (Left ZeroIdx)
fenvPushLHS (LeftHandSideSingle (GroundRbuffer tp)) (LeftHandSideSingle _) (TupRsingle Unique) env =
  FEnvFSkip env `FEnvPush` FutureBuffer tp (Left ZeroIdx) (Move Nothing) (Just $ Move Nothing)
fenvPushLHS (LeftHandSideSingle (GroundRbuffer tp)) (LeftHandSideSingle _) _ env =
  FEnvFSkip env `FEnvPush` FutureBuffer tp (Left ZeroIdx) (Move Nothing) Nothing
fenvPushLHS (LeftHandSideWildcard _) (LeftHandSideWildcard _) _ env = env
fenvPushLHS (LeftHandSidePair lhs1 lhs2) (LeftHandSidePair lhs1' lhs2') us env
  | (us1, us2) <- pairUniqueness us
  = fenvPushLHS lhs2 lhs2' us2 $ fenvPushLHS lhs1 lhs1' us1 env
fenvPushLHS _ _ _ _ = internalError "LHS mismatch: expected two left hand sides of the same shape"

-- TODO: Separate chainFuture(Env) for sequential let bindings?
-- And possibly another for sequential let bindings, where the binding guaranteed does not introduce forks?

-- Data type for the existentially qualified type variable fenv' used in chainFuture
data ChainFutureEnv kernel fenv genv where
  ChainFutureEnv
    :: (BuildSchedule kernel fenv' -> BuildSchedule kernel fenv)
    -> Skip fenv' fenv
    -> FutureEnv fenv' genv
    -> FutureEnv fenv' genv
    -> ChainFutureEnv kernel fenv genv

chainFutureEnvironmentSeqIf :: Bool -> FutureEnv fenv genv -> SyncEnv genv -> SyncEnv genv -> ChainFutureEnv kernel fenv genv
chainFutureEnvironmentSeqIf True env left right
  | (left', right') <- seqChainFutureEnv env left right
  = ChainFutureEnv id SkipNone left' right'
chainFutureEnvironmentSeqIf False env left right = chainFutureEnvironment SkipNone env left right

chainFutureEnvironment :: Skip fenv' fenv -> FutureEnv fenv genv -> SyncEnv genv -> SyncEnv genv -> ChainFutureEnv kernel fenv' genv
-- If left SyncEnv is empty, no further synchronisations are necessary. We do still have to pass scalars to the left environment.
chainFutureEnvironment skip env PEnd _ = ChainFutureEnv id SkipNone (fRemoveBuffers env') env'
  where env' = fenvWeakenF skip env
-- Same, but now for the right subterm.
chainFutureEnvironment skip env _ PEnd  = ChainFutureEnv id SkipNone env' (fRemoveBuffers env')
  where env' = fenvWeakenF skip env
chainFutureEnvironment skip (FEnvFSkip env) senvLeft senvRight = chainFutureEnvironment (SkipSucc skip) env senvLeft senvRight
-- Scalars don't require further synchronisation
chainFutureEnvironment skip (FEnvPush fenv f@FutureScalar{}) senvLeft senvRight
  | ChainFutureEnv instr skip1 fenvLeft fenvRight <- chainFutureEnvironment skip fenv (partialEnvTail senvLeft) (partialEnvTail senvRight)
  , f' <- weaken (skipWeakenIdx skip1) $ weaken (skipWeakenIdx skip) f
  = ChainFutureEnv instr skip1 (FEnvPush fenvLeft f') (FEnvPush fenvRight f')
-- Buffer used in both subterms
chainFutureEnvironment skip (FEnvPush fenv f) (PPush senvLeft sLeft) (PPush senvRight sRight)
  | ChainFuture    instr1 skip1 fLeft    fRight    <- chainFuture (weaken (skipWeakenIdx skip) f) sLeft sRight
  , ChainFutureEnv instr2 skip2 fenvLeft fenvRight <- chainFutureEnvironment (chainSkip skip1 skip) fenv senvLeft senvRight
  = ChainFutureEnv
      (instr1 . instr2)
      (chainSkip skip2 skip1)
      (FEnvPush fenvLeft  $ weaken (skipWeakenIdx skip2) fLeft)
      (FEnvPush fenvRight $ weaken (skipWeakenIdx skip2) fRight)
-- Only used in left subterm
chainFutureEnvironment skip (FEnvPush fenv f) (PPush senvLeft _) senvRight
  | ChainFutureEnv instr skip1 fenvLeft fenvRight <- chainFutureEnvironment skip fenv senvLeft (partialEnvTail senvRight)
  , f' <- weaken (skipWeakenIdx skip1) $ weaken (skipWeakenIdx skip) f
  = ChainFutureEnv instr skip1 (FEnvPush fenvLeft f') (fenvGSkip fenvRight)
-- Only used in right subterm
chainFutureEnvironment skip (FEnvPush fenv f) senvLeft (PPush senvRight _)
  | ChainFutureEnv instr skip1 fenvLeft fenvRight <- chainFutureEnvironment skip fenv (partialEnvTail senvLeft) senvRight
  , f' <- weaken (skipWeakenIdx skip1) $ weaken (skipWeakenIdx skip) f
  = ChainFutureEnv instr skip1 (fenvGSkip fenvLeft) (FEnvPush fenvRight f')
-- Index not present
chainFutureEnvironment skip (FEnvGSkip fenv) senvLeft senvRight
  | ChainFutureEnv instr skip1 fenvLeft fenvRight <- chainFutureEnvironment skip fenv (partialEnvTail senvLeft) (partialEnvTail senvRight)
  = ChainFutureEnv instr skip1 (fenvGSkip fenvLeft) (fenvGSkip fenvRight)
chainFutureEnvironment _ _ _ _ = internalError "Illegal case. The keys of the FutureEnv should be the union of the keys of the two SyncEnvs."


-- Data type for the existentially qualified type variable fenv' used in chainFuture
data ChainFuture kernel fenv t where
  ChainFuture
    :: (BuildSchedule kernel fenv' -> BuildSchedule kernel fenv)
    -> Skip fenv' fenv
    -> Future fenv' t
    -> Future fenv' t
    -> ChainFuture kernel fenv t

chainFuture :: Future fenv t -> Sync t -> Sync t -> ChainFuture kernel fenv t
chainFuture (FutureScalar tp _ _) SyncRead  _ = bufferImpossible tp
chainFuture (FutureScalar tp _ _) SyncWrite _ = bufferImpossible tp

-- Read before read, without a release
--          Left     Right
-- Read  --> X      -> X
--        \       /
--          -----
chainFuture f@(FutureBuffer _ _ (Move _) mwrite) SyncRead SyncRead
  | Just _ <- mwrite = internalError "Expected a FutureBuffer without write lock"
  | Nothing <- mwrite
  = ChainFuture
      -- This doesn't require any additional signals
      id
      SkipNone
      f
      f

-- Read before read
--          Left     Right
--               -------
--             /         \
-- Read  --> X      -> X -->
--        \       /
--          -----
chainFuture (FutureBuffer tp ref (Borrow s r) mwrite) SyncRead SyncRead
  | Just _ <- mwrite = internalError "Expected a FutureBuffer without write lock"
  | Nothing <- mwrite
  = ChainFuture
      -- Create a pair of signal and resolver for both subterms.
      -- Fork a thread which will resolve the final read signal when the two
      -- new signals have been resolved.
      ( buildLet lhsSignal NewSignal
        . buildLet lhsSignal NewSignal
        . buildSpawn (buildEffect (SignalAwait [signal1, signal2]) $ buildEffect (SignalResolve [weaken k r]) buildReturn)
      )
      -- Weaken all other identifiers with four, as we introduced two new signals
      -- and two new signal resolvers.
      ( SkipSucc $ SkipSucc $ SkipSucc $ SkipSucc SkipNone )
      ( FutureBuffer
          tp
          (weakenEither k ref)
          (Lock (weaken k <$> s) (Just resolver1))
          Nothing
      )
      ( FutureBuffer
          tp
          (weakenEither k ref)
          (Lock (weaken k <$> s) (Just resolver2))
          Nothing
      )
  where
    k = weakenSucc $ weakenSucc $ weakenSucc $ weakenSucc weakenId

    signal1   = SuccIdx $ SuccIdx $ SuccIdx ZeroIdx
    resolver1 =           SuccIdx $ SuccIdx ZeroIdx
    signal2   =                     SuccIdx ZeroIdx
    resolver2 =                             ZeroIdx

-- Write before read, without release
--          Left     Right
-- Read  --> X       > X
--                 /
--               /
--             /
-- Write --> X
--
-- Note that the left subterm must synchronise its read and write operations itself.
chainFuture (FutureBuffer tp ref (Move readSignal) (Just (Move writeSignal))) SyncWrite SyncRead
  = ChainFuture
      -- Create a signal to let the read operation in the second subterm only
      -- start after the write operation of the first subterm has finished.
      ( buildLet lhsSignal NewSignal )
      ( SkipSucc $ SkipSucc SkipNone )
      -- The first subterm must resolve the new signal after finishing its write operation.
      ( FutureBuffer
          tp
          (weakenEither k ref)
          (Lock (weaken k <$> readSignal) Nothing)
          (Just $ Lock (weaken k <$> writeSignal) $ Just writeResolver)
      )
      ( FutureBuffer
          tp
          (weakenEither k ref)
          (Lock (Just writeSignal2) Nothing)
          Nothing
      )
  where
    k = weakenSucc $ weakenSucc weakenId
    writeSignal2  = SuccIdx ZeroIdx
    writeResolver = ZeroIdx

-- Write before read
--          Left     Right
--               -------
--             /         \
-- Read  --> X       > X -->
--                 /
--               /
--             /
-- Write --> X ------------->
-- Note that the left subterm must synchronise its read and write operations itself.
chainFuture (FutureBuffer tp ref (Borrow readSignal readRelease) (Just (Borrow writeSignal writeRelease))) SyncWrite SyncRead
  = ChainFuture
      -- Create a signal (signal1) to let the read operation in the second subterm only
      -- start after the write operation of the first subterm has finished.
      -- Also create signals (signal2 and signal3) to denote that the read operations
      -- of respectively the left and right subterm have finished.
      -- 'readRelease' will be resolved when signal2 and signal3 are both resolved.
      -- 'writeRelease' will be resolved when signal1 is resolved.
      ( buildLet lhsSignal NewSignal
        . buildLet lhsSignal NewSignal
        . buildLet lhsSignal NewSignal
        . buildSpawn (buildEffect (SignalAwait [signal2, signal3]) $ buildEffect (SignalResolve [weaken k readRelease]) buildReturn)
        . buildSpawn (buildEffect (SignalAwait [signal1]) $ buildEffect (SignalResolve [weaken k writeRelease]) buildReturn)
      )
      ( SkipSucc $ SkipSucc $ SkipSucc $ SkipSucc $ SkipSucc $ SkipSucc SkipNone )
      ( FutureBuffer
          tp
          (weakenEither k ref)
          (Lock (weaken k <$> readSignal) (Just resolver2))
          (Just $ Lock (weaken k <$> writeSignal) (Just resolver1))
      )
      ( FutureBuffer
          tp
          (weakenEither k ref)
          (Lock (Just signal1) (Just resolver3))
          Nothing
      )
  where
    k = weakenSucc $ weakenSucc $ weakenSucc $ weakenSucc $ weakenSucc $ weakenSucc weakenId

    signal1   = SuccIdx $ SuccIdx $ SuccIdx $ SuccIdx $ SuccIdx ZeroIdx
    resolver1 =           SuccIdx $ SuccIdx $ SuccIdx $ SuccIdx ZeroIdx
    signal2   =                     SuccIdx $ SuccIdx $ SuccIdx ZeroIdx
    resolver2 =                               SuccIdx $ SuccIdx ZeroIdx
    signal3   =                                         SuccIdx ZeroIdx
    resolver3 =                                                 ZeroIdx

-- Write before read, with a write release
--          Left     Right
-- Read  --> X       > X
--                 /
--               /
--             /
-- Write --> X ------------->
-- Note that the left subterm must synchronise its read and write operations itself.
chainFuture (FutureBuffer tp ref (Move readSignal) (Just (Borrow writeSignal writeRelease))) SyncWrite SyncRead
  = ChainFuture
      -- Create a signal to let the read operation in the second subterm only
      -- start after the write operation of the first subterm has finished.
      -- 'writeSignal' can be resolved when this newly introduced signal
      -- is resolved.
      ( buildLet lhsSignal NewSignal
        . buildSpawn (buildEffect (SignalAwait [signal1]) $ buildEffect (SignalResolve [weaken k writeRelease]) buildReturn)
      )
      -- Weaken all other identifiers with two, as we introduced a new signal
      -- and a new signal resolver
      (SkipSucc $ SkipSucc SkipNone)
      ( FutureBuffer
          tp
          (weakenEither k ref)
          (Lock (weaken k <$> readSignal) Nothing)
          (Just $ Lock (weaken k <$> writeSignal) (Just resolver1))
      )
      ( FutureBuffer
          tp
          (weakenEither k ref)
          (Lock (Just signal1) Nothing)
          Nothing
      )
  where
    k = weakenSucc $ weakenSucc weakenId
    signal1   = SuccIdx ZeroIdx
    resolver1 = ZeroIdx

-- Invalid cases of write-before-read
chainFuture (FutureBuffer _ _ _ Nothing) SyncWrite SyncRead = internalError "Expected a FutureBuffer with write lock"
chainFuture (FutureBuffer _ _ (Borrow _ _) (Just (Move _))) SyncWrite SyncRead = internalError "Illegal FutureBuffer with borrow read access and move write access"

-- Read before write
--          Left     Right
--          -----
--        /       \
-- Read  --> X      -> X -->
--             \
--               \
--                 \
-- Write ------------> X -->
chainFuture (FutureBuffer tp ref read mwrite) SyncRead SyncWrite
  | Nothing <- mwrite = internalError "Expected a FutureBuffer with write lock"
  | Just write <- mwrite
  = ChainFuture
      -- Create a signal to let the write operation in the second subterm only
      -- start after the read operation of the first subterm has finished.
      -- Also create a signal which will be resolved when the newly introduced signal
      -- and the incoming write signal are both resolved.
      ( buildLet lhsSignal NewSignal
        . buildLet lhsSignal NewSignal
        . buildSpawn (buildAwait [weaken k <$> lockSignal write, Just signal1] $ buildEffect (SignalResolve [resolver2]) buildReturn)
      )
      -- Weaken all other identifiers with four, as we introduced two new signals
      -- and two new signal resolvers.
      (SkipSucc $ SkipSucc $ SkipSucc $ SkipSucc SkipNone)
      -- The first subterm must resolve the new signal after finishing its read operation.
      ( FutureBuffer
          tp
          (weakenEither k ref)
          (Borrow (weaken k <$> lockSignal read) resolver1)
          Nothing
      )
      -- The second subterm must wait on the signal before it can start the write operation.
      ( FutureBuffer
          tp
          (weakenEither k ref)
          (weaken' k read)
          (Just $ Lock (Just signal2) $ fmap (weaken k) $ lockResolver write) -- lockResolver write)
      )
  where
    k = weakenSucc $ weakenSucc $ weakenSucc $ weakenSucc weakenId

    signal1   = SuccIdx $ SuccIdx $ SuccIdx ZeroIdx
    resolver1 =           SuccIdx $ SuccIdx ZeroIdx
    signal2   =                     SuccIdx ZeroIdx
    resolver2 =                             ZeroIdx

-- Write before write
--          Left     Right
-- Read  --> X       > X -->
--             \   /
--               X
--             /   \
-- Write --> X       > X -->
chainFuture (FutureBuffer tp ref read mwrite) SyncWrite SyncWrite
  | Nothing <- mwrite = internalError "Expected a FutureBuffer with write lock"
  | Just write <- mwrite
  = ChainFuture
      -- Create two signals (signal1 and signal2) to let the first subterm
      -- inform that respectively its read or write operations have finished.
      ( buildLet lhsSignal NewSignal
        . buildLet lhsSignal NewSignal
      )
      (SkipSucc $ SkipSucc $ SkipSucc $ SkipSucc SkipNone)
      ( FutureBuffer
          tp
          (weakenEither k ref)
          (Borrow (weaken k <$> lockSignal read) resolver1)
          (Just $ Borrow (weaken k <$> lockSignal write) resolver2)
      )
      ( FutureBuffer
          tp
          (weakenEither k ref)
          (Lock (Just signal2) $ weaken k <$> lockResolver read)
          (Just $ Lock (Just signal1) $ weaken k <$> lockResolver write)
      )
  where
    k = weakenSucc $ weakenSucc $ weakenSucc $ weakenSucc weakenId

    signal1   = SuccIdx $ SuccIdx $ SuccIdx ZeroIdx
    resolver1 =           SuccIdx $ SuccIdx ZeroIdx
    signal2   =                     SuccIdx ZeroIdx
    resolver2 =                             ZeroIdx

-- Variant of chainFutureEnv, where there is no synchronisation needed between the two subterms.
-- This is used when the two terms are executed sequentially.
-- This case does require synchronisation with other parts of the program.
-- Assumes that the first term introduces no forks.
seqChainFutureEnv :: FutureEnv fenv genv -> SyncEnv genv -> SyncEnv genv -> (FutureEnv fenv genv, FutureEnv fenv genv)
seqChainFutureEnv FEnvEnd _ _ = (FEnvEnd, FEnvEnd)
seqChainFutureEnv env PEnd _ = (fRemoveBuffers env, env)
seqChainFutureEnv env _ PEnd = (env, fRemoveBuffers env)
seqChainFutureEnv (FEnvFSkip env) left right
  | (envL, envR) <- seqChainFutureEnv env left right
  = (FEnvFSkip envL, FEnvFSkip envR)
seqChainFutureEnv (FEnvGSkip env) left right
  | (envL, envR) <- seqChainFutureEnv env (partialEnvTail left) (partialEnvTail right)
  = (FEnvGSkip envL, FEnvGSkip envR)
seqChainFutureEnv (FEnvPush env future@FutureScalar{}) left right
  | (envL, envR) <- seqChainFutureEnv env (partialEnvTail left) (partialEnvTail right)
  = (FEnvPush envL future, FEnvPush envR future)
seqChainFutureEnv (FEnvPush env future) (PPush left l) (PPush right r)
  | (envL, envR) <- seqChainFutureEnv env left right
  , (futureL, futureR) <- seqChainFuture future l r
  = (FEnvPush envL futureL, FEnvPush envR futureR)
seqChainFutureEnv (FEnvPush env future) (PPush left _) right
  | (envL, envR) <- seqChainFutureEnv env left (partialEnvTail right)
  = (FEnvPush envL future, FEnvGSkip envR)
seqChainFutureEnv (FEnvPush env future) left (PPush right _)
  | (envL, envR) <- seqChainFutureEnv env (partialEnvTail left) right
  = (FEnvGSkip envL , FEnvPush envR future)
seqChainFutureEnv (FEnvPush _ FutureBuffer{}) (PNone _) (PNone _) = internalError "FutureEnv & SyncEnv mismatch"

seqChainFuture :: Future fenv t -> Sync t -> Sync t -> (Future fenv t, Future fenv t)
seqChainFuture (FutureBuffer tp ref (Lock signal resolver) Nothing) SyncRead SyncRead =
  ( FutureBuffer tp ref (Lock signal Nothing) Nothing
  , FutureBuffer tp ref (Lock Nothing resolver) Nothing
  )
seqChainFuture (FutureBuffer tp ref (Lock signal resolver) (Just (Lock wsignal wresolver))) SyncWrite SyncRead =
  ( FutureBuffer tp ref (Lock signal Nothing) (Just $ Lock wsignal wresolver)
  , FutureBuffer tp ref (Lock Nothing resolver) Nothing
  )
seqChainFuture (FutureBuffer tp ref (Lock signal resolver) (Just (Lock wsignal wresolver))) SyncRead SyncWrite =
  ( FutureBuffer tp ref (Lock signal Nothing) Nothing
  , FutureBuffer tp ref (Lock Nothing resolver) (Just $ Lock wsignal wresolver)
  )
seqChainFuture (FutureBuffer tp ref (Lock signal resolver) (Just (Lock wsignal wresolver))) SyncWrite SyncWrite =
  ( FutureBuffer tp ref (Lock signal Nothing) (Just $ Lock wsignal Nothing)
  , FutureBuffer tp ref (Lock Nothing resolver) (Just $ Lock Nothing wresolver)
  )
seqChainFuture _ _ _ = internalError "FutureBuffer & Sync mismatch"


subFutureEnvironment :: forall fenv genv kernel. FutureEnv fenv genv -> SyncEnv genv -> (FutureEnv fenv genv, BuildSchedule kernel fenv)
subFutureEnvironment = subFutureEnvironment' SkipNone

subFutureEnvironment' :: forall fenv fenv' genv kernel. Skip fenv' fenv -> FutureEnv fenv genv -> SyncEnv genv -> (FutureEnv fenv' genv, BuildSchedule kernel fenv')
subFutureEnvironment' _ FEnvEnd PEnd = (FEnvEnd, buildReturn)
subFutureEnvironment' skip (FEnvGSkip fenv) (PNone senv) = (FEnvGSkip fenv', actions)
  where
    (fenv', actions) = subFutureEnvironment' skip fenv senv
subFutureEnvironment' skip (FEnvGSkip fenv) PEnd = (FEnvGSkip fenv', actions)
  where
    (fenv', actions) = subFutureEnvironment' skip fenv PEnd
subFutureEnvironment' skip FEnvEnd (PNone senv) = (FEnvGSkip fenv', actions)
  where
    (fenv', actions) = subFutureEnvironment' skip FEnvEnd senv
subFutureEnvironment' skip (FEnvFSkip fenv) senv = subFutureEnvironment' (SkipSucc skip) fenv senv
subFutureEnvironment' skip (FEnvPush fenv f@FutureScalar{}) senv = (FEnvPush fenv' $ weaken (skipWeakenIdx skip) f, actions)
  where
    (fenv', actions) = subFutureEnvironment' skip fenv $ partialEnvTail senv
subFutureEnvironment' skip (FEnvPush fenv f@(FutureBuffer tp ref read write)) (PPush senv sync) = (FEnvPush fenv' $ weaken (skipWeakenIdx skip) f', actions')
  where
    (fenv', actions) = subFutureEnvironment' skip fenv senv

    (f', actions') = case (write, sync) of
      (Nothing, SyncRead) -> (f, actions) -- No need to change
      (Just _, SyncWrite) -> (f, actions) -- No need to change
      (Nothing, SyncWrite) -> -- Illegal input
        internalError "Got a FutureBuffer without write capabilities, but the SyncEnv asks for write permissions"
      (Just (Borrow ws wr), SyncRead) -> -- Write capability not used
        ( FutureBuffer tp ref read Nothing
        -- Resolve the write resolver after taking both the read and write signal
        , buildSpawn
            (buildEffect (SignalAwait $ fmap (weaken (skipWeakenIdx skip)) $ catMaybes [lockSignal read, ws])
              $ buildEffect (SignalResolve [weaken (skipWeakenIdx skip) $ wr]) buildReturn)
            actions
        )
      (Just (Move _), SyncRead) ->
        ( FutureBuffer tp ref read Nothing
        , actions'
        )
subFutureEnvironment' skip (FEnvPush fenv (FutureBuffer _ _ read write)) (PNone senv) = (FEnvGSkip fenv', actions')
  where
    (fenv', actions) = subFutureEnvironment' skip fenv senv

    actions' = case (read, write) of
      (Borrow rs rr, Just (Borrow ws wr)) ->
        buildSpawn
          (buildEffect (SignalAwait $ fmap (weaken $ skipWeakenIdx skip) $ catMaybes [rs])
            $ buildEffect (SignalResolve [weaken (skipWeakenIdx skip) rr])
            $ buildEffect (SignalAwait $ fmap (weaken $ skipWeakenIdx skip) $ catMaybes [ws])
            $ buildEffect (SignalResolve [weaken (skipWeakenIdx skip) wr])
            buildReturn)
          actions
      (Borrow _ _, Just (Move _)) -> internalError "Illegal FutureBuffer with borrow read access and move write access"
      (Move rs, Just (Borrow ws wr)) ->
        buildSpawn
          (buildEffect (SignalAwait $ fmap (weaken $ skipWeakenIdx skip) $ catMaybes [rs, ws])
            $ buildEffect (SignalResolve [weaken (skipWeakenIdx skip) wr])
            buildReturn)
          actions
      (Move _, Just (Move _)) -> actions
      (Borrow rs rr, Nothing) ->
        buildSpawn
          (buildEffect (SignalAwait $ fmap (weaken $ skipWeakenIdx skip) $ catMaybes [rs])
            $ buildEffect (SignalResolve [weaken (skipWeakenIdx skip) rr])
            buildReturn)
          actions
      (Move _, Nothing) -> actions
subFutureEnvironment' _ (FEnvGSkip _) (PPush _ _) = internalError "Variable missing in FutureEnv, but expected based on SyncEnv"
subFutureEnvironment' _ FEnvEnd (PPush _ _) = internalError "Variable missing in FutureEnv, but expected based on SyncEnv"
subFutureEnvironment' skip fenv@FEnvPush{} PEnd = subFutureEnvironment' skip fenv (PNone PEnd)

-- When binding new variables, the LeftHandSide and Uniquenesses might not correspond to the values in SyncEnv.
-- This is a simplified variant of subFutureEnvironment, where we only visit
-- the part of the FutureEnv corresponding to the LeftHandSide, and assume that
-- those bindings only have Move locks (no Borrows). The latter is the case
-- because of the construction in declareDestinations.
restrictEnvForLHS :: GLeftHandSide t genv genv' -> FutureEnv fenv genv' -> SyncEnv genv' -> FutureEnv fenv genv'
restrictEnvForLHS lhs = go (lhsSkip' lhs)
  where
    -- Note: Since Skip appends the environment in 
    go :: Skip' genv' genv -> FutureEnv fenv genv' -> SyncEnv genv' -> FutureEnv fenv genv'
    go SkipNone' env _ = env
    go skip (FEnvFSkip env) senv = FEnvFSkip $ go skip env senv
    go _ FEnvEnd _ = FEnvEnd
    go (SkipSucc' skip) (FEnvGSkip env) senv = FEnvGSkip $ go skip env $ partialEnvTail senv
    go (SkipSucc' skip) (FEnvPush env future@FutureScalar{}) senv = go skip env (partialEnvTail senv) `FEnvPush` future
    -- Unused buffer. The locks should be Move, so we don't need to release anything.
    go (SkipSucc' skip) (FEnvPush env _) (PNone senv) = FEnvGSkip $ go skip env senv
    go (SkipSucc' skip) (FEnvPush env future) (PPush senv sync) = go skip env senv `FEnvPush` future'
      where
        future'
          | FutureBuffer tp ref read (Just _) <- future
          , SyncRead <- sync
          -- Downgrade unique buffer to shared buffer.
          -- Note that 'write' will be Move, so we don't need to release anything.
          = FutureBuffer tp ref read Nothing
          | otherwise
          = future
    go skip@SkipSucc'{} env PEnd = go skip env (PNone PEnd)

type MaybeSignal fenv = Maybe (Idx fenv Signal)
type MaybeSignalResolver fenv = Maybe (Idx fenv SignalResolver)

buildAwait :: [MaybeSignal fenv] -> BuildSchedule kernel fenv -> BuildSchedule kernel fenv
buildAwait signals = case catMaybes signals of
  [] -> id
  signals' -> buildEffect (SignalAwait signals')

lhsSignal :: BLeftHandSide (Signal, SignalResolver) fenv ((fenv, Signal), SignalResolver)
lhsSignal = LeftHandSidePair (LeftHandSideSingle BaseRsignal) (LeftHandSideSingle BaseRsignalResolver)

lhsRef :: GroundR tp -> LeftHandSide BaseR (Ref tp, OutputRef tp) fenv ((fenv, Ref tp), OutputRef tp)
lhsRef tp = LeftHandSidePair (LeftHandSideSingle $ BaseRref tp) (LeftHandSideSingle $ BaseRrefWrite tp)
