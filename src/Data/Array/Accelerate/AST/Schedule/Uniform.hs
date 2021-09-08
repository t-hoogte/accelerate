{-# LANGUAGE EmptyCase            #-}
{-# LANGUAGE GADTs                #-}
{-# LANGUAGE RankNTypes           #-}
{-# LANGUAGE ScopedTypeVariables  #-}
{-# LANGUAGE TemplateHaskell      #-}
{-# LANGUAGE TypeOperators        #-}
{-# LANGUAGE TypeFamilies         #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_HADDOCK hide #-}
-- |
-- Module      : Data.Array.Accelerate.Schedule.Uniform
-- Copyright   : [2008..2020] The Accelerate Team
-- License     : BSD3
--
-- Maintainer  : Trevor L. McDonell <trevor.mcdonell@gmail.com>
-- Stability   : experimental
-- Portability : non-portable (GHC extensions)
--

module Data.Array.Accelerate.AST.Schedule.Uniform (
  UniformSchedule(..), UniformScheduleFun(..),
  Input, Output, inputSingle, inputR, outputR, InputOutputR(..),
  Binding(..), Effect(..),
  BaseR(..), BasesR, BaseVar, BaseVars, BLeftHandSide,
  Signal(..), SignalResolver(..), Ref(..), OutputRef(..),
  module Operation,
  module Partitioned,
  await, resolve,
  signalResolverImpossible, scalarSignalResolverImpossible,

  -- ** Free variables
  freeVars, funFreeVars, effectFreeVars, bindingFreeVars,
) where

import Data.Array.Accelerate.AST.Exp
import Data.Array.Accelerate.AST.Idx
import Data.Array.Accelerate.AST.IdxSet ( IdxSet )
import qualified Data.Array.Accelerate.AST.IdxSet as IdxSet
import Data.Array.Accelerate.AST.LeftHandSide
import Data.Array.Accelerate.AST.Var
import Data.Array.Accelerate.Type
import Data.Array.Accelerate.Representation.Array
import Data.Array.Accelerate.Representation.Shape
import Data.Array.Accelerate.Representation.Type
import Data.Array.Accelerate.AST.Operation   as Operation           hiding (PreOpenAcc(..), PreOpenAfun(..))
import Data.Array.Accelerate.AST.Partitioned as Partitioned         hiding (PartitionedAcc, PartitionedAfun)
import Data.Array.Accelerate.Trafo.Exp.Substitution
import Control.Concurrent.MVar
import Data.IORef
import Data.Typeable                                                ( (:~:)(..) )

-- Generic schedule for a uniform memory space and uniform scheduling.
-- E.g., we don't have host and device memory or scheduling.
-- The schedule will exploit task parallelism.

-- The schedule consists of bindings, effects and (parallel) control flow
data UniformSchedule op env where
  Return  :: UniformSchedule op env

  Alet    :: BLeftHandSide t env env'
          -> Binding env t
          -> UniformSchedule op env'
          -> UniformSchedule op env

  Effect  :: Effect op env
          -> UniformSchedule op env
          -> UniformSchedule op env

  Acond   :: ExpVar env PrimBool
          -> UniformSchedule op env -- True branch
          -> UniformSchedule op env -- False branch
          -> UniformSchedule op env -- Operations after the if-then-else
          -> UniformSchedule op env

  -- The step function of the loop outputs a bool to denote whether the loop should
  -- proceed. If true, then the other output values should also be filled, possibly at
  -- a later point in time. If it is false, then no other output values may be filled.
  Awhile  :: InputOutputR input output
          -> UniformScheduleFun op env (input -> Output PrimBool -> output -> ())
          -> BaseVars env input
          -> UniformSchedule op env -- Operations after the while loop
          -> UniformSchedule op env

  -- Whereas Fork is symmetric, we generate programs in a way in which it is usually better
  -- to execute the first branch first. A fork should thus be evaluated by delegating the second branch
  -- (eg by putting the second branch in a queue) and continueing with the first branch
  Fork    :: UniformSchedule op env
          -> UniformSchedule op env
          -> UniformSchedule op env

data UniformScheduleFun op env t where
  Slam  :: BLeftHandSide s env env'
        -> UniformScheduleFun op env' t
        -> UniformScheduleFun op env  (s -> t)

  Sbody :: UniformSchedule    op env
        -> UniformScheduleFun op env ()

type family Input t where
  Input ()         = ()
  Input (a, b)     = (Input a, Input b)
  Input t          = (Signal, Ref t)

inputSingle :: forall t. GroundR t -> (Input t, Output t) :~: ((Signal, Ref t), (SignalResolver, OutputRef t))
-- Last case of type family Input and Output.
-- We must pattern match to convince the type checker that
-- t is not () or (a, b).
inputSingle (GroundRbuffer _) = Refl
inputSingle (GroundRscalar (VectorScalarType _)) = Refl
inputSingle (GroundRscalar (SingleScalarType (NumSingleType tp))) = case tp of
  IntegralNumType TypeInt    -> Refl
  IntegralNumType TypeInt8   -> Refl
  IntegralNumType TypeInt16  -> Refl
  IntegralNumType TypeInt32  -> Refl
  IntegralNumType TypeInt64  -> Refl
  IntegralNumType TypeWord   -> Refl
  IntegralNumType TypeWord8  -> Refl
  IntegralNumType TypeWord16 -> Refl
  IntegralNumType TypeWord32 -> Refl
  IntegralNumType TypeWord64 -> Refl
  FloatingNumType TypeHalf   -> Refl
  FloatingNumType TypeFloat  -> Refl
  FloatingNumType TypeDouble -> Refl

inputR :: forall t. GroundsR t -> BasesR (Input t)
inputR TupRunit = TupRunit
inputR (TupRpair t1 t2) = TupRpair (inputR t1) (inputR t2)
inputR (TupRsingle ground)
  -- Last case of type family Input.
  -- We must pattern match to convince the type checker that
  -- t is not () or (a, b).
  | Refl <- inputSingle ground = TupRsingle BaseRsignal `TupRpair` TupRsingle (BaseRref ground)

type family Output t where
  Output ()     = ()
  Output (a, b) = (Output a, Output b)
  Output t      = (SignalResolver, OutputRef t)

outputR :: GroundsR t -> BasesR (Output t)
outputR TupRunit = TupRunit
outputR (TupRpair t1 t2) = TupRpair (outputR t1) (outputR t2)
outputR (TupRsingle ground)
  -- Last case of type family Output.
  -- We must pattern match to convince the type checker that
  -- t is not () or (a, b).
  | Refl <- inputSingle ground = TupRsingle BaseRsignalResolver `TupRpair` TupRsingle (BaseRrefWrite ground)

-- Relation between input and output
data InputOutputR input output where
  InputOutputRsignal  :: InputOutputR Signal SignalResolver
  -- The next iteration of the loop may signal that it wants to release the buffer,
  -- such that the previous iteration can free that buffer (or release it for other operations).
  InputOutputRrelease :: InputOutputR SignalResolver Signal
  InputOutputRref     :: InputOutputR (Ref f) (OutputRef t)
  InputOutputRpair    :: InputOutputR i1 o1
                      -> InputOutputR i2 o2
                      -> InputOutputR (i1, i2) (o1, o2)
  InputOutputRunit    :: InputOutputR () ()

-- Bindings of instructions which have some return value.
-- They cannot perform side effects.
--
data Binding env t where
  Compute       :: Exp env t
                -> Binding env t

  NewSignal     :: Binding env (Signal, SignalResolver)

  NewRef        :: GroundR t
                -> Binding env (Ref t, OutputRef t)

  Alloc         :: ShapeR sh
                -> ScalarType e
                -> ExpVars env sh
                -> Binding env (Buffer e)

  Use           :: ScalarType e
                -> Buffer e
                -> Binding env (Buffer e)

  Unit          :: ExpVar env e
                -> Binding env (Buffer e)

  -- undefined result if the Ref hasn't been written
  RefRead       :: BaseVar env (Ref t) -> Binding env t

-- Effects do not have a return value.
data Effect op env where
  Exec          :: op args
                -> Args env args
                -> Effect op env

  SignalAwait   :: [Idx env Signal] -> Effect op env

  SignalResolve :: [Idx env SignalResolver] -> Effect op env

  RefWrite      :: BaseVar env (OutputRef t) -> BaseVar env t -> Effect op env

-- A base value in the schedule is a scalar, buffer, a signal (resolver)
-- or a (possibly mutable) reference
--
data BaseR t where
  BaseRground         :: GroundR t -> BaseR t
  BaseRsignal         :: BaseR Signal
  BaseRsignalResolver :: BaseR SignalResolver
  BaseRref            :: GroundR t -> BaseR (Ref t)
  BaseRrefWrite       :: GroundR t -> BaseR (OutputRef t)

-- Tuples of base values
type BasesR = TupR BaseR

type BaseVar      = Var BaseR
type BaseVars env = Vars BaseR env

type BLeftHandSide = LeftHandSide BaseR

newtype Signal = Signal (MVar ())
newtype SignalResolver = SignalResolver (MVar ())

-- Note: Refs should only be assigned once. They start undefined, and are at some point resolved to a value
newtype Ref t  = Ref (IORef t)
newtype OutputRef t = OutputRef (IORef t)

await :: [Idx env Signal] -> UniformSchedule op env -> UniformSchedule op env
await [] = id
await signals = Effect (SignalAwait signals)

resolve :: [Idx env SignalResolver] -> UniformSchedule op env -> UniformSchedule op env
resolve [] = id
resolve signals = Effect (SignalResolve signals)

freeVars :: UniformSchedule op env -> IdxSet env
freeVars Return = IdxSet.empty
freeVars (Alet lhs bnd s) = bindingFreeVars bnd `IdxSet.union` IdxSet.drop' lhs (freeVars s)
freeVars (Effect effect s) = effectFreeVars effect `IdxSet.union` freeVars s
freeVars (Acond c t f s)
  = IdxSet.insertVar c
  $ IdxSet.union (freeVars t)
  $ IdxSet.union (freeVars f)
  $ freeVars s
freeVars (Awhile _ step ini continuation)
  = IdxSet.union (funFreeVars step)
  $ IdxSet.union (IdxSet.fromVarList $ flattenTupR ini)
  $ freeVars continuation
freeVars (Fork s1 s2) = freeVars s1 `IdxSet.union` freeVars s2

funFreeVars :: UniformScheduleFun op env t -> IdxSet env
funFreeVars (Sbody s)    = freeVars s
funFreeVars (Slam lhs f) = IdxSet.drop' lhs $ funFreeVars f

bindingFreeVars :: Binding env t -> IdxSet env
bindingFreeVars NewSignal      = IdxSet.empty
bindingFreeVars (NewRef _)     = IdxSet.empty
bindingFreeVars (Alloc _ _ sh) = IdxSet.fromVarList $ flattenTupR sh
bindingFreeVars (Use _ _)      = IdxSet.empty
bindingFreeVars (Unit var)     = IdxSet.singletonVar var
bindingFreeVars (RefRead var)  = IdxSet.singletonVar var
bindingFreeVars (Compute e)    = IdxSet.fromList $ map f $ arrayInstrs e
  where
    f :: Exists (ArrayInstr env) -> Exists (Idx env)
    f (Exists (Index (Var _ idx)))     = Exists idx
    f (Exists (Parameter (Var _ idx))) = Exists idx

effectFreeVars :: Effect op env -> IdxSet env
effectFreeVars (Exec _ args)           = IdxSet.fromVarList $ argsVars args
effectFreeVars (SignalAwait signals)     = IdxSet.fromList $ map Exists $ signals
effectFreeVars (SignalResolve resolvers) = IdxSet.fromList $ map Exists resolvers
effectFreeVars (RefWrite ref value)      = IdxSet.insertVar ref $ IdxSet.singletonVar value

signalResolverImpossible :: GroundsR SignalResolver -> a
signalResolverImpossible (TupRsingle (GroundRscalar tp)) = scalarSignalResolverImpossible tp

scalarSignalResolverImpossible :: ScalarType SignalResolver -> a
scalarSignalResolverImpossible (SingleScalarType (NumSingleType (IntegralNumType tp))) = case tp of {}
scalarSignalResolverImpossible (SingleScalarType (NumSingleType (FloatingNumType tp))) = case tp of {}
