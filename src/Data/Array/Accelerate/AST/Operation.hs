{-# LANGUAGE BangPatterns          #-}
{-# LANGUAGE EmptyCase             #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE LambdaCase            #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE TemplateHaskell       #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE TypeOperators         #-}
{-# OPTIONS_HADDOCK hide #-}
-- |
-- Module      : Data.Array.Accelerate.AST.Operation
-- Copyright   : [2008..2020] The Accelerate Team
-- License     : BSD3
--
-- Maintainer  : Trevor L. McDonell <trevor.mcdonell@gmail.com>
-- Stability   : experimental
-- Portability : non-portable (GHC extensions)
--

module Data.Array.Accelerate.AST.Operation (
  PreOpenAcc(..), PreOpenAfun(..),
  OperationAcc, OperationAfun, Execute(..),

  GroundR(..), GroundsR, GroundVar, GroundVars, GLeftHandSide,

  PreArgs(..), Arg(..), Args, Modifier(..),

  Exp', Fun', In, Out, Mut,

  OpenExp(..), OpenFun(..),

  PrimConst, PrimFun, PrimBool, PrimMaybe, ExpVar, ExpVars,
) where

import Data.Array.Accelerate.AST (PrimConst, PrimFun, PrimBool, PrimMaybe, ExpVar, ExpVars, primFunType, primConstType)
import Data.Array.Accelerate.AST.LeftHandSide
import Data.Array.Accelerate.AST.Var
import Data.Array.Accelerate.Representation.Array
import Data.Array.Accelerate.Representation.Shape
import Data.Array.Accelerate.Representation.Slice
import Data.Array.Accelerate.Representation.Tag
import Data.Array.Accelerate.Representation.Type
import Data.Array.Accelerate.Representation.Vec
import Data.Array.Accelerate.Sugar.Foreign
import Data.Array.Accelerate.Type
import Data.Array.Accelerate.Error
import Data.Primitive.Vec

import GHC.TypeNats

-- | An intermediate representation consisting parameterized over executable
-- operations. This data type only consists of the control flow structure and
-- bookkeeping (allocating or copying buffers).
--
-- The data type is parameterized over the type of executable operations. In
-- the compiler pipeline, it is first instantiated with 'Execute op', which
-- means that the Exec constructor will target a single operation. Type
-- argument op is platform dependent, such that we can have different
-- operations for each backend and thus have backend specific optimizations
-- for some combinators. For instance, some backends may have a three kernel
-- scan whereas others have a single pass scan, or we may have different
-- operations based on which atomic instructions are available on the backend.
--
-- The data type is also parameterized over the environment of the terms,
-- consisting of ground values typed by 'GroundR', and the return type, which
-- is a tuple of ground values, typed by 'GroundsR'.
--
data PreOpenAcc exe env a where
  -- | Executes an executable operation. Such execution does not return a
  -- value, the effects of the execution are only visible by the mutation of
  -- buffers which were annotated with either 'Mut' or 'Out'.
  --
  Exec    :: exe env
          -> PreOpenAcc exe env ()

  -- | Returns the values of the given variables.
  --
  Return  :: GroundVars env a
          -> PreOpenAcc exe env a

  -- | Evaluates the expression and returns its value.
  --
  Compute :: OpenExp env t
          -> PreOpenAcc exe env t

  -- | Local binding of ground values.
  -- As it is common in this intermediate representation to evaluate some program
  -- resulting in unit, for instance when execution some operation, and then
  -- and then do some other code, we write 'a; b' to denote 'let () = a in b'.
  Alet     :: GLeftHandSide t env env'
          -> PreOpenAcc exe env  t
          -> PreOpenAcc exe env' b
          -> PreOpenAcc exe env  b

  -- | Allocates a new buffer of the given size.
  --
  Alloc   :: ShapeR sh
          -> ScalarType e
          -> ExpVars env sh
          -> PreOpenAcc exe env (Buffer e)

  -- | Buffer inlet. To pass an array constant in this data type, one may need
  -- multiple 'Use' constructs because of the explicit Structure-of-Arrays.
  -- Triggers (possibly) asynchronous host->device transfer if necessary.
  --
  Use     :: ScalarType e
          -> Buffer e
          -> PreOpenAcc exe env (Buffer e)

  -- | Capture a scalar in a singleton buffer
  --
  Unit    :: ExpVar env e
          -> PreOpenAcc exe env (Buffer e)

  -- | Copies a buffer. This is used before passing a buffer to a 'Mut' argument,
  -- to make sure it is unique. This may be removed during fusion to facilitate
  -- in-place updates
  --
  Clone   :: ShapeR sh
          -> ExpVars env sh
          -> GroundVar env (Buffer e)
          -> PreOpenAcc exe env (Buffer e)

  -- | If-then-else for array-level computations
  --
  Acond   :: ExpVar env Bool
          -> PreOpenAcc exe env a
          -> PreOpenAcc exe env a
          -> PreOpenAcc exe env a

  -- Value-recursion for array-level computations
  --
  Awhile  :: PreOpenAfun exe env (arrs -> Bool)
          -> PreOpenAfun exe env (arrs -> arrs)
          -> PreOpenAcc  exe env arrs
          -> PreOpenAcc  exe env arrs

-- | Function abstraction over parametrised array computations
--
data PreOpenAfun com env t where
  Abody ::                             PreOpenAcc  com env  t -> PreOpenAfun acc env t
  Alam  :: GLeftHandSide a env env' -> PreOpenAfun acc env' t -> PreOpenAfun acc env (a -> t)


-- | Ground values are buffers or scalars.
--
data GroundR a where
  GroundRbuffer :: ScalarType e -> GroundR (Buffer e)
  GroundRscalar :: ScalarType e -> GroundR e

-- | Tuples of ground values
--
type GroundsR = TupR GroundR

-- | Types for local bindings
type GLeftHandSide = LeftHandSide GroundR
type GroundVar      = Var  GroundR
type GroundVars env = Vars GroundR env

-- | The arguments to be passed to an operation of type `t`.
-- This type is represented as a cons list, separated by (->) and ending
-- in (). This function type represents the type of the operations.
-- `PreArgs a t` provides the arguments for function type `t`, where `a`
-- provides a single argument.
--
data PreArgs a t where
  ArgsNil :: PreArgs a ()
  (:>:)   :: a s -> PreArgs a t -> PreArgs a (s -> t)

-- | A single argument to an operation.
--
data Arg env t where
  ArgExp      :: ExpVars env e         -> Arg env (Exp' e)

  ArgMaybeExp :: Maybe (ExpVars env e) -> Arg env (Maybe (Exp' e))

  ArgFun      :: OpenFun env e         -> Arg env (Fun' e)

  -- | An array is represented as scalar variables denoting the size and buffer variables.
  -- We assume that all the buffer variables stored in 'ArgBuffers' have the same size,
  -- as specified by the scalar variables of the size.
  --
  ArgArray    :: Modifier m
              -> ShapeR sh
              -> GroundVars env sh
              -> GroundVars env (Buffers e)
              -> Arg env (m sh e)

-- | The arguments to be passed to an operation, in some environment.
--
type Args env = PreArgs (Arg env)

-- | Array arguments are annotated with an access modifier
--
data Modifier m where
  -- | The operation only reads from this array
  In  :: Modifier In
  -- | The operation only writes to the array. The initial content of the array is thus irrelevant
  Out :: Modifier Out
  -- | The operation both reads and writes to the array.
  Mut :: Modifier Mut

-- Empty data types, which are only used for the types of 'Arg'.
data Exp' e   where
data Fun' t   where
data In  sh e where
data Out sh e where
data Mut sh e where

-- | Executes a single operation. Provides the operation arguments
-- from the environment.
--
data Execute op env where
  Execute :: op args -> Args env args -> Execute op env

-- | An intermediate representation consisting of operations. This data type
-- only consists of the control flow structure and bookkeeping (allocating or
-- copying buffers). It is parameterized over the actual type of operations.
--
type OperationAcc op = PreOpenAcc (Execute op)

-- | Functions on an intermediate representation consisting of operations.
-- This data type only consists of the control flow structure and bookkeeping (allocating or
-- copying buffers). It is parameterized over the actual type of operations.
--
type OperationAfun op = PreOpenAfun (Execute op)


-- | Vanilla open expressions using de Bruijn indices for variables ranging
-- over tuples of scalars and arrays of tuples. All code, except Cond, is
-- evaluated eagerly. N-tuples are represented as nested pairs.
--
-- The data type is parametrised over the representation type (not the
-- surface types). The environment contains buffers and scalar values,
-- in contrary to earlier stages in the compiler which have separate
-- environments for arrays and for scalars
--
data OpenExp env t where

  -- Local binding of a scalar expression and buffer variables
  Let           :: GLeftHandSide bnd_t env env'
                -> OpenExp env  bnd_t
                -> OpenExp env' body_t
                -> OpenExp env  body_t

  -- Variable index, ranging only over scalars or buffers
  ExpVar        :: GroundVar env t
                -> OpenExp env t

  -- Apply a backend-specific foreign function
  Foreign       :: Foreign asm
                => GroundsR y
                -> asm         (x -> y)    -- foreign function
                -> OpenFun env (x -> y)    -- alternate implementation (for other backends)
                -> OpenExp env x
                -> OpenExp env y

  -- Tuples
  Pair          :: OpenExp env t1
                -> OpenExp env t2
                -> OpenExp env (t1, t2)

  Nil           :: OpenExp env ()

  -- SIMD vectors
  VecPack       :: KnownNat n
                => VecR n s tup
                -> OpenExp env tup
                -> OpenExp env (Vec n s)

  VecUnpack     :: KnownNat n
                => VecR n s tup
                -> OpenExp env (Vec n s)
                -> OpenExp env tup

  -- Array indices & shapes
  IndexSlice    :: SliceIndex slix sl co sh
                -> OpenExp env slix
                -> OpenExp env sh
                -> OpenExp env sl

  IndexFull     :: SliceIndex slix sl co sh
                -> OpenExp env slix
                -> OpenExp env sl
                -> OpenExp env sh

  -- Shape and index conversion
  ToIndex       :: ShapeR sh
                -> OpenExp env sh           -- shape of the array
                -> OpenExp env sh           -- index into the array
                -> OpenExp env Int

  FromIndex     :: ShapeR sh
                -> OpenExp env sh           -- shape of the array
                -> OpenExp env Int          -- index into linear representation
                -> OpenExp env sh

  -- Case statement
  Case          :: OpenExp env TAG
                -> [(TAG, OpenExp env b)]      -- list of equations
                -> Maybe (OpenExp env b)       -- default case
                -> OpenExp env b

  -- Conditional expression (non-strict in 2nd and 3rd argument)
  Cond          :: OpenExp env PrimBool
                -> OpenExp env t
                -> OpenExp env t
                -> OpenExp env t

  -- Value recursion
  While         :: OpenFun env (a -> PrimBool) -- continue while true
                -> OpenFun env (a -> a)        -- function to iterate
                -> OpenExp env a               -- initial value
                -> OpenExp env a

  -- Constant values
  Const         :: ScalarType t
                -> t
                -> OpenExp env t

  PrimConst     :: PrimConst t
                -> OpenExp env t

  -- Primitive scalar operations
  PrimApp       :: PrimFun (a -> r)
                -> OpenExp env a
                -> OpenExp env r

  -- Project a single scalar from an array.
  -- The array expression can not contain any free scalar variables.
  LinearIndex   :: GroundVar env (Buffer t)
                -> OpenExp env Int
                -> OpenExp env t

  -- Number of elements of an array given its shape
  ShapeSize     :: ShapeR dim
                -> OpenExp env dim
                -> OpenExp env Int

  -- Unsafe operations (may fail or result in undefined behaviour)
  -- An unspecified bit pattern
  Undef         :: ScalarType t
                -> OpenExp env t

  -- Reinterpret the bits of a value as a different type
  Coerce        :: BitSizeEq a b
                => ScalarType a
                -> ScalarType b
                -> OpenExp env a
                -> OpenExp env b

-- | Vanilla open function abstraction
--
data OpenFun env t where
  Body ::                             OpenExp env  t -> OpenFun env t
  Lam  :: GLeftHandSide a env env' -> OpenFun env' t -> OpenFun env (a -> t)

class HasGroundsR f where
  groundsR :: f a -> GroundsR a

instance HasGroundsR (PreOpenAcc exe env) where
  groundsR (Exec _)          = TupRunit
  groundsR (Return vars)     = groundsR vars
  groundsR (Compute e)       = groundsR e
  groundsR (Alet _ _ a)      = groundsR a
  groundsR (Alloc _ tp _)    = TupRsingle $ GroundRbuffer tp
  groundsR (Use tp _)        = TupRsingle $ GroundRbuffer tp
  groundsR (Unit (Var tp _)) = TupRsingle $ GroundRbuffer tp
  groundsR (Clone _ _ var)   = groundsR var
  groundsR (Acond _ a _)     = groundsR a
  groundsR (Awhile _ _ a)    = groundsR a

instance HasGroundsR (GroundVar env) where
  groundsR (Var repr _) = TupRsingle repr

instance HasGroundsR (GroundVars env) where
  groundsR = varsType

instance HasGroundsR (OpenExp env) where
  groundsR (Let _ _ e)             = groundsR e
  groundsR (ExpVar (Var tp _))     = TupRsingle tp
  groundsR (Foreign tp _ _ _)      = tp
  groundsR (Pair e1 e2)            = groundsR e1 `TupRpair` groundsR e2
  groundsR Nil                     = TupRunit
  groundsR (VecPack   vecR _)      = TupRsingle $ GroundRscalar $ VectorScalarType $ vecRvector vecR
  groundsR (VecUnpack vecR _)      = typeRtoGroundsR $ vecRtuple vecR
  groundsR (IndexSlice si _ _)     = typeRtoGroundsR $ shapeType $ sliceShapeR si
  groundsR (IndexFull  si _ _)     = typeRtoGroundsR $ shapeType $ sliceDomainR si
  groundsR ToIndex{}               = TupRsingle $ GroundRscalar scalarTypeInt
  groundsR (FromIndex shr _ _)     = typeRtoGroundsR $ shapeType shr
  groundsR (Case _ ((_,e):_) _)    = groundsR e
  groundsR (Case _ [] (Just e))    = groundsR e
  groundsR Case{}                  = internalError "empty case encountered"
  groundsR (Cond _ e _)            = groundsR e
  groundsR (While _ (Lam lhs _) _) = lhsToTupR lhs
  groundsR While{}                 = error "What's the matter, you're running in the shadows"
  groundsR (Const tR _)            = TupRsingle $ GroundRscalar tR
  groundsR (PrimConst c)           = TupRsingle $ GroundRscalar $ SingleScalarType $ primConstType c
  groundsR (PrimApp f _)           = typeRtoGroundsR $ snd $ primFunType f
  groundsR (LinearIndex (Var (GroundRbuffer tp) _) _)
                                   = TupRsingle $ GroundRscalar tp
  groundsR (LinearIndex (Var (GroundRscalar tp) _) _)
                                   = bufferImpossible tp
  groundsR (ShapeSize{})           = TupRsingle $ GroundRscalar scalarTypeInt
  groundsR (Undef tR)              = TupRsingle $ GroundRscalar tR
  groundsR (Coerce _ tR _)         = TupRsingle $ GroundRscalar tR

typeRtoGroundsR :: TypeR t -> GroundsR t
typeRtoGroundsR = mapTupR GroundRscalar

bufferImpossible :: ScalarType (Buffer e) -> a
bufferImpossible (SingleScalarType (NumSingleType (IntegralNumType tp))) = case tp of {}
bufferImpossible (SingleScalarType (NumSingleType (FloatingNumType tp))) = case tp of {}
