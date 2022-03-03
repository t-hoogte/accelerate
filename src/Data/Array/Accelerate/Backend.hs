{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE BangPatterns        #-}
{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE GADTs               #-}
{-# LANGUAGE MagicHash           #-}
{-# LANGUAGE PatternGuards       #-}
{-# LANGUAGE RankNTypes          #-}
{-# LANGUAGE RecordWildCards     #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications    #-}
{-# LANGUAGE TypeFamilies        #-}
{-# LANGUAGE TypeOperators       #-}
{-# LANGUAGE ViewPatterns        #-}

-- |
-- Module      : Data.Array.Accelerate.Backend
-- Copyright   : [2012..2020] The Accelerate Team
-- License     : BSD3
--
-- Maintainer  : Trevor L. McDonell <trevor.mcdonell@gmail.com>
-- Stability   : experimental
-- Portability : non-portable (GHC extensions)
--
-- This module defines the interface for kernels, to be implemented
-- in other modules.
--

module Data.Array.Accelerate.Backend (
  Backend(..),
  run, runWith,
  run1, run1With,
  runN, runNWith,
) where

import qualified Data.Array.Accelerate.Smart as Smart
import Data.Array.Accelerate.AST.Schedule
import Data.Array.Accelerate.AST.Kernel
import Data.Array.Accelerate.AST.Execute
import qualified Data.Array.Accelerate.Sugar.Array as Sugar
import Data.Array.Accelerate.Representation.Array
import Data.Array.Accelerate.Representation.Ground
import Data.Array.Accelerate.Trafo
import Data.Array.Accelerate.Trafo.Config
import qualified Data.Array.Accelerate.Trafo.Operation.LiveVars as Operation

import Data.Array.Accelerate.Trafo.Sharing (Afunction(..), AfunctionRepr(..), afunctionGroundR, afunctionRepr)
import qualified Data.Array.Accelerate.Trafo.Desugar as Desugar
import qualified Data.Array.Accelerate.Trafo.Partitioning.ILP.Graph as Partitioning
import qualified Data.Array.Accelerate.Pretty.Operation as Pretty
import Data.Kind
import Data.Type.Equality
import System.IO.Unsafe (unsafePerformIO)

class
  ( Desugar.DesugarAcc (Operation backend)
  , Operation.SLVOperation (Operation backend)
  , Partitioning.MakesILP (Operation backend)
  , IsSchedule (Schedule backend)
  , IsKernel (Kernel backend)
  , Pretty.PrettyOp (Operation backend)
  , Execute (Schedule backend) (Kernel backend)
  ) => Backend backend where

  type Schedule backend :: (Type -> Type) -> Type -> Type -> Type
  type Kernel backend :: Type -> Type

type Operation backend = KernelOperation (Kernel backend)

-- Backend can be chosen with an explicit type application, for instance:
--   run @Interpreter acc
run :: forall backend t. (Sugar.Arrays t, Backend backend) => Smart.Acc t -> t
run = runWith @backend defaultOptions

runWith :: forall backend t. (Sugar.Arrays t, Backend backend) => Config -> Smart.Acc t -> t
runWith config acc
  = Sugar.toArr $ sugarArrays repr $ unsafePerformIO $ executeAcc (desugarArraysR repr) schedule
  where
    repr = Sugar.arraysR @t
    schedule = convertAccWith @(Schedule backend) @(Kernel backend) config acc

run1
  :: forall backend s t.
     (Sugar.Arrays s, Sugar.Arrays t, Backend backend)
  => (Smart.Acc s -> Smart.Acc t)
  -> s -> t
run1 = runN @backend

run1With
  :: forall backend s t.
     (Sugar.Arrays s, Sugar.Arrays t, Backend backend)
  => Config
  -> (Smart.Acc s -> Smart.Acc t)
  -> s -> t
run1With = runNWith @backend

runN
  :: forall backend f.
     (Afunction f, Backend backend)
  => f
  -> AfunctionR f
runN = runNWith @backend defaultOptions

runNWith
  :: forall backend f.
     (Afunction f, Backend backend)
  => Config
  -> f
  -> AfunctionR f
runNWith config f = schedule `seq` sugarFunction (afunctionRepr @f) $ executeAfun (afunctionGroundR @f) schedule
  where
    schedule = convertAfunWith @(Schedule backend) @(Kernel backend) config f

sugarFunction
  :: forall f.
     AfunctionRepr f (AfunctionR f) (ArraysFunctionR f)
  -> IOFun (DesugaredAfun (ArraysFunctionR f))
  -> AfunctionR f
sugarFunction AfunctionReprBody a
  | Refl <- desugaredAfunIsBody repr
  , Refl <- reprIsBody (desugarArraysR repr) = Sugar.toArr $ sugarArrays repr $ unsafePerformIO a
  where
    repr = Sugar.arraysR @(AfunctionR f)
sugarFunction (AfunctionReprLam r) f = \x -> sugarFunction r $ f $ desugarArrays repr $ Sugar.fromArr x
  where
    repr :: forall a b. f ~ (Smart.Acc a -> b) => ArraysR (Sugar.ArraysR a)
    repr = Sugar.arraysR @a
