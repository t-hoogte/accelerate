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
  Backend(..), run
) where

import qualified Data.Array.Accelerate.Smart as Smart
import Data.Array.Accelerate.AST.Partitioned
import Data.Array.Accelerate.AST.Schedule
import Data.Array.Accelerate.AST.Kernel
import Data.Array.Accelerate.AST.Execute
import Data.Array.Accelerate.Sugar.Array as Sugar
import Data.Array.Accelerate.Representation.Ground
import Data.Array.Accelerate.Trafo

import qualified Data.Array.Accelerate.Trafo.Desugar as Desugar
import qualified Data.Array.Accelerate.Trafo.Partitioning.ILP.Graph as Partitioning
import Data.Kind
import System.IO.Unsafe

class
  ( Desugar.DesugarAcc (Operation backend)
  , Partitioning.MakesILP (Operation backend)
  , IsSchedule (Schedule backend)
  , IsKernel (Kernel backend)
  , Execute (Schedule backend) (Kernel backend)
  ) => Backend backend where

  type Schedule backend :: (Type -> Type) -> Type -> Type -> Type
  type Kernel backend :: Type -> Type

type Operation backend = KernelOperation (Kernel backend)

-- Backend can be chosen with an explicit type application, for instance:
--   run @Interpreter acc
run :: forall backend t. Sugar.Arrays t => Backend backend => Smart.Acc t -> t
run acc = unsafePerformIO $ do
  result <- executeAcc (desugarArraysR repr) schedule
  return $ toArr $ sugarArrays repr result
  where
    repr = Sugar.arraysR @t
    schedule = convertAcc @(Schedule backend) @(Kernel backend) acc
