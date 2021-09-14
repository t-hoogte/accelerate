{-# LANGUAGE TypeFamilies #-}

-- |
-- Module      : Data.Array.Accelerate.AST.Kernel
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

module Data.Array.Accelerate.AST.Kernel (
  IsKernel(..),
  compileKernels,
) where

import Data.Array.Accelerate.AST.Partitioned
import Data.Array.Accelerate.AST.Schedule
import Data.Kind

class NFData' kernel => IsKernel kernel where
  type KernelOperation kernel :: Type -> Type
  compileKernel :: Cluster (KernelOperation kernel) args -> kernel args

compileKernels :: (IsSchedule sched, IsKernel kernel) => sched (Cluster (KernelOperation kernel)) env t -> sched kernel env t
compileKernels = mapSchedule compileKernel
