{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE TypeApplications      #-}
{-# LANGUAGE TypeFamilies          #-}

-- |
-- Module      : Data.Array.Accelerate.AST.Kernel
-- Copyright   : [2012..2020] The Accelerate Team
-- License     : BSD3
--
-- Maintainer  : Trevor L. McDonell <trevor.mcdonell@gmail.com>
-- Stability   : experimental
-- Portability : non-portable (GHC extensions)
--
-- This module defines the interface to execute progams, to be implemented
-- in other modules for different backends.
--

module Data.Array.Accelerate.AST.Execute (
  Execute(..),
  executeAcc,
  FunctionR(..)
) where

import Data.Array.Accelerate.AST.Partitioned
import Data.Array.Accelerate.AST.Schedule
import Data.Type.Equality

class Execute sched kernel where
  executeAfun :: FunctionR t -> sched kernel () (Scheduled sched t) -> t

executeAcc :: forall sched kernel t. Execute sched kernel => GroundsR t -> sched kernel () (ScheduleOutput sched t -> ()) -> t
executeAcc repr sched
  | Refl <- reprIsBody @sched repr
  = executeAfun (FunctionRbody repr) sched

data FunctionR t where
  FunctionRlam  :: GroundsR t -> FunctionR s -> FunctionR (t -> s)
  FunctionRbody :: GroundsR t                -> FunctionR t
