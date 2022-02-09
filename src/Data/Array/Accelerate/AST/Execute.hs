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
  executeAfun,
  executeAcc,
  GFunctionR(..)
) where

import Data.Array.Accelerate.AST.Partitioned
import Data.Array.Accelerate.AST.Schedule
import Data.Array.Accelerate.Representation.Ground
import Data.Type.Equality

class Execute sched kernel where
  executeAfunSchedule :: GFunctionR t -> sched kernel () (Scheduled sched t) -> IOFun (Scheduled sched t)

executeAfun :: forall sched kernel t. (IsSchedule sched, Execute sched kernel) => GFunctionR t -> sched kernel () (Scheduled sched t) -> IOFun t
executeAfun repr sched = flattenIOFun repr $ callScheduledFun @sched repr $ executeAfunSchedule repr sched

executeAcc :: forall sched kernel t. (IsSchedule sched, Execute sched kernel) => GroundsR t -> sched kernel () (ScheduleOutput sched t -> ()) -> IO t
executeAcc repr sched
  | Refl <- reprIsBody @sched repr
  = executeAfun (GFunctionRbody repr) sched
