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
  GFunctionR(..)
) where

import Data.Array.Accelerate.AST.Partitioned
import Data.Array.Accelerate.AST.Schedule
import Data.Type.Equality

class Execute sched kernel where
  executeAfun :: GFunctionR t -> sched kernel () (Scheduled sched t) -> IO t

executeAcc :: forall sched kernel t. Execute sched kernel => GroundsR t -> sched kernel () (ScheduleOutput sched t -> ()) -> IO t
executeAcc repr sched
  | Refl <- reprIsBody @sched repr
  = executeAfun (GFunctionRbody repr) sched

data GFunctionR t where
  GFunctionRlam  :: GroundsR t -> GFunctionR s -> GFunctionR (t -> s)
  GFunctionRbody :: GroundsR t                 -> GFunctionR t
