-- |
-- Module      : Data.Array.Accelerate.Pretty.Schedule
-- Copyright   : [2008..2020] The Accelerate Team
-- License     : BSD3
--
-- Maintainer  : Trevor L. McDonell <trevor.mcdonell@gmail.com>
-- Stability   : experimental
-- Portability : non-portable (GHC extensions)
--

module Data.Array.Accelerate.Pretty.Schedule (
  PrettySchedule(..), PrettyKernel(..)
) where

import Data.Array.Accelerate.AST.Kernel
import Data.Array.Accelerate.Pretty.Exp

class PrettySchedule sched where
  prettySchedule :: PrettyKernel kernel => sched kernel () t -> Adoc

class PrettyKernel kernel where
  prettyKernel :: Val env -> kernel env -> Adoc
