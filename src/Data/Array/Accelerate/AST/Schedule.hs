{-# LANGUAGE AllowAmbiguousTypes  #-}
{-# LANGUAGE CPP                  #-}
{-# LANGUAGE ConstraintKinds      #-}
{-# LANGUAGE FlexibleContexts     #-}
{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE GADTs                #-}
{-# LANGUAGE InstanceSigs         #-}
{-# LANGUAGE LambdaCase           #-}
{-# LANGUAGE OverloadedStrings    #-}
{-# LANGUAGE PatternGuards        #-}
{-# LANGUAGE RankNTypes           #-}
{-# LANGUAGE ScopedTypeVariables  #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE TypeApplications     #-}
{-# LANGUAGE TypeOperators        #-}
{-# LANGUAGE TypeFamilies         #-}
{-# LANGUAGE ViewPatterns         #-}

-- |
-- Module      : Data.Array.Accelerate.AST.Schedule
-- Copyright   : [2012..2020] The Accelerate Team
-- License     : BSD3
--
-- Maintainer  : Trevor L. McDonell <trevor.mcdonell@gmail.com>
-- Stability   : experimental
-- Portability : non-portable (GHC extensions)
--
-- This module defines the interface for schedules, to be implemented
-- in other modules.
--

module Data.Array.Accelerate.AST.Schedule (
  IsSchedule(..),
  convertSchedule,
  Scheduled,
  reprIsBody,
) where

import Data.Array.Accelerate.AST.Partitioned
import Data.Array.Accelerate.AST.Kernel
import Data.Array.Accelerate.Type
import Data.Array.Accelerate.Representation.Type
import Data.Typeable                                                ( (:~:)(..) )
import Data.Array.Accelerate.AST.Operation

class IsSchedule sched where
  -- 'a' is a ground type (ie, can be represented using GroundR)
  type ScheduleInput  sched a
  type ScheduleOutput sched a

  rnfSchedule :: NFData' kernel => sched kernel env t -> ()

  convertScheduleFun
    :: IsKernel kernel
    => PartitionedAfun (KernelOperation kernel) () t -> sched kernel () (Scheduled sched t)


convertSchedule
  :: forall sched kernel t.
     (IsSchedule sched, IsKernel kernel)
  => PartitionedAcc (KernelOperation kernel) () t -> sched kernel () (ScheduleOutput sched t -> ())
convertSchedule acc
  | Refl <- reprIsBody @sched $ groundsR acc = convertScheduleFun (Abody acc)

type family Scheduled sched a where
  Scheduled sched (a -> b) = ScheduleInput  sched a -> Scheduled sched b
  Scheduled sched a        = ScheduleOutput sched a -> ()

reprIsBody :: forall sched t. GroundsR t -> Scheduled sched t :~: (ScheduleOutput sched t -> ())
reprIsBody TupRunit = Refl
reprIsBody TupRpair{} = Refl
reprIsBody (TupRsingle (GroundRbuffer _)) = Refl
reprIsBody (TupRsingle (GroundRscalar (VectorScalarType _))) = Refl
reprIsBody (TupRsingle (GroundRscalar (SingleScalarType (NumSingleType t)))) = case t of
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
