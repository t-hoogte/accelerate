{-# LANGUAGE CPP                  #-}
{-# LANGUAGE ConstraintKinds      #-}
{-# LANGUAGE FlexibleContexts     #-}
{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE GADTs                #-}
{-# LANGUAGE InstanceSigs         #-}
{-# LANGUAGE KindSignatures       #-}
{-# LANGUAGE LambdaCase           #-}
{-# LANGUAGE OverloadedStrings    #-}
{-# LANGUAGE PatternGuards        #-}
{-# LANGUAGE RankNTypes           #-}
{-# LANGUAGE ScopedTypeVariables  #-}
{-# LANGUAGE TypeApplications     #-}
{-# LANGUAGE TypeOperators        #-}
{-# LANGUAGE ViewPatterns         #-}

-- |
-- Module      : Data.Array.Accelerate.Trafo.NewNewFusion
-- Copyright   : [2012..2020] The Accelerate Team
-- License     : BSD3
--
-- Maintainer  : Trevor L. McDonell <trevor.mcdonell@gmail.com>
-- Stability   : experimental
-- Portability : non-portable (GHC extensions)
--
-- This module should implement fusion.
--

module Data.Array.Accelerate.Trafo.NewNewFusion (

  convertAcc,  convertAccWith,
  convertAfun, convertAfunWith,

) where

import Data.Array.Accelerate.AST.Operation
import Data.Array.Accelerate.AST.Partitioned
import Data.Array.Accelerate.Trafo.Config
import Data.Array.Accelerate.Error

import Data.Array.Accelerate.Debug.Flags                ( array_fusion )
import qualified Data.Array.Accelerate.Debug.Stats      as Stats
import Data.Kind
#ifdef ACCELERATE_DEBUG
import System.IO.Unsafe -- for debugging
#endif


-- Array Fusion
-- ============

class FusibleAcc (op :: Type -> Type) where

-- | Apply the fusion transformation to a de Bruijn AST
--
convertAcc
    :: HasCallStack
    => Config
    -> OperationAcc op benv a
    -> PartitionedAcc op benv a
convertAcc _ =  withSimplStats $ mapAccExecutable dontFuse

convertAccWith :: HasCallStack => Config -> OperationAcc op benv a -> PartitionedAcc op benv a
convertAccWith config = convertAcc config

-- | Apply the fusion transformation to a function of array arguments
--
convertAfun :: HasCallStack => Config -> OperationAfun op benv f -> PartitionedAfun op benv f
convertAfun _ = withSimplStats $ mapAfunExecutable dontFuse

convertAfunWith :: HasCallStack => Config -> OperationAfun op benv f -> PartitionedAfun op benv f
convertAfunWith config = convertAfun config

withSimplStats :: a -> a
#ifdef ACCELERATE_DEBUG
withSimplStats x = unsafePerformIO Stats.resetSimplCount `seq` x
#else
withSimplStats x = x
#endif

dontFuse :: Execute op benv -> Cluster op benv
dontFuse = undefined 