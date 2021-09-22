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
import Data.Array.Accelerate.Trafo.Partitioning.ILP (gurobiFusion)
import Data.Array.Accelerate.Trafo.Partitioning.ILP.Graph (MakesILP, incr)
import Data.Array.Accelerate.Trafo.Partitioning.ILP.Labels (LabelEnv (LabelEnvNil))


#ifdef ACCELERATE_DEBUG
import System.IO.Unsafe -- for debugging
#endif

-- Array Fusion
-- ============

-- | Apply the fusion transformation to a de Bruijn AST
--
convertAccWith
    :: (HasCallStack, MakesILP op)
    => Config
    -> OperationAcc op () a
    -> PartitionedAcc op () a
convertAccWith config = convertAccWith' config LabelEnvNil

convertAccWith' 
    :: (HasCallStack, MakesILP op)
    => Config
    -> LabelEnv env
    -> OperationAcc op env a
    -> PartitionedAcc op env a
convertAccWith' _ = withSimplStats gurobiFusion

convertAcc :: (HasCallStack, MakesILP op) => OperationAcc op () a -> PartitionedAcc op () a
convertAcc = convertAccWith defaultOptions

-- | Apply the fusion transformation to a function of array arguments
--
convertAfun :: (HasCallStack, MakesILP op) => OperationAfun op () f -> PartitionedAfun op () f
convertAfun = convertAfunWith defaultOptions

convertAfunWith :: (HasCallStack, MakesILP op) => Config -> OperationAfun op () f -> PartitionedAfun op () f
convertAfunWith config = go LabelEnvNil
  where
    go :: MakesILP op => LabelEnv env -> OperationAfun op env f -> PartitionedAfun op env f
    go env (Abody acc) = Abody $ convertAccWith' config env acc
    go env (Alam lhs fun) = Alam lhs $ go (incr lhs env) fun


withSimplStats :: a -> a
#ifdef ACCELERATE_DEBUG
withSimplStats x = unsafePerformIO Stats.resetSimplCount `seq` x
#else
withSimplStats x = x
#endif

dontFuse :: op args -> Args env args -> Cluster op args
dontFuse = unfused
