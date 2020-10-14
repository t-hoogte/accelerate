{-# LANGUAGE BangPatterns          #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE LambdaCase            #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE TemplateHaskell       #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE TypeOperators         #-}
{-# OPTIONS_HADDOCK hide #-}
-- |
-- Module      : Data.Array.Accelerate.AST.Partitioned
-- Copyright   : [2008..2020] The Accelerate Team
-- License     : BSD3
--
-- Maintainer  : Trevor L. McDonell <trevor.mcdonell@gmail.com>
-- Stability   : experimental
-- Portability : non-portable (GHC extensions)
--

module Data.Array.Accelerate.AST.Partitioned ( module Data.Array.Accelerate.AST.Operation, Cluster(..), PartitionedAcc, PartitionedAfun ) where

import Data.Array.Accelerate.AST.Operation hiding ( OperationAcc, Execute(..) )

data Cluster op env where
  Base :: op args -> Args env args -> Cluster op env
  -- TODO: Vertical, Horizontal, Diagonal

instance IsExecutableAcc (Cluster op) where
  reindexExecPartial k (Base op args) = Base op <$> reindexArgs k args
  execVars (Base _ args) = argsVars args

type PartitionedAcc  op = PreOpenAcc  (Cluster op)
type PartitionedAfun op = PreOpenAfun (Cluster op)
