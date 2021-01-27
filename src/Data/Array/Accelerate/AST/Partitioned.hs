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

{-# OPTIONS_GHC -Wno-unused-binds #-} -- remove later, I don't like seeing the warnings now

-- |
-- Module      : Data.Array.Accelerate.AST.Partitioned
-- Copyright   : [2008..2020] The Accelerate Team
-- License     : BSD3
--
-- Maintainer  : Trevor L. McDonell <trevor.mcdonell@gmail.com>
-- Stability   : experimental
-- Portability : non-portable (GHC extensions)
--
module Data.Array.Accelerate.AST.Partitioned 
  ( module Data.Array.Accelerate.AST.Operation
  , Cluster(..), Combine(..), SwapArgs(..)
  , PartitionedAcc, PartitionedAfun
  ) where

import Data.Array.Accelerate.AST.Operation


data Cluster op args where
  Leaf :: op args -> Cluster op args

  Node :: Cluster op a
       -> Cluster op   b
       -> Combine    a b c
       -> Cluster op     c

  Reorder :: SwapArgs args args'
          -> Cluster op args
          -> Cluster op args'

-- Note that, in general, these combination descriptors can definitely represent
-- undesirable states: It's probably not doable to encode all fusability rules
-- in the types (especially while abstracting over backends), instead we will need
-- to call `error "impossible fusion"` in the backends at some points (particularly codegen).

data Combine a b c where
  -- An array is produced and consumed, fusing it away.
  -- NOTE: this means that the array does not appear in the environment, and
  -- it does not have an accompanying `Arg` constructor: Its scope is now
  -- bound by this `Vertical` constructor.
  Vertical   :: Combine (Out sh e -> a) (In sh e -> a)               a
  
  -- Like vertical, but the `Array sh e` is stored for later use
  Diagonal   :: Combine (Out sh e -> a) (In  sh e -> a) (Out sh e -> a)
  
  -- Both outputs are stored. We purposely don't require sh1 == sh2, but the rest of the types
  -- need to align, so this is why we need weakening.
  -- TODO: perhaps this type is too strict, and we'll want to horizontally fuse two clusters
  -- with multiple out-variables.
  Horizontal :: Combine (Out sh1 e1 -> a) (Out sh2 e2 -> a) (Out sh1 e1 -> Out sh2 e2 -> a)


type PartitionedAcc  op = PreOpenAcc  (Cluster op)
type PartitionedAfun op = PreOpenAfun (Cluster op)

-- Re-order the type level arguments, to align them for the fusion constructors.
-- pray we won't need it, fear we might, hope it doesn't complicate things
data SwapArgs a b where
  -- Switch the first two arguments. This might be all we need, but probably not..
  Swap :: SwapArgs (a -> b -> x) (b -> a -> x)

  -- Alternatively, we would need constructors traversing the whole type, something like these:
  Start :: SwapArgs () ()
  Dig :: SwapArgs a b -> SwapArgs (x -> a) (x -> b)
  Swap' :: SwapArgs a (x -> y -> z)
        -> SwapArgs a (y -> x -> z)
