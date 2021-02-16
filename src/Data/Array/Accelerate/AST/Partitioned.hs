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
import Data.Array.Accelerate.AST.Environment


data Cluster op args where
  Leaf :: op args -> Cluster op args

  Node :: Cluster op a
       -> Cluster op   b
       -> Combine    a b c
       -> Cluster op     c

  Reorder :: SwapArgs args args'
          -> Cluster op args
          -> Cluster op args'

  -- | Not a true weakening: that would imply adding inputs and/or removing outputs.
  -- This 'weakening' only adds arguments, in and/or out, to the phantom types.
  -- Maybe think of a different name for it :)
  Weaken :: args :> args' -- TODO replace with an Arg-level weakening
         -> Cluster op args'
         -> Cluster op args

-- Note that, in general, these combination descriptors can definitely represent
-- undesirable states: It's probably not doable to encode all fusability rules
-- in the types (especially while abstracting over backends), instead we will need
-- to call `error "impossible fusion"` in the backends at some points (particularly codegen).

-- | All these options will, in general, require the underlying Clusters to be weakened
-- by adding superfluous Args. The constructors below are the only way to "remove Args".
data Combine a b c where
  -- An array is produced and consumed, fusing it away.
  -- NOTE: this means that the array does not appear in the environment, and
  -- it does not have an accompanying `Arg` constructor: Its scope is now
  -- bound by this `Vertical` constructor.
  Vertical   :: Combine (Out sh e -> a) (In sh e -> a)               a

  -- Like vertical, but the `Array sh e` is stored for later use
  Diagonal   :: Combine (Out sh e -> a) (In  sh e -> a) (Out sh e -> a)

  -- Both outputs are stored. Because of the weakening, this combination is trivial.
  Horizontal :: Combine a a a


type PartitionedAcc  op = PreOpenAcc  (Cluster op)
type PartitionedAfun op = PreOpenAfun (Cluster op)

-- Re-order the type level arguments, to align them for the fusion constructors.
-- pray we won't need it, fear we might, hope it doesn't complicate things
data SwapArgs a b where
  -- Switch the first two arguments. This might be all we need, but probably not..
  Swap :: SwapArgs (a -> b -> x) (b -> a -> x)

  -- Alternatively, we could need constructors traversing the whole type, something like these:
  Start :: SwapArgs () ()
  Dig :: SwapArgs a b -> SwapArgs (x -> a) (x -> b)
  Swap' :: SwapArgs a (x -> y -> z)
        -> SwapArgs a (y -> x -> z)
  SSwap :: SwapArgs a b -> SwapArgs b c -> SwapArgs a c
