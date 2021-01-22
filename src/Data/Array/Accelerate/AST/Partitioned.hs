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
  , Cluster(..)
  , PartitionedAcc
  , PartitionedAfun
  ) where

import Data.Array.Accelerate.AST.Operation hiding ( OperationAcc, Execute(..) )


-- `Cluster` replaces `Execute` during the fusion pass: 
--    PreOpenAcc (Execute op) 
-- -> PreOpenAcc (Cluster op)

-- As a refresh, `Execute` is currently defined as:
-- data Execute op env where
--   Execute :: op args -> Args env args -> Execute op env

data Cluster op env where
  Root :: ClusterTree op args -> Args env args -> Cluster op env

instance IsExecutableAcc (Cluster op) where
  reindexExecPartial k (Root op args) = Root op <$> reindexArgs k args
  execVars (Root _ args) = argsVars args

    -- Could even abstract one more step (will do once we settle on ClusterTree)

    -- data Foo f (op :: Type -> Type) env where
    --   Foo :: f op args -> Args env args -> Foo f op env

    -- data Identity a b = Identity (a b)
    -- data Bar a b = Bar Int (a b)

    -- type Execute' = Foo Identity
    -- type LabelledExecute = Foo Bar -- as input to the ILP, give each Execute a unique (Int) label.
    -- type Cluster' = Foo ClusterTree

    -- instance IsExecutableAcc (Foo f op) where
    --   reindexExecPartial k (Foo fop args) = Foo fop <$> reindexArgs k args
    --   execVars (Foo _ args) = argsVars args




data ClusterTree op args where
  Leaf :: op args -> ClusterTree op args

  Node :: ClusterTree op a
       -> ClusterTree op   b
       -> Combine        a b c
       -> ClusterTree op     c

  Reorder :: SwapArgs args args'
          -> ClusterTree op args
          -> ClusterTree op args'

-- Note that, in general, these combination descriptors can definitely represent
-- undesirable states: It's probably not doable to encode all fusability rules
-- in the types (especially while abstracting over backends), instead we will need
-- to call `error "impossible fusion"` in the backends at some points (particularly codegen).
-- maybe should inline the three options?
data Combine a b c = CVertical   (Vertical   a b c)
                   | CHorizontal (Horizontal a b c)
                   | CDiagonal   (Diagonal   a b c)

-- Proof that `first` can fuse before `second`, giving result type `total`.
data Vertical first second total where
  -- An array is produced and consumed, fusing it away.
  -- NOTE: this means that the array does not appear in the environment, and
  -- it does not have an accompanying `Arg` constructor: Its scope is now
  -- bound by this `Vertical` constructor.
  Vertical :: Vertical (Out sh e -> a) (In sh e -> a) a

data Horizontal left right total where
  -- Both outputs are stored. We purposely don't require sh1 == sh2, but the rest of the types
  -- need to align, so this is why we need weakening.
  Horizontal :: Horizontal (Out sh1 e1 -> a) (Out sh2 e2 -> a) (Out sh1 e1 -> Out sh2 e2 -> a)

data Diagonal first second total where
  -- Like vertical, but the `Array sh e` is stored for later use
  Diagonal :: Diagonal (Out sh e -> a) (In  sh e -> a) (Out sh e -> a)


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
