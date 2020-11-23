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
{-# OPTIONS_GHC -Wno-unused-binds #-} -- for a more pleasant IDE experience :)
module Data.Array.Accelerate.AST.Partitioned ( module Data.Array.Accelerate.AST.Operation, Cluster(..), PartitionedAcc, PartitionedAfun ) where

import Data.Array.Accelerate.AST.Operation hiding ( OperationAcc, Execute(..) )

-- replaces 'Execute' during the fusion ILP pass: PreOpenAcc (Execute op) -> PreOpenAcc (Cluster op)
newtype Cluster op env = Root (forall args. ClusterTree op env args)

data ClusterTree op env args where
  Leaf :: op args -> Args env args -> ClusterTree op env args

  Node :: ClusterTree op env a
       -> ClusterTree op env b
       -> Combine a b c
       -> ClusterTree op env c

data Combine a b c = Vertical   (Vertical   a b c)
                   | Horizontal (Horizontal a b c)
                   | Diagonal   (Diagonal   a b c)

-- Proof that `first` can fuse before `second`, giving result type `total`.
data Vertical first second total where
  -- The canonical case: the `Array sh e` is produced and consumed.
  OutVertical :: Vertical (Out sh e -> a) (In  sh e -> a) a
  MutVertical :: Vertical (Mut sh e -> a) (In  sh e -> a) a

  -- Does this need induction?
  -- InductVertical  :: Vertical f s t
  --                 -> Vertical (In  sh e -> f) (In  sh e -> s) (In  sh e -> t)
  -- OutductVertical :: Vertical f s t
  --                 -> Vertical (Out sh e -> f) (Out sh e -> s) (Out sh e -> t)
  -- MutductVertical :: Vertical f s t
  --                 -> Vertical (Mut sh e -> f) (Mut sh e -> s) (Mut sh e -> t)

data Horizontal left right total where
  -- Both outputs are stored. We can't neccesarily relate the shapes to eachother here.
  ReallyHorizontal :: Horizontal (Out sh1 e1 -> a) (Out sh2 e2 -> a) (Out sh1 e1 -> Out sh2 e2 -> a)
  -- Safely fusing `Mut` horizontally sounds like a minefield, so skipping until that seems needed

data Diagonal first second total where
  -- Like the canonical vertical case, but the `Array sh e` is stored for later use
  OutDiagonal :: Diagonal (Out sh e -> a) (In  sh e -> a) (Out sh e -> a)
  MutDiagonal :: Diagonal (Mut sh e -> a) (In  sh e -> a) (Mut sh e -> a)

-- todo
-- instance IsExecutableAcc (Cluster op)

type PartitionedAcc  op = PreOpenAcc  (Cluster op)
type PartitionedAfun op = PreOpenAfun (Cluster op)
