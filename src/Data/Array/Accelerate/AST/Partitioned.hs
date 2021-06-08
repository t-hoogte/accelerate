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
  , Cluster(..), Combine(..)
  , PartitionedAcc, PartitionedAfun
  , SwapArgs(..), Take(..)
  , swapArgs, swapArgs'
  , put, take'
  , combineArgs,labelledTake,liftSwap) where

import Data.Array.Accelerate.AST.Operation

import Control.Category ( Category(..) )
import Prelude hiding (id, (.))
import Data.Bifunctor (second)
import Data.Array.Accelerate.Trafo.Partitioning.ILP.Labels

type PartitionedAcc  op = PreOpenAcc  (Cluster op)
type PartitionedAfun op = PreOpenAfun (Cluster op)

-- data Cluster op args where
--   Leaf :: op args -> Cluster op args
--   ConsCluster :: op a'
--               -> SwapArgs a' a
--               -> Combine     a b c
--               -> Cluster op    b
--               -> Cluster op      c

-- | These definitions are far from guaranteeing a unique representation;
-- there are many equivalent ways to represent a clustering, even ignoring
-- the ambiguity in SwapArgs (where you can make many convoluted versions
-- of `id`). I don't think this is a big deal, but since it seems to always
-- be possible to construct a Cluster by appending a single element at a time,
-- it might be better to refactor this into a pseudo list (instead of binary tree).
-- Even then, every topologically sorted order will be a valid sequence.
data Cluster op args where
  -- Currently, we only swapArgs the order of the arguments at the leaves. 
  -- This is needed to be able to horizontally fuse (x -> y -> a) with (y -> x -> a).
  -- I think it is also sufficient to do it only at leaves, and not in every node.
  -- Maybe putting it in the nodes will turn out to be easier though!
  Leaf :: op args'
       -> SwapArgs args args'
       -> Cluster op args

  -- Fuse two clusters.
  Branch :: Cluster op a
         -> Cluster op   b
         -> Combine    a b c
         -> Cluster op     c

-- Note that, in general, these combination descriptors can definitely represent
-- undesirable states: It's probably not doable to encode all fusability rules
-- in the types (especially while abstracting over backends), instead we will need
-- to call `error "impossible fusion"` in the backends at some points (particularly codegen).

-- | All these options will, in general, require the underlying Clusters to be weakened
-- by adding superfluous Args. The constructors below are the only way to "remove Args".
data Combine left right result where
  Combine :: Combine () () ()
  -- An array is produced and consumed, fusing it away.
  -- NOTE: this means that the array does not appear in the environment, and
  -- it does not have an accompanying `Arg` constructor: Its scope is now
  -- bound by this `Node` constructor in `Cluster`.
  Vertical  :: Combine              a              b               c
            -> Combine (Out sh e -> a) (In sh e -> b)              c

  -- Like vertical, but the arg is stored for later use
  Diagonal  :: Combine              a              b               c
            -> Combine (Out sh e -> a) (In sh e -> b) (Out sh e -> c)

  -- Both computations use the argument in the same fashion.
  -- Note that you can't recreate this type using WeakLeft and WeakRight,
  -- as that would duplicate the argument in the resulting type.
  -- Note also that it doesn't make too much sense to horizontally fuse output arguments.
  Horizontal :: Combine       a        b        c
             -> Combine (In sh e -> a) (In sh e -> b) (In sh e -> c)

  -- Only the right computation uses x, so this 'weakens' the left computation
  WeakLeft  :: Combine       a        b         c
            -> Combine       a (x  -> b) (x  -> c)
  -- Mirror of WeakLeft
  WeakRight :: Combine       a        b         c
            -> Combine (x -> a)       b  (x  -> c)

-- Re-order the type level arguments, to align them for the fusion constructors.
data SwapArgs a b where
  -- no swapping, base case
  Start :: SwapArgs a a
  -- put x on top of a recursive swapArgs
  Swap  :: SwapArgs a xb
        -> Take x xb b
        -> SwapArgs a (x -> b)

-- neat, but is it actually useful?
instance Category SwapArgs where
  id  = Start
  (.) = flip composeSwap

data Take x xa a where
  -- base case
  Here  :: Take x (x -> a) a
  -- recursive case
  There :: Take x       xa        a
        -> Take x (y -> xa) (y -> a)

composeSwap :: forall a b c. SwapArgs a b -> SwapArgs b c -> SwapArgs a c
composeSwap x = go
  where go :: SwapArgs b x -> SwapArgs a x
        -- If the second SwapArgs is identity, return x
        go Start = x
        -- Otherwise, the second SwapArgs puts something in front.
        -- Recurse, then wrap that in a Swap which puts the same thing in front!
        go (Swap a b) = Swap (go a) b

----------------

-- | Given two Args, make the one corresponding to the fused cluster.
combineArgs :: Combine a b c -> Args env a -> Args env b -> Args env c
combineArgs Combine        ArgsNil  ArgsNil  = ArgsNil
  -- The only option which throws away an Arg! It is fused away.
combineArgs (Vertical   c) (_:>:as) (_:>:bs) =       combineArgs c as bs
  -- For Diagonal and Horizontal, we assume that `a` and `b` are the same Arg.
combineArgs (Diagonal   c) (a:>:as) (_:>:bs) = a :>: combineArgs c as bs
combineArgs (Horizontal c) (a:>:as) (_:>:bs) = a :>: combineArgs c as bs
combineArgs (WeakLeft   c)      as  (b:>:bs) = b :>: combineArgs c as bs
combineArgs (WeakRight  c) (a:>:as)      bs  = a :>: combineArgs c as bs

-- | Do the swap thing
swapArgs :: forall env a b. SwapArgs a b -> Args env a -> Args env b
swapArgs Start = id
swapArgs (Swap s t) = uncurry (:>:) . take' t . swapArgs s

take' :: Take x xc c -> Args env xc -> (Arg env x, Args env c)
take' Here      (x :>: xs) = (x, xs)
take' (There t) (x :>: xs) = second (x :>:) $ take' t xs

labelledTake :: Take x xc c -> LabelArgs xc -> (ALabels x, LabelArgs c)
labelledTake Here      (x :>>: xs) = (x, xs)
labelledTake (There t) (x :>>: xs) = second (x :>>:) $ labelledTake t xs

-- | Inverse of `swapArgs`
swapArgs' :: forall env a b. SwapArgs b a -> Args env a -> Args env b
swapArgs' Start = id
swapArgs' (Swap s t) = swapArgs' s . put t . \(x :>: xs) -> (x, xs)

put :: Take x xc c -> (Arg env x, Args env c) -> Args env xc
put Here       (x, xs) = x :>: xs
put (There t') (x, y :>: xs) = y :>: put t' (x, xs)


-- Simpler definition which is 'semantically equivalent' 
-- (when plugged into swapArgs or swapArgs') but explodes 
-- in the size of the SwapArgs:
--  > liftSwap Start = Start
--  > liftSwap (Swap s t) = Swap (Swap (liftSwap s) (There t)) (There Here)
-- That version lifts each Take, and brings `x` forward every time.
-- This version instead keeps track of where `x` ends up after only lifting
-- each Take, and puts it at the top all the way at the end.
-- The difference becomes clear when you repeatedly apply this function to
-- lift through some layers (:: SwapArgs a b -> SwapArgs (x->y->z->a) (x->y->z->b))
-- (as happens in `Clustering`): The simple version multiplies the size by 2^n, 
-- while the below version adds n There's to each Take and adds n Swaps in front.
-- Note that this algorithm is linear in the size of SwapArgs (which can be quadratic in its depth)
liftSwap :: SwapArgs a b -> SwapArgs (x -> a) (x -> b)
liftSwap s = case go s of LSA s' acc -> Swap s' acc
  where
    go :: SwapArgs a b -> LiftSwapAcc a b x
    go Start = LSA Start Here
    go (Swap s' t) = case go s' of
      LSA s'' acc -> case goPast t acc of
        GP t' acc' -> LSA (Swap s'' t') (There acc')

    goPast :: Take x bx b -> Take y bxy bx -> GoPast x y b bx bxy
    goPast x Here = GP (There x) Here
    goPast Here (There y) = GP Here y
    goPast (There x) (There y) = case goPast x y of
      GP a b -> GP (There a) (There b)

-- Internal datatypes for existential reasons
data LiftSwapAcc a b x = forall bx. LSA (SwapArgs (x -> a) bx) (Take x bx b)
data GoPast x y b bx bxy = forall by. GP (Take x bxy by) (Take y by b)

