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
module Data.Array.Accelerate.AST.Partitioned where

import Data.Array.Accelerate.AST.Operation

import Prelude hiding ( take )
import Data.Bifunctor (second)
import Data.Array.Accelerate.Trafo.Partitioning.ILP.Labels



type PartitionedAcc  op = PreOpenAcc  (Cluster op)
type PartitionedAfun op = PreOpenAfun (Cluster op)

-- | A cluster of operations, in total having `args` as signature
data Cluster op args where
  Cluster :: ClusterIO args input output
          -> ClusterAST op  input output
          -> Cluster op args

-- | Internal AST of `Cluster`, simply a list of let-bindings.
data ClusterAST op env result where
  None :: ClusterAST op env env
  -- `Bind _ x y` reads as `x; y`
  Bind :: LeftHandSideArgs body env scope
       -> op body
       -> ClusterAST op scope result
       -> ClusterAST op env   result

-- | `xargs` is a type-level list with function seperators,
-- which contains `x`. Removing `x` from `xargs` yields `args`.
data Take x xargs args where
  Here  :: Take x (x ->  args)       args
  There :: Take x       xargs        args
        -> Take x (y -> xargs) (y -> args)

-- | A version of `LeftHandSide` that works on the function-separated environments: 
-- Given environment `env`, we can execute `body`, yielding environment `scope`.
data LeftHandSideArgs body env scope where
  Base :: LeftHandSideArgs () args args
  
  -- The body creates an array
  Make :: Take (Out sh e) body' body
       -> LeftHandSideArgs body  env             scope
       -> LeftHandSideArgs body' env (In sh e -> scope)
       
  -- The body has an input
  Reqr :: Take (In sh e) body' body
       -> LeftHandSideArgs body              env              scope
       -> LeftHandSideArgs body' (In sh e -> env) (In sh e -> scope)

data ClusterIO args input output where
  Empty  :: ClusterIO () () output
  Input  :: Take (In sh e) einput input
         -> ClusterIO             args   input output
         -> ClusterIO (In sh e -> args) einput output
  Output :: Take (In sh e) eoutput output
         -> ClusterIO              args  input  output
         -> ClusterIO (Out sh e -> args) input eoutput

unfused :: op args -> Args env args -> Cluster op args
unfused op args = io args $ \inout -> Cluster inout (Bind lhs op None)
  where 
    lhs = undefined

io :: Args env args -> (forall x y. ClusterIO args x y -> r) -> r
io ArgsNil f = f Empty
io (ArgArray In  _ _ _ :>: xs) f = io xs $ \res -> f (Input  Here res)
io (ArgArray Out _ _ _ :>: xs) f = io xs $ \res -> f (Output Here res)
io _ _ = error "todo: make non-array arguments flow like In arrays cleanly"


take :: Take x xc c -> Args env xc -> (Arg env x, Args env c)
take Here      (x :>: xs) = (x, xs)
take (There t) (x :>: xs) = second (x :>:) $ take t xs

labelledTake :: Take x xc c -> LabelArgs xc -> (ALabels x, LabelArgs c)
labelledTake Here      (x :>>: xs) = (x, xs)
labelledTake (There t) (x :>>: xs) = second (x :>>:) $ labelledTake t xs


put :: Take x xc c -> (Arg env x, Args env c) -> Args env xc
put Here       (x, xs) = x :>: xs
put (There t') (x, y :>: xs) = y :>: put t' (x, xs)

