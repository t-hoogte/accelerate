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



type PartitionedAcc  op = PreOpenAcc  (Cluster op)
type PartitionedAfun op = PreOpenAfun (Cluster op)

-- | A cluster of operations, in total having `args` as signature
data Cluster op args where
  Cluster :: ClusterIO args input output
          -> ClusterAST op  input output
          -> Cluster op args

-- | Internal AST of `Cluster`, simply a list of let-bindings.
-- Note that all environments hold scalar values, not arrays!
data ClusterAST op env result where
  None :: ClusterAST op env env
  -- `Bind _ x y` reads as `do x; in the resulting environment, do y`
  Bind :: LeftHandSideArgs body env scope
       -> op body
       -> ClusterAST op scope result
       -> ClusterAST op env   result

-- | A version of `LeftHandSide` that works on the function-separated environments: 
-- Given environment `env`, we can execute `body`, yielding environment `scope`.
data LeftHandSideArgs body env scope where
  -- Because 
  Base :: LeftHandSideArgs () args args
  -- The body has an input array
  Reqr :: LeftHandSideArgs              body   env      scope
       -> LeftHandSideArgs (In  sh e -> body) (env, e) (scope, e)
  -- The body creates an array
  Make :: LeftHandSideArgs              body   env      scope
       -> LeftHandSideArgs (Out sh e -> body)  env     (scope, e)
  -- One array that is both input and output
  Adju :: LeftHandSideArgs              body   env      scope
       -> LeftHandSideArgs (Mut sh e -> body) (env, e) (scope, e)
  -- Holds `Var' e`, `Exp' e`, `Fun' e`: The non-array Arg options.
  -- Behaves like `In` arguments.
  EArg :: LeftHandSideArgs              body   env      scope
       -> LeftHandSideArgs (       e -> body) (env, e) (scope, e)
  -- Does nothing to this part of the environment
  Ignr :: LeftHandSideArgs              body   env      scope
       -> LeftHandSideArgs              body  (env, e) (scope, e)

data ClusterIO args input output where
  Empty  :: ClusterIO () () output
  Input  :: ClusterIO              args   input      output
         -> ClusterIO (In  sh e -> args) (input, e) (output, e)
  Output :: Take e eoutput output
         -> ClusterIO              args   input      output
         -> ClusterIO (Out sh e -> args)  input     eoutput
  MutPut :: Take e eoutput output
         -> ClusterIO              args   input      output
         -> ClusterIO (Mut sh e -> args) (input, e) eoutput
  -- Contract: Only use this for `Var`, `Exp`, `Fun` args;
  -- don't abuse as backdoor with in/out/mut
  ExpPut :: ClusterIO              args   input      output
         -> ClusterIO (       e -> args) (input, e) (output, e)

-- A cluster from a single node
unfused :: op args -> Args env args -> Cluster op args
unfused op args = iolhs args $ \io lhs -> Cluster io (Bind lhs op None)

iolhs :: Args env args -> (forall x y. ClusterIO args x y -> LeftHandSideArgs args x y -> r) -> r
iolhs ArgsNil                     f =                       f  Empty            Base
iolhs (ArgArray In  _ _ _ :>: as) f = iolhs as $ \io lhs -> f (Input       io) (Reqr lhs)
iolhs (ArgArray Out _ _ _ :>: as) f = iolhs as $ \io lhs -> f (Output Here io) (Make lhs)
iolhs (ArgArray Mut _ _ _ :>: as) f = iolhs as $ \io lhs -> f (MutPut Here io) (Adju lhs)
iolhs (_                  :>: as) f = iolhs as $ \io lhs -> f (ExpPut      io) (EArg lhs)




-- | `xargs` is a type-level list which contains `x`. 
-- Removing `x` from `xargs` yields `args`.
data Take x xargs args where
  Here  :: Take x (args, x)       args
  There :: Take x  xargs      args
        -> Take x (xargs, y) (args, y)

-- for the old version of Take (using `->` instead of `(,)`):

-- take :: Take x xc c -> Args env xc -> (Arg env x, Args env c)
-- labelledTake :: Take x xc c -> LabelArgs xc -> (ALabels x, LabelArgs c)
-- take         Here      (x :>:  xs) = (x, xs)
-- take         (There t) (x :>:  xs) = second (x :>:)  $ take t xs
-- labelledTake Here      (x :>>: xs) = (x, xs)
-- labelledTake (There t) (x :>>: xs) = second (x :>>:) $ labelledTake t xs

-- put :: Take x xc c -> (Arg env x, Args env c) -> Args env xc
-- put Here      (x,       xs) = x :>: xs
-- put (There t) (x, y :>: xs) = y :>: put t (x, xs)

