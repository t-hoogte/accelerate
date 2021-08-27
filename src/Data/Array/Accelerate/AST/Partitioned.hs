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
{-# LANGUAGE TupleSections #-}

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
import Data.Bifunctor



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
  -- Because of `Ignr`, we could also give this the type `LeftHandSideArgs () () ()`.
  Base :: LeftHandSideArgs () () ()
  -- The body has an input array
  Reqr :: Take e eenv env -> Take e escope scope
       -> LeftHandSideArgs              body   env      scope
       -> LeftHandSideArgs (In  sh e -> body) eenv     escope
  -- The body creates an array
  Make :: Take e escope scope
       -> LeftHandSideArgs              body   env      scope
       -> LeftHandSideArgs (Out sh e -> body)  env     escope
  -- One array that is both input and output
  Adju :: Take e eenv env -> Take e escope scope
       -> LeftHandSideArgs              body   env      scope
       -> LeftHandSideArgs (Mut sh e -> body) eenv     escope
  -- TODO: duplicate for Var' and Fun'
  EArg :: LeftHandSideArgs              body   env      scope
       -> LeftHandSideArgs (Exp'   e -> body) (env, e) (scope, e)
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
  -- TODO: duplicate for Var' and Fun'
  ExpPut :: ClusterIO              args   input      output
         -> ClusterIO (Exp'   e -> args) (input, e) (output, e)

-- | `xargs` is a type-level list which contains `x`. 
-- Removing `x` from `xargs` yields `args`.
data Take x xargs args where
  Here  :: Take x ( args, x)  args
  There :: Take x  xargs      args
        -> Take x (xargs, y) (args, y)

        
-- A cluster from a single node
unfused :: op args -> Args env args -> Cluster op args
unfused op args = iolhs args $ \io lhs -> Cluster io (Bind lhs op None)

iolhs :: Args env args -> (forall x y. ClusterIO args x y -> LeftHandSideArgs args x y -> r) -> r
iolhs ArgsNil                     f =                       f  Empty            Base
iolhs (ArgArray In  _ _ _ :>: as) f = iolhs as $ \io lhs -> f (Input       io) (Reqr Here Here lhs)
iolhs (ArgArray Out _ _ _ :>: as) f = iolhs as $ \io lhs -> f (Output Here io) (Make Here lhs)
iolhs (ArgArray Mut _ _ _ :>: as) f = iolhs as $ \io lhs -> f (MutPut Here io) (Adju Here Here lhs)
iolhs (ArgExp _           :>: as) f = iolhs as $ \io lhs -> f (ExpPut      io) (EArg lhs)
iolhs _ _ = undefined -- TODO Var', Fun'

mkBase :: ClusterIO args i o -> LeftHandSideArgs () i i
mkBase Empty = Base
mkBase (Input ci) = Ignr (mkBase ci)
mkBase (Output _ ci) = mkBase ci
mkBase (MutPut _ ci) = Ignr (mkBase ci)
mkBase (ExpPut ci) = Ignr (mkBase ci)


take :: Take a ab b -> ab -> (a, b)
take Here (b, a) = (a, b)
take (There t) (ab', c) = second (,c) $ take t ab'

put :: Take a ab b -> a -> b -> ab
put Here a b = (b, a)
put (There t) a (b, c) = (put t a b, c)

ttake :: Take x xas as -> Take y xyas xas -> (forall yas. Take x xyas yas -> Take y yas as -> r) -> r
ttake  tx           Here       k = k (There tx)   Here
ttake  Here        (There t)   k = k  Here        t
ttake  (There tx)  (There ty)  k = ttake tx ty $ \t1 t2 -> k (There t1) (There t2)

ttake' :: Take' x xas as -> Take' y xyas xas -> (forall yas. Take' x xyas yas -> Take' y yas as -> r) -> r
ttake' tx           Here'      k = k (There' tx)   Here'
ttake' Here'       (There' t)  k = k  Here'        t
ttake' (There' tx) (There' ty) k = ttake' tx ty $ \t1 t2 -> k (There' t1) (There' t2)

data Take' x xargs args where
  Here'  :: Take' x (x ->  args)       args
  There' :: Take' x       xargs        args
         -> Take' x (y -> xargs) (y -> args)

type family ToIn  a where
  ToIn  ()              = ()
  ToIn  (In sh e  -> x) = (ToIn x, e)
  ToIn  (Mut sh e -> x) = (ToIn x, e)
  ToIn  (Exp'   e -> x) = (ToIn x, e)
  ToIn  (_ -> x)        =  ToIn x
type family ToOut a where
  ToOut ()              = ()
  ToOut (Out sh e -> x) = (ToOut x, e)
  ToOut (Mut sh e -> x) = (ToOut x, e)
  ToOut (_  -> x)       =  ToOut x

getIn :: LeftHandSideArgs body i o -> i -> ToIn body
getIn Base () = ()
getIn (Reqr t1 t2 lhs) i = let (x, i') = take t1 i in (getIn lhs i', x)
getIn (Make t lhs) i = getIn lhs i
getIn (Adju t1 t2 lhs) i = let (x, i') = take t1 i in (getIn lhs i', x)
getIn (EArg lhs) (i, x) = (getIn lhs i, x)
getIn (Ignr lhs) (i, x) =  getIn lhs i

genOut :: LeftHandSideArgs body i o -> i -> ToOut body -> o
genOut Base             ()    o     = 
  ()
genOut (Reqr t1 t2 lhs) i     o     = 
  let (x, i') = take t1 i 
  in put t2 x (genOut lhs i' o)
genOut (Make t lhs)     i    (o, x) = 
  put t x (genOut lhs i o)
genOut (Adju t1 t2 lhs) i    (o, x) = 
  let (y, i') = take t1 i 
  in put t2 x (genOut lhs i' o)
genOut (EArg lhs)      (i, x) o     =
  (genOut lhs i o, x)
genOut (Ignr lhs)      (i, x) o     =
  (genOut lhs i o, x)
