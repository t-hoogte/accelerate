{-# LANGUAGE BangPatterns          #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE LambdaCase            #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE TemplateHaskell       #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE TypeFamilyDependencies#-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE ViewPatterns #-}

-- |
-- Module      : Data.Array.Accelerate.AST.Partitioned
-- Copyright   : [2008..2020] The Accelerate Team
-- License     : BSD3
--
-- Maintainer  : Trevor L. McDonell <trevor.mcdonell@gmail.com>
-- Stability   : experimental
-- Portability : non-portable (GHC extensions)
--
module Data.Array.Accelerate.AST.Partitioned (
  module Data.Array.Accelerate.AST.Partitioned,
  GroundR(..), GroundsR, GroundVar, GroundVars, NFData'(..), Arg(..),
  PreArgs(..), Args, Modifier(..),
  Exp', Var', Fun', In, Out, Mut
) where

import Data.Array.Accelerate.AST.Idx
import Data.Array.Accelerate.AST.Operation

import Prelude hiding ( take )
import Data.Bifunctor
import Data.Array.Accelerate.Trafo.Desugar (ArrayDescriptor(..))
import Data.Array.Accelerate.Representation.Array (Array, Buffers, ArrayR (ArrayR), arrayRtype, rnfArrayR)
import qualified Data.Array.Accelerate.AST.Environment as Env
import Data.Array.Accelerate.Representation.Shape (ShapeR)
import Data.Type.Equality
import Unsafe.Coerce (unsafeCoerce)
import Data.Array.Accelerate.Trafo.Operation.LiveVars
import Data.Array.Accelerate.Representation.Type (TypeR, rnfTypeR)
import Control.DeepSeq (NFData (rnf))
import Data.Array.Accelerate.Trafo.Operation.Simplify (SimplifyOperation(..))
 
-- In this model, every thread has one input element per input array,
-- and one output element per output array. That works perfectly for
-- a Map, Generate, ZipWith - but the rest requires some fiddling:
--
-- - Folds and Scans need to cooperate, and not every thread will
--   return a value. This makes them harder to squeeze into the interpreter,
--   but the LLVM backends are used to such tricks.
--
-- - Fusing Backpermute and Stencil does not translate well to this composition of loop
--   bodies. Instead, we will need a pass (after construction of these clusters)
--   that propagates them to the start of each cluster (or the 
--    originating generate, if fused).

type PartitionedAcc  op = PreOpenAcc  (Cluster op)
type PartitionedAfun op = PreOpenAfun (Cluster op)

-- | A cluster of operations, in total having `args` as signature
data Cluster op args where
  Cluster :: ClusterIO args input output
          -> ClusterAST op  input output
          -> Cluster op args

-- | Internal AST of `Cluster`, simply a list of let-bindings.
-- Note that all environments hold scalar values, not arrays! (aside from Mut)
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
  Reqr :: Take (Value sh e) eenv env
       -> Take (Value sh e) escope scope
       -> LeftHandSideArgs              body   env             scope
       -> LeftHandSideArgs (In  sh e -> body) eenv            escope
  -- The body creates an array
  Make :: Take (Value sh e) escope scope
       -> LeftHandSideArgs              body   env             scope
       -> LeftHandSideArgs (Out sh e -> body) (env, Sh sh e)    escope
  -- Used for Permute: Each 'thread' gets atomic update acess to all values. Behaves like Exp', Var' and Fun'.
  Adju :: LeftHandSideArgs              body   env             scope
       -> LeftHandSideArgs (Mut sh e -> body) (env, Mut sh e) (scope, Mut sh e)
  -- Does nothing to this part of the environment
  Ignr :: LeftHandSideArgs              body   env             scope
       -> LeftHandSideArgs              body  (env, e)        (scope, e)
  EArg :: LeftHandSideArgs              body   env             scope
       -> LeftHandSideArgs (Exp'   e -> body) (env, Exp' e)   (scope, Exp' e)
  VArg :: LeftHandSideArgs              body   env             scope
       -> LeftHandSideArgs (Var'   e -> body) (env, Var' e)   (scope, Var' e)
  FArg :: LeftHandSideArgs              body   env             scope
       -> LeftHandSideArgs (Fun'   e -> body) (env, Fun' e)   (scope, Fun' e)

-- input ~ InArgs args, and output is a permuted version of OutArgs args
data ClusterIO args input output where
  Empty  :: ClusterIO () () ()
  -- Even when an array is fused away, we'll still need its shape sometimes!
  Vertical :: Take (Value sh e) eoutput output -> ArrayR (Array sh e) 
           -> ClusterIO             args   input            output 
           -> ClusterIO (Var' sh -> args) (input, Sh sh e) eoutput
  Input  :: ClusterIO              args   input               output
         -> ClusterIO (In  sh e -> args) (input, Value sh e) (output, Value sh e)
  Output :: Take (Value sh e) eoutput output
         -> SubTupR e e'
         -> TypeR e
         -> ClusterIO              args   input               output
         -> ClusterIO (Out sh e' -> args) (input, Sh sh e)    eoutput
  MutPut :: ClusterIO              args   input             output
         -> ClusterIO (Mut sh e -> args) (input, Mut sh e) (output, Mut sh e)
  ExpPut :: ClusterIO              args   input             output
         -> ClusterIO (Exp'   e -> args) (input, Exp' e)   (output, Exp' e)
  VarPut :: ClusterIO              args   input             output
         -> ClusterIO (Var'   e -> args) (input, Var' e)   (output, Var' e)
  FunPut :: ClusterIO              args   input             output
         -> ClusterIO (Fun'   e -> args) (input, Fun' e)   (output, Fun' e)


pattern ExpArg :: () 
                => forall e args body scope. (args' ~ (e -> args), body' ~ (body, e), scope' ~ (scope, e)) 
                => LeftHandSideArgs args body scope 
                -> LeftHandSideArgs args' body' scope'
pattern ExpArg lhs <- (unExpArg -> Just (lhs, Refl))
{-# COMPLETE Base, Reqr, Make, Adju, Ignr, ExpArg #-}
unExpArg :: LeftHandSideArgs args' i' o' -> Maybe (LeftHandSideArgs args i o, (args', i', o') :~: (e -> args, (i, e), (o, e)))
unExpArg (EArg lhs) = Just (unsafeCoerce lhs, unsafeCoerce Refl)
unExpArg (VArg lhs) = Just (unsafeCoerce lhs, unsafeCoerce Refl)
unExpArg (FArg lhs) = Just (unsafeCoerce lhs, unsafeCoerce Refl)
unExpArg _ = Nothing

pattern ExpPut' :: () 
                => forall e args i o. (args' ~ (e -> args), i' ~ (i, e), o' ~ (o, e)) 
                => ClusterIO args  i  o 
                -> ClusterIO args' i' o'
pattern ExpPut' io <- (unExpPut' -> Just (io, Refl))
{-# COMPLETE Empty, Vertical, Input, Output, MutPut, ExpPut' #-}
unExpPut' :: ClusterIO args' i' o' -> Maybe (ClusterIO args i o, (args', i', o') :~: (e -> args, (i, e), (o, e)))
unExpPut' (ExpPut io) = Just (unsafeCoerce io, unsafeCoerce Refl)
unExpPut' (VarPut io) = Just (unsafeCoerce io, unsafeCoerce Refl)
unExpPut' (FunPut io) = Just (unsafeCoerce io, unsafeCoerce Refl)
unExpPut' _ = Nothing




-- | `xargs` is a type-level list which contains `x`. 
-- Removing `x` from `xargs` yields `args`.
data Take x xargs args where
  Here  :: Take x ( args, x)  args
  There :: Take x  xargs      args
        -> Take x (xargs, y) (args, y)

takeIdx :: Take x xargs args -> Idx xargs x
takeIdx Here      = ZeroIdx
takeIdx (There t) = SuccIdx $ takeIdx t

-- A cluster from a single node
unfused :: op args -> Args env args -> Cluster op args
unfused op args = iolhs args $ \io lhs -> Cluster io (Bind lhs op None)

iolhs :: Args env args -> (forall x y. ClusterIO args x y -> LeftHandSideArgs args x y -> r) -> r
iolhs ArgsNil                     f =                       f  Empty            Base
iolhs (ArgArray In  _ _ _ :>: as) f = iolhs as $ \io lhs -> f (Input       io) (Reqr Here Here lhs)
iolhs (ArgArray Out r _ _ :>: as) f = iolhs as $ \io lhs -> f (Output Here SubTupRkeep (arrayRtype r) io) (Make Here lhs)
iolhs (ArgArray Mut _ _ _ :>: as) f = iolhs as $ \io lhs -> f (MutPut io) (Adju lhs)
iolhs (ArgExp _           :>: as) f = iolhs as $ \io lhs -> f (ExpPut      io) (EArg lhs)
iolhs (ArgVar _           :>: as) f = iolhs as $ \io lhs -> f (VarPut      io) (VArg lhs)
iolhs (ArgFun _           :>: as) f = iolhs as $ \io lhs -> f (FunPut      io) (FArg lhs)

mkBase :: ClusterIO args i o -> LeftHandSideArgs () i i
mkBase Empty = Base
mkBase (Input    ci) = Ignr (mkBase ci)
mkBase (Output _ _ _ ci) = Ignr (mkBase ci)
mkBase (MutPut   ci) = Ignr (mkBase ci)
mkBase (ExpPut'   ci) = Ignr (mkBase ci)
mkBase (Vertical _ _ ci) = Ignr (mkBase ci)

fromArgsTake :: forall env a ab b. Take a ab b -> Take (FromArg env a) (FromArgs env ab) (FromArgs env b)
fromArgsTake Here = Here
fromArgsTake (There t) = There (fromArgsTake @env t)

take :: Take a ab b -> ab -> (a, b)
take Here (b, a) = (a, b)
take (There t) (ab', c) = second (,c) $ take t ab'

put :: Take a ab b -> a -> b -> ab
put Here a b = (b, a)
put (There t) a (b, c) = (put t a b, c)

take' :: Take a ab b -> Env.Env f ab -> (f a, Env.Env f b)
take' Here (Env.Push env x) = (x, env)
take' (There t) (Env.Push env x) = second (`Env.Push` x) $ take' t env

put' :: Take a ab b -> f a -> Env.Env f b -> Env.Env f ab
put' Here a env = Env.Push env a
put' (There t) a (Env.Push env c) = Env.Push (put' t a env) c

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

type family InArgs  a where
  InArgs  ()              = ()
  InArgs  (In sh e  -> x) = (InArgs x, Value sh e)
  InArgs  (Mut sh e -> x) = (InArgs x, Mut sh e)
  InArgs  (Exp'   e -> x) = (InArgs x, Exp' e)
  InArgs  (Fun'   e -> x) = (InArgs x, Fun' e)
  InArgs  (Var'   e -> x) = (InArgs x, Var' e)
  InArgs  (Out sh e -> x) = (InArgs x, Sh sh e)
type family OutArgs a where
  OutArgs ()              = ()
  OutArgs (Out sh e -> x) = (OutArgs x, Value sh e)
  OutArgs (Mut sh e -> x) = (OutArgs x, Mut sh e)
  OutArgs (_  -> x)       =  OutArgs x

data ToArg env a where
  ArrArg :: ArrayR (Array sh e)
         -> GroundVars env sh
         -> GroundVars env (Buffers e)
         -> ToArg env (Value sh e)
  OutArg :: ArrayR (Array sh e)
         -> GroundVars env sh
         -> GroundVars env (Buffers e) 
         -> ToArg env (Sh sh e)
  Others :: Arg env a -> ToArg env a


getIn :: LeftHandSideArgs body i o -> i -> InArgs body
getIn Base () = ()
getIn (Reqr t1 _ lhs) i = let (x, i') = take t1 i in (getIn lhs i', x)
getIn (Make _ lhs) (i, sh) = (getIn lhs i, sh)
getIn (Adju lhs)   (i, x)  = (getIn lhs i, x)
getIn (Ignr lhs)   (i, _)  =  getIn lhs i
getIn (EArg lhs)   (i, x)  = (getIn lhs i, x)
getIn (VArg lhs)   (i, x)  = (getIn lhs i, x)
getIn (FArg lhs)   (i, x)  = (getIn lhs i, x)

genOut :: LeftHandSideArgs body i o -> i -> OutArgs body -> o
genOut Base             ()    _     = 
  ()
genOut (Reqr t1 t2 lhs) i     o     = 
  let (x, i') = take t1 i 
  in put t2 x (genOut lhs i' o)
genOut (Make t lhs)    (i, _) (o, x) = 
  put t x (genOut lhs i o)
genOut (Adju lhs) (i, _)    (o, x) = 
  (genOut lhs i o, x)
genOut (Ignr lhs)      (i, x) o     =
  (genOut lhs i o, x)
genOut (EArg lhs)      (i, x) o     =
  (genOut lhs i o, x)
genOut (VArg lhs)      (i, x) o     =
  (genOut lhs i o, x)
genOut (FArg lhs)      (i, x) o     =
  (genOut lhs i o, x)

type family FromArg env a = b | b -> a where
  FromArg env (Exp'     e) = Exp     env e
  FromArg env (Var'     e) = ExpVars env e
  FromArg env (Fun'     e) = Fun     env e
  FromArg env (Mut   sh e) = ArrayDescriptor env (Array sh e)
  FromArg env (Value sh e) = Value sh e
  FromArg env (Sh    sh e) = Sh sh e

type family FromArgs env a = b | b -> a where
  FromArgs env ()            = ()
  FromArgs env (a, x) = (FromArgs env a, FromArg env x)
  -- FromArgs env (x, Exp'   e) = (FromArgs env x, Exp     env e)
  -- FromArgs env (x, Var'   e) = (FromArgs env x, ExpVars env e)
  -- FromArgs env (x, Fun'   e) = (FromArgs env x, Fun     env e)
  -- FromArgs env (x, Mut sh e) = (FromArgs env x, ArrayDescriptor env (Array sh e))
  -- FromArgs env (x, Value sh e) = (FromArgs env x,       Value sh    e)
  -- FromArgs env (x, Sh    sh e) = (FromArgs env x,         Sh sh e)

type FromIn  env args = FromArgs env ( InArgs args)
type FromOut env args = FromArgs env (OutArgs args)


-- helps for type inference and safety: If we instead use 'e', it can match all the other options too. 
data Value sh e = Value e (Sh sh e)
-- e is phantom
data Sh sh e    = Shape (ShapeR sh) sh

instance NFData' op => NFData' (Cluster op) where
  rnf' (Cluster io ast) = rnf io `seq` rnf ast

instance NFData (ClusterIO args input output) where
  rnf Empty = ()
  rnf (Vertical take repr io) = rnf take `seq` rnfArrayR repr `seq` rnf io
  rnf (Input io) = rnf io
  rnf (Output take subTupR tp io) = rnf take `seq` rnf subTupR `seq` rnfTypeR tp `seq` rnf io
  rnf (MutPut io) = rnf io
  rnf (ExpPut io) = rnf io
  rnf (VarPut io) = rnf io
  rnf (FunPut io) = rnf io

instance NFData (Take x xargs args) where
  rnf Here = ()
  rnf (There take) = rnf take

instance NFData' op => NFData (ClusterAST op env result) where
  rnf None = ()
  rnf (Bind lhsArgs op ast) = rnf lhsArgs `seq` rnf' op `seq` rnf ast

instance NFData (LeftHandSideArgs body env scope) where
  rnf Base = ()
  rnf (Reqr take1 take2 args) = rnf take1 `seq` rnf take2 `seq` rnf args
  rnf (Make take args) = rnf take `seq` rnf args
  rnf (Adju args) = rnf args
  rnf (Ignr args) = rnf args
  rnf (EArg args) = rnf args
  rnf (VArg args) = rnf args
  rnf (FArg args) = rnf args

instance SimplifyOperation op => SimplifyOperation (Cluster op) where
  -- TODO: Propagate detectCopy of operations in cluster?

instance SLVOperation (Cluster op) where
  slvOperation (Cluster io ast :: Cluster op args) = Just $ ShrinkOperation shrinkOperation
    where
      shrinkOperation :: SubArgs args args' -> Args env args' -> Args env' args -> ShrunkOperation (Cluster op) env
      shrinkOperation subArgs args' args = ShrunkOperation (Cluster (slvIO subArgs args' args io) ast) args'

      slvIO :: SubArgs a a' -> Args env a' -> Args env' a -> ClusterIO a i o -> ClusterIO a' i o
      slvIO SubArgsNil ArgsNil ArgsNil Empty = Empty
      slvIO (SubArgsDead subargs) (ArgVar _ :>: args') (ArgArray Out (ArrayR shr _) _ _ :>: args) (Output t _ te io') = Vertical t (ArrayR shr te) (slvIO subargs args' args io')
      slvIO (SubArgsLive SubArgKeep subargs) (_ :>: (args' :: Args env a')) (_ :>: (args :: Args env' a)) io'
        = let k :: forall i o. ClusterIO a i o -> ClusterIO a' i o 
              k = slvIO subargs args' args in case io' of
            Vertical t r io'' -> Vertical t r $ k io''
            Input        io'' -> Input        $ k io''
            Output t s e io'' -> Output t s e $ k io''
            MutPut       io'' -> MutPut       $ k io''
            ExpPut       io'' -> ExpPut       $ k io''
            VarPut       io'' -> VarPut       $ k io''
            FunPut       io'' -> FunPut       $ k io''
      slvIO
        (SubArgsLive (SubArgOut s) subargs)
        ((ArgArray Out _ _ _) :>: args')
        ((ArgArray Out _ _ _) :>: args)
        (Output t s' tr io')
        = Output t (composeSubTupR s s') tr (slvIO subargs args' args io')

