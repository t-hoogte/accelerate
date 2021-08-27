{-# LANGUAGE BangPatterns          #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE LambdaCase            #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE TemplateHaskell       #-}
{-# LANGUAGE TupleSections #-}
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
import Data.Bifunctor

-- In this model, every thread has one input element per input array,
-- and one output element per output array. That works perfectly for
-- a Map, Generate, ZipWith - but the rest requires some fiddling:
--
-- - Folds, Scans and Stencils need to cooperate, and not every thread will
--   return a value. This makes them harder to squeeze into the interpreter,
--   but the LLVM backends are used to such tricks.
--
-- - Fusing Backpermute does not translate well to this composition of loop
--   bodies. Instead, we will need a pass (after construction of these clusters)
--   that propagates backpermutes to the start of each cluster (or the 
--    originating backpermute, if fused).
--
-- - I'm not sure how to handle Permute: It hints towards needing a constructor
--   that passes an entire mut array to all elements, like Exp' and friends.
--   It currently uses `Mut` in Desugar.hs, but in the fusion files that means
--   'somethat that is both input and output', e.g. an in-place Map.


type PartitionedAcc  op = PreOpenAcc  (Clustered op)
type PartitionedAfun op = PreOpenAfun (Clustered op)

pattern ExecC :: () => (t ~ ()) => Cluster aenv op args -> Args aenv args -> PreOpenAcc (Clustered op) aenv t
pattern ExecC op args = Execute (Clustered op args)
{-# COMPLETE ExecC,Return,Compute,Alet,Alloc,Use,Unit,Acond,Awhile #-}

data Clustered op aenv args = Clustered (Cluster aenv op args) (Args aenv args)

-- | A cluster of operations, in total having `args` as signature
data Cluster aenv op args where
  Cluster :: ClusterIO          args input output
          -> ClusterAST aenv op      input output
          -> Cluster    aenv op args

-- | Internal AST of `Cluster`, simply a list of let-bindings.
-- Note that all environments hold scalar values, not arrays!
data ClusterAST aenv op env result where
  None :: ClusterAST aenv op env env
  -- `Bind _ x y` reads as `do x; in the resulting environment, do y`
  Bind :: LeftHandSideArgs aenv body env scope
       -> op body
       -> ClusterAST aenv op scope result
       -> ClusterAST aenv op env   result

-- | A version of `LeftHandSide` that works on the function-separated environments: 
-- Given environment `env`, we can execute `body`, yielding environment `scope`.
data LeftHandSideArgs aenv body env scope where
  -- Because of `Ignr`, we could also give this the type `LeftHandSideArgs () () ()`.
  Base :: LeftHandSideArgs aenv () () ()
  -- The body has an input array
  Reqr :: Take e eenv env -> Take e escope scope
       -> LeftHandSideArgs aenv              body   env      scope
       -> LeftHandSideArgs aenv (In  sh e -> body) eenv     escope
  -- The body creates an array
  Make :: Take e escope scope
       -> LeftHandSideArgs aenv              body   env      scope
       -> LeftHandSideArgs aenv (Out sh e -> body)  env     escope
  -- One array that is both input and output
  Adju :: Take e eenv env -> Take e escope scope
       -> LeftHandSideArgs aenv              body   env      scope
       -> LeftHandSideArgs aenv (Mut sh e -> body) eenv     escope
  -- TODO: duplicate for Var' and Fun'
  EArg :: LeftHandSideArgs aenv              body   env      scope
       -> LeftHandSideArgs aenv (Exp'   e -> body) (env, Exp aenv e) (scope, Exp aenv e)
  -- Does nothing to this part of the environment
  Ignr :: LeftHandSideArgs aenv              body   env      scope
       -> LeftHandSideArgs aenv              body  (env, e) (scope, e)

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
         -> ClusterIO (Exp'   e -> args) (input, Exp aenv e) (output, Exp aenv e)

-- | `xargs` is a type-level list which contains `x`. 
-- Removing `x` from `xargs` yields `args`.
data Take x xargs args where
  Here  :: Take x ( args, x)  args
  There :: Take x  xargs      args
        -> Take x (xargs, y) (args, y)


-- A cluster from a single node
unfused :: op args -> Args aenv args -> Cluster aenv op args
unfused op args = iolhs args $ \io lhs -> Cluster io (Bind lhs op None)

iolhs :: Args aenv args -> (forall x y. ClusterIO args x y -> LeftHandSideArgs aenv args x y -> r) -> r
iolhs ArgsNil                     f =                       f  Empty            Base
iolhs (ArgArray In  _ _ _ :>: as) f = iolhs as $ \io lhs -> f (Input       io) (Reqr Here Here lhs)
iolhs (ArgArray Out _ _ _ :>: as) f = iolhs as $ \io lhs -> f (Output Here io) (Make Here lhs)
iolhs (ArgArray Mut _ _ _ :>: as) f = iolhs as $ \io lhs -> f (MutPut Here io) (Adju Here Here lhs)
iolhs (ArgExp _           :>: as) f = iolhs as $ \io lhs -> f (ExpPut      io) (EArg lhs)
iolhs _ _ = undefined -- TODO Var', Fun'

mkBase :: ClusterIO args i o -> LeftHandSideArgs aenv () i i
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

type family ToIn  aenv a where
  ToIn  aenv ()              = ()
  ToIn  aenv (In sh e  -> x) = (ToIn aenv x, e)
  ToIn  aenv (Mut sh e -> x) = (ToIn aenv x, e)
  ToIn  aenv (Exp'   e -> x) = (ToIn aenv x, Exp aenv e)
  ToIn  aenv (_ -> x)        =  ToIn aenv x
type family ToOut aenv a where
  ToOut aenv ()              = ()
  ToOut aenv (Out sh e -> x) = (ToOut aenv x, e)
  ToOut aenv (Mut sh e -> x) = (ToOut aenv x, e)
  ToOut aenv (_  -> x)       =  ToOut aenv x

getIn :: LeftHandSideArgs aenv body i o -> i -> ToIn aenv body
getIn Base           ()     = ()
getIn (Reqr t _ lhs)  i     = let (x, i') = take t i
                              in (getIn lhs i', x)
getIn (Make _   lhs)  i     =     getIn lhs i
getIn (Adju t _ lhs)  i     = let (x, i') = take t i
                              in (getIn lhs i', x)
getIn (EArg     lhs) (i, x) =    (getIn lhs i, x)
getIn (Ignr     lhs) (i, _) =     getIn lhs i

genOut :: LeftHandSideArgs aenv body i o -> i -> ToOut aenv body -> o
genOut Base             ()    ()    = ()
genOut (Reqr t1 t2 lhs) i     o     = let (x, i') = take t1 i
                                      in put t2 x (genOut lhs i' o)
genOut (Make t lhs)     i    (o, x) =    put t  x (genOut lhs i  o)
genOut (Adju t1 t2 lhs) i    (o, x) = let (_, i') = take t1 i
                                      in put t2 x (genOut lhs i' o)
genOut (EArg lhs)      (i, x) o     =             (genOut lhs i  o, x)
genOut (Ignr lhs)      (i, x) o     =             (genOut lhs i  o, x)



reindexAccC :: Applicative f => ReindexPartial f env env' -> PartitionedAcc op env t -> f (PartitionedAcc op env' t)
reindexAccC r (ExecC opargs pa) = ExecC (_ opargs) <$> reindexArgs r pa
reindexAccC r (Return tr) = Return <$> reindexVars r tr
reindexAccC r (Compute poe) = Compute <$> reindexExp r poe
reindexAccC r (Alet lhs tr poa poa') = reindexLHS r lhs $ \lhs' r' -> Alet lhs' tr <$> reindexAccC r poa <*> reindexAccC r' poa'
reindexAccC r (Alloc sr st tr) = Alloc sr st <$> reindexVars r tr
reindexAccC _ (Use st bu) = pure $ Use st bu
reindexAccC r (Unit var) = Unit <$> reindexVar r var
reindexAccC r (Acond var poa poa') = Acond <$> reindexVar r var <*> reindexAccC r poa <*> reindexAccC r poa'
reindexAccC r (Awhile tr poa poa' tr') = Awhile tr <$> reindexAfunC r poa <*> reindexAfunC r poa' <*> reindexVars r tr'


reindexAfunC :: Applicative f => ReindexPartial f env env' -> PartitionedAfun op env t -> f (PartitionedAfun op env' t)
reindexAfunC r (Abody poa) = Abody <$> reindexAccC r poa
reindexAfunC r (Alam lhs poa) = reindexLHS r lhs $ \lhs' r' -> Alam lhs' <$> reindexAfunC r' poa

reindexCluster :: Applicative f => ReindexPartial f env env' -> Cluster env op args -> f (Cluster env' op args)
reindexCluster r (Cluster ci ca) = _

reindexCAST :: Applicative f => ReindexPartial f aenv aenv' -> ClusterAST aenv op env result -> f (ClusterAST aenv' op env result)
reindexCAST _ None = pure None
reindexCAST r (Bind lhs op ast) = Bind <$> reindexCLHS r lhs <*> pure op <*> reindexCAST r ast


reindexCLHS :: Applicative f => ReindexPartial f aenv aenv' -> LeftHandSideArgs aenv body env scope -> f (LeftHandSideArgs aenv' body (ChangeAEnv aenv' env) (ChangeAEnv aenv' scope))
reindexCLHS _  Base            = pure Base
reindexCLHS r (Reqr t1 t2 lhs) = Reqr t1 t2 <$> reindexCLHS r lhs
reindexCLHS r (Make t     lhs) = Make t     <$> reindexCLHS r lhs
reindexCLHS r (Adju t1 t2 lhs) = Adju t1 t2 <$> reindexCLHS r lhs
reindexCLHS r (EArg       lhs) = EArg       <$> reindexCLHS r lhs
reindexCLHS r (Ignr       lhs) = Ignr       <$> reindexCLHS r lhs

type family ChangeAEnv aenv env where
  ChangeAEnv _ () = ()
  ChangeAEnv aenv (env, Exp _ e) = (ChangeAEnv aenv env, Exp aenv e)
  ChangeAEnv aenv (env, x) = (ChangeAEnv aenv env, x)
