{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE BangPatterns        #-}
{-# LANGUAGE BlockArguments      #-}
{-# LANGUAGE EmptyCase           #-}
{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE FlexibleInstances   #-}
{-# LANGUAGE GADTs               #-}
{-# LANGUAGE InstanceSigs        #-}
{-# LANGUAGE LambdaCase          #-}
{-# LANGUAGE LambdaCase        #-}
{-# LANGUAGE MagicHash           #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE PatternGuards       #-}
{-# LANGUAGE PatternSynonyms     #-}
{-# LANGUAGE RankNTypes          #-}
{-# LANGUAGE RecordWildCards     #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections       #-}
{-# LANGUAGE TypeApplications    #-}
{-# LANGUAGE TypeFamilies        #-}
{-# LANGUAGE TypeFamilyDependencies #-}
{-# LANGUAGE TypeOperators       #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ViewPatterns        #-}

{-# OPTIONS_GHC -fno-warn-name-shadowing #-}

module Data.Array.Accelerate.Eval where

import Prelude                                                      hiding (take, (!!), sum, Either(..) )
import Data.Array.Accelerate.AST.Partitioned hiding (Empty)
import qualified Data.Array.Accelerate.AST.Partitioned as P
import Data.Array.Accelerate.AST.Operation
import Data.Array.Accelerate.Trafo.Desugar
import Data.Array.Accelerate.Representation.Array
import Data.Array.Accelerate.Representation.Type
import Data.Array.Accelerate.AST.Environment hiding (Identity(..))
import Data.Array.Accelerate.Trafo.Operation.LiveVars
import Data.Array.Accelerate.Trafo.Partitioning.ILP.Graph (BackendCluster, MakesILP (BackendClusterArg))
import Data.Array.Accelerate.Array.Buffer
import Data.Array.Accelerate.Pretty.Partitioned ()


import Data.Array.Accelerate.Trafo.Schedule.Uniform ()
import Data.Array.Accelerate.Pretty.Schedule.Uniform ()
import Data.Kind (Type)
import Data.Bifunctor (bimap)

type BackendArgs op env = PreArgs (BackendClusterArg2 op env)
type BackendEnv op env = Env (BackendEnvElem op env)
data BackendEnvElem op env arg = BEE (ToArg env arg) (BackendClusterArg2 op env arg)
type BackendArgEnv op env = Env (BackendArgEnvElem op env)
data BackendArgEnvElem op env arg = BAE (FromArg env arg) (BackendClusterArg2 op env arg)
newtype FromArg' env a = FromArg (FromArg env a)
pattern PushFA :: () => (e' ~ (e, x)) => FromArg env x -> Env (FromArg' env) e -> Env (FromArg' env) e'
pattern PushFA x env = Push env (FromArg x)
{-# COMPLETE Empty, PushFA #-}

-- TODO make actually static, i.e. by removing all 'Val env's from these functions and using `Fun env (Int -> Int)` instead in the interpreter
class (MakesILP op) => StaticClusterAnalysis (op :: Type -> Type) where
  -- give better name
  data BackendClusterArg2 op env arg
  onOp :: op args -> BackendArgs op env (OutArgsOf args) -> Args env args -> Val env -> BackendArgs op env args
  def :: Arg env arg -> Val env -> BackendClusterArg op arg -> BackendClusterArg2 op env arg
  valueToIn    :: BackendClusterArg2 op env (Value sh e)  -> BackendClusterArg2 op env (In    sh e)
  valueToOut   :: BackendClusterArg2 op env (Value sh e)  -> BackendClusterArg2 op env (Out   sh e)
  inToValue    :: BackendClusterArg2 op env (In    sh e)  -> BackendClusterArg2 op env (Value sh e)
  outToValue   :: BackendClusterArg2 op env (Out   sh e)  -> BackendClusterArg2 op env (Value sh e)
  outToSh      :: BackendClusterArg2 op env (Out   sh e)  -> BackendClusterArg2 op env (Sh    sh e)
  shToOut      :: BackendClusterArg2 op env (Sh    sh e)  -> BackendClusterArg2 op env (Out   sh e)
  shToValue    :: BackendClusterArg2 op env (Sh    sh e)  -> BackendClusterArg2 op env (Value sh e)
  varToValue   :: BackendClusterArg2 op env (Var'  sh)    -> BackendClusterArg2 op env (Value sh e)
  varToSh      :: BackendClusterArg2 op env (Var'  sh)    -> BackendClusterArg2 op env (Sh    sh e)
  shToVar      :: BackendClusterArg2 op env (Sh    sh e)  -> BackendClusterArg2 op env (Var'  sh  )
  shrinkOrGrow :: BackendClusterArg2 op env (m     sh e') -> BackendClusterArg2 op env (m     sh e)


-- use ScopedTypeVariables for op and env, but not for the args (so we call them arguments instead)
makeBackendArg :: forall op env arguments. StaticClusterAnalysis op => Args env arguments -> Val env -> Cluster op arguments -> BackendArgs op env arguments
makeBackendArg args env (Cluster info (Cluster' io ast)) = let o = getOutputEnv io args info
                                                               i = fromAST ast o
                                                          in fromInputEnv io i
  where
    fromAST :: ClusterAST op i o -> BackendEnv op env o -> BackendEnv op env i
    fromAST None o = o
    fromAST (Bind lhs op ast) o = let o' = fromAST ast o
                                  in lhsArgsEnv lhs o' (uncurry (onOp op) (first' onlyOut $ lhsEnvArgs lhs o') env)

    onlyOut :: BackendArgs op env args -> Args env args -> BackendArgs op env (OutArgsOf args)
    onlyOut ArgsNil ArgsNil = ArgsNil
    onlyOut (b :>: bs) (ArgArray Out _ _ _ :>: as) = b :>: onlyOut bs as
    onlyOut (_ :>: bs) (a                  :>: as) = case a of
      ArgArray In  _ _ _ -> onlyOut bs as
      ArgArray Mut _ _ _ -> onlyOut bs as
      ArgExp{} -> onlyOut bs as
      ArgVar{} -> onlyOut bs as
      ArgFun{} -> onlyOut bs as

    lhsEnvArgs :: LeftHandSideArgs body env' scope -> BackendEnv op env scope -> (BackendArgs op env body, Args env body)
    lhsEnvArgs Base Empty = (ArgsNil, ArgsNil)
    lhsEnvArgs (Reqr _ t lhs) env = case take' t env of (BEE (ArrArg r sh buf) f, env') -> bimap (valueToIn  f :>:) (ArgArray In  r sh buf :>:) $ lhsEnvArgs lhs env'
                                                        _ -> error "urk"
    lhsEnvArgs (Make   t lhs) env = case take' t env of (BEE (ArrArg r sh buf) f, env') -> bimap (valueToOut f :>:) (ArgArray Out r sh buf :>:) $ lhsEnvArgs lhs env'
                                                        _ -> error "urk"
    lhsEnvArgs (ExpArg lhs) (Push env (BEE (Others arg) f)) = bimap (f :>:) (arg :>:) $ lhsEnvArgs lhs env
    lhsEnvArgs (Adju   lhs) (Push env (BEE (Others arg) f)) = bimap (f :>:) (arg :>:) $ lhsEnvArgs lhs env
    lhsEnvArgs (Ignr lhs) (Push env _) = lhsEnvArgs lhs env

    lhsArgsEnv :: LeftHandSideArgs body env' scope -> BackendEnv op env scope -> BackendArgs op env body -> BackendEnv op env env'
    lhsArgsEnv Base                   _                ArgsNil            = Empty
    lhsArgsEnv (Reqr t1 t2 lhs)       env              (f :>: args) = case take' t2 env of (BEE arg          _, env') -> put' t1 (BEE arg (inToValue f)) (lhsArgsEnv lhs env' args)
    lhsArgsEnv (Make t     lhs)       env              (f :>: args) = case take' t  env of (BEE (ArrArg r sh buf) _, env') -> Push (lhsArgsEnv lhs env' args) (BEE (OutArg r sh buf) (outToSh f))
                                                                                           _ -> error "urk"
    lhsArgsEnv (ExpArg     lhs) (Push env (BEE arg _)) (f :>: args) = Push (lhsArgsEnv lhs env  args) (BEE arg f)
    lhsArgsEnv (Adju       lhs) (Push env (BEE arg _)) (f :>: args) = Push (lhsArgsEnv lhs env  args) (BEE arg f)
    lhsArgsEnv (Ignr       lhs) (Push env arg)                      args  = Push (lhsArgsEnv lhs env  args) arg

    getOutputEnv :: ClusterIO args i o -> Args env args -> BackendCluster op args -> BackendEnv op env o
    getOutputEnv P.Empty       ArgsNil           _ = Empty
    getOutputEnv (Vertical t r io) (arg@(ArgVar vars) :>: args) (info :>: infos) = put' t (BEE (ArrArg r (toGrounds vars) (error "accessing a fused away buffer")) (varToValue $ def arg env info)) (getOutputEnv io args infos) -- there is no buffer!
    getOutputEnv (Input      io) (arg@(ArgArray In r sh buf) :>: args) (info :>: infos) = Push (getOutputEnv io args infos) (BEE (ArrArg r sh buf) (inToValue $ def arg env info))
    getOutputEnv (Output t s e io) (arg@(ArgArray Out r sh buf) :>: args) (info :>: infos) = put' t (BEE (ArrArg (ArrayR (arrayRshape r) e) sh (biggenBuffers s buf)) (outToValue $ shrinkOrGrow $ def arg env info)) (getOutputEnv io args infos)
    getOutputEnv (MutPut     io) (arg :>: args) (info :>: infos) = Push (getOutputEnv io args infos) (BEE (Others arg) (def arg env info))
    getOutputEnv (ExpPut'    io) (arg :>: args) (info :>: infos) = Push (getOutputEnv io args infos) (BEE (Others arg) (def arg env info))

    biggenBuffers :: SubTupR e e' -> GroundVars env (Buffers e') -> GroundVars env (Buffers e)
    biggenBuffers SubTupRskip _ = error "accessing a simplified away buffer"
    biggenBuffers SubTupRkeep vars = vars
    biggenBuffers (SubTupRpair _ _) (TupRsingle _) = error "impossible???"
    biggenBuffers (SubTupRpair sl sr) (TupRpair bufl bufr) = TupRpair (biggenBuffers sl bufl) (biggenBuffers sr bufr)

    fromInputEnv :: ClusterIO args input output -> BackendEnv op env input -> BackendArgs op env args
    fromInputEnv P.Empty       Empty = ArgsNil
    fromInputEnv (Vertical _ _ io) (Push env (BEE _ f)) = shToVar f                :>: fromInputEnv io env
    fromInputEnv (Input        io) (Push env (BEE _ f)) = valueToIn f              :>: fromInputEnv io env
    fromInputEnv (Output _ _ _ io) (Push env (BEE _ f)) = shrinkOrGrow (shToOut f) :>: fromInputEnv io env
    fromInputEnv (MutPut       io) (Push env (BEE _ f)) = f                        :>: fromInputEnv io env
    fromInputEnv (ExpPut'      io) (Push env (BEE _ f)) = f                        :>: fromInputEnv io env



fromArgs :: Int -> Val env -> Args env args -> FromIn env args
fromArgs _ _ ArgsNil = ()
fromArgs i env (ArgVar v :>: args) = (fromArgs i env args, v)
fromArgs i env (ArgExp e :>: args) = (fromArgs i env args, e)
fromArgs i env (ArgFun f :>: args) = (fromArgs i env args, f)
fromArgs i env (ArgArray Mut (ArrayR shr _) sh buf :>: args) = (fromArgs i env args, ArrayDescriptor shr sh buf)
fromArgs i env (ArgArray In (ArrayR shr typer) shv buf :>: args) =
  let buf' = varsGetVal buf env
      sh   = varsGetVal shv env
  in (fromArgs i env args, Value (indexBuffers typer buf' i) (Shape shr sh))
fromArgs i env (ArgArray Out (ArrayR shr _) sh _ :>: args) = (fromArgs i env args, Shape shr (varsGetVal sh env))


class (StaticClusterAnalysis op, Monad (EvalMonad op)) => EvalOp op where
  type family EvalMonad op :: Type -> Type
  evalOp :: Int -> op args -> Val env -> BackendArgEnv op env (InArgs args) -> (EvalMonad op) (Env (FromArg' env) (OutArgs args))
  writeOutput :: TypeR e -> Buffers e -> Int -> e -> EvalMonad op ()
  readInput :: TypeR e -> Buffers e -> BackendClusterArg2 op env (In sh e) -> Int -> EvalMonad op e

evalCluster :: forall op env args. EvalOp op => ((Int -> EvalMonad op ()) -> EvalMonad op ()) -> Cluster op args -> Args env args -> Val env -> (EvalMonad op) ()
evalCluster f c@(Cluster _ (Cluster' io ast)) args env = do
  let ba = makeBackendArg args env c
  f (\n -> do i <- evalIO1 n io args ba env
              o <- evalAST n ast env i
              evalIO2 @op n io args env o)

evalIO1 :: EvalOp op => Int -> ClusterIO args i o -> Args env args -> BackendArgs op env args -> Val env -> (EvalMonad op) (BackendArgEnv op env i)
evalIO1 _ P.Empty                                     ArgsNil    ArgsNil    _ = pure Empty
evalIO1 n (Input     io) (ArgArray In r sh buf :>: args) (info :>: infos) env =
  Push <$> evalIO1 n io args infos env <*> ((\value -> BAE value $ inToValue info) <$> value)
    where value = Value <$> readInput (arrayRtype r) (varsGetVal buf env) info n
                      <*> pure (Shape   (arrayRshape r) (varsGetVal sh  env))
evalIO1 n (Vertical _ r io) (ArgVar vars         :>: args) (info :>: infos) env = Push <$> evalIO1 n io args infos env <*> pure (BAE (Shape (arrayRshape r) (varsGetVal vars env)) $ varToSh info)
evalIO1 n (Output _ _ _ io) (ArgArray Out r sh _ :>: args) (info :>: infos) env = Push <$> evalIO1 n io args infos env <*> pure (BAE (Shape (arrayRshape r) (varsGetVal sh env)) $ outToSh $ shrinkOrGrow info)
evalIO1 n (MutPut     io) (ArgArray Mut r sh buf :>: args) (info :>: infos) env = Push <$> evalIO1 n io args infos env <*> pure (BAE (ArrayDescriptor (arrayRshape r) sh buf) info)
evalIO1 n (ExpPut'    io) (ArgExp e              :>: args) (info :>: infos) env = Push <$> evalIO1 n io args infos env <*> pure (BAE e info)
evalIO1 n (ExpPut'    io) (ArgVar e              :>: args) (info :>: infos) env = Push <$> evalIO1 n io args infos env <*> pure (BAE e info)
evalIO1 n (ExpPut'    io) (ArgFun e              :>: args) (info :>: infos) env = Push <$> evalIO1 n io args infos env <*> pure (BAE e info)

evalIO2 :: forall op args i o env. EvalOp op => Int -> ClusterIO args i o -> Args env args -> Val env -> Env (FromArg' env) o -> (EvalMonad op) ()
evalIO2 _ P.Empty ArgsNil _ Empty = pure ()
evalIO2 n (Vertical t _ io) (_                                    :>: args) env (take' t -> (_, o)) = evalIO2 @op n io args env o
evalIO2 n (Input      io)   (_                                    :>: args) env (PushFA _ o)        = evalIO2 @op n io args env o
evalIO2 n (MutPut     io)   (_                                    :>: args) env (PushFA _ o)        = evalIO2 @op n io args env o
evalIO2 n (ExpPut'     io)  (_                                    :>: args) env (PushFA _ o)        = evalIO2 @op n io args env o
evalIO2 n (Output t s _ io) (ArgArray Out (arrayRtype -> r) _ buf :>: args) env o = let (FromArg (Value x _), o') = take' t o in writeOutput @op r (varsGetVal buf env) n (subTup s x) >> evalIO2 @op n io args env o'

evalAST :: forall op i o env. EvalOp op => Int -> ClusterAST op i o -> Val env -> BackendArgEnv op env i -> (EvalMonad op) (Env (FromArg' env) o)
evalAST _ None _ Empty = pure Empty
evalAST n None env (Push i (BAE x _)) = flip Push (FromArg x) <$> evalAST n None env i
evalAST n (Bind lhs op ast) env i = do
  let i' = evalLHS1 lhs i env
  o' <- evalOp n op env i'
  let scope = evalLHS2 lhs i env o'
  evalAST n ast env scope

evalLHS1 :: forall op body i scope env. LeftHandSideArgs body i scope -> BackendArgEnv op env i -> Val env -> BackendArgEnv op env (InArgs body)
evalLHS1 Base Empty _ = Empty
evalLHS1 (Reqr t _ lhs) i env = let (BAE x info, i') = take' t i in Push (evalLHS1 lhs i' env) $ BAE x info
evalLHS1 (Make _   lhs) (Push i' (BAE x info)) env = Push (evalLHS1 lhs i' env) (BAE x info)
evalLHS1 (EArg     lhs) (Push i' (BAE x info)) env = Push (evalLHS1 lhs i' env) (BAE x info)
evalLHS1 (FArg     lhs) (Push i' (BAE x info)) env = Push (evalLHS1 lhs i' env) (BAE x info)
evalLHS1 (VArg     lhs) (Push i' (BAE x info)) env = Push (evalLHS1 lhs i' env) (BAE x info)
evalLHS1 (Adju     lhs) (Push i' (BAE x info)) env = Push (evalLHS1 lhs i' env) (BAE x info)
evalLHS1 (Ignr     lhs) (Push i' (BAE _ _   )) env =       evalLHS1 lhs i' env

evalLHS2 :: EvalOp op => LeftHandSideArgs body i scope -> BackendArgEnv op env i -> Val env -> Env (FromArg' env) (OutArgs body) -> BackendArgEnv op env scope
evalLHS2 Base Empty _ Empty = Empty
evalLHS2 (Reqr t1 t2 lhs) i env o = let (x, i') = take' t1 i
                                    in put' t2 x (evalLHS2 lhs i' env o)
evalLHS2 (Make t lhs) (Push i (BAE _ info)) env (Push o (FromArg y)) = put' t (BAE y (shToValue info)) (evalLHS2 lhs i  env o)
evalLHS2 (EArg   lhs) (Push i (BAE x info)) env           o  = Push (evalLHS2 lhs i env o) (BAE x info)
evalLHS2 (FArg   lhs) (Push i (BAE x info)) env           o  = Push (evalLHS2 lhs i env o) (BAE x info)
evalLHS2 (VArg   lhs) (Push i (BAE x info)) env           o  = Push (evalLHS2 lhs i env o) (BAE x info)
evalLHS2 (Adju   lhs) (Push i (BAE _ info)) env (PushFA m o) = Push (evalLHS2 lhs i env o) (BAE m info)
evalLHS2 (Ignr   lhs) (Push i (BAE x info)) env           o  = Push (evalLHS2 lhs i env o) (BAE x info)

first' :: (a -> b -> c) -> (a,b) -> (c,b)
first' f (a,b) = (f a b, b)
