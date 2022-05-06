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
import Data.Array.Accelerate.AST.Var
import Data.Array.Accelerate.AST.LeftHandSide
import qualified Data.Array.Accelerate.AST.Partitioned as P
import Data.Array.Accelerate.AST.Operation
import Data.Array.Accelerate.Trafo.Var
import Data.Array.Accelerate.Trafo.Desugar
import Data.Array.Accelerate.Representation.Array
import Data.Array.Accelerate.Representation.Type
import Data.Array.Accelerate.Representation.Ground
import Data.Array.Accelerate.AST.Environment hiding (Identity(..))
import Data.Array.Accelerate.Trafo.Substitution
import Data.Array.Accelerate.Trafo.Operation.LiveVars
import Data.Array.Accelerate.Trafo.Partitioning.ILP.Graph (BackendCluster, MakesILP (BackendClusterArg))
import Data.Array.Accelerate.Array.Buffer
import Data.Array.Accelerate.Pretty.Partitioned ()


import Data.Array.Accelerate.Trafo.Schedule.Uniform ()
import Data.Array.Accelerate.Pretty.Schedule.Uniform ()
import Data.Kind (Type)
import Data.Bifunctor (bimap, first)
import Data.Functor.Compose
import Data.Type.Equality
import Unsafe.Coerce (unsafeCoerce)
import Data.Maybe (fromJust)
import Data.Typeable

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
  addTup       :: BackendClusterArg2 op env (v     sh e)  -> BackendClusterArg2 op env (v     sh ((), e))


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
    lhsEnvArgs (Reqr _ t   lhs) env = case getCompose $ tupRindex (justEnv env) t of
      Just (BEE (ArrArg r sh buf) f) -> bimap (valueToIn  f :>:) (ArgArray In  r sh buf :>:) $ lhsEnvArgs lhs env
      _ -> error "urk"
    lhsEnvArgs (Make t1 t2 lhs) env = case first getCompose $ takeBuffers t1 $ justEnv env of
      (Just (BEE (ArrArg r sh buf) f), env') -> bimap (valueToOut f :>:) (ArgArray Out r sh buf :>:) $ lhsEnvArgs lhs $ fromJustEnv env'
      _ -> error "urk"
    lhsEnvArgs (ExpArg lhs) (Push env (BEE (Others arg) f)) = bimap (f :>:) (arg :>:) $ lhsEnvArgs lhs env
    lhsEnvArgs (Adju   lhs) (Push env (BEE (Others arg) f)) = bimap (f :>:) (arg :>:) $ lhsEnvArgs lhs env
    lhsEnvArgs (Ignr lhs) (Push env _) = lhsEnvArgs lhs env

    lhsArgsEnv :: LeftHandSideArgs body env' scope -> BackendEnv op env scope -> BackendArgs op env body -> BackendEnv op env env'
    lhsArgsEnv Base                   _                ArgsNil            = Empty
    lhsArgsEnv (Reqr t1 t2 lhs)       env              (f :>: args) = case getCompose $ tupRindex (justEnv env) t2 of
      Just (BEE arg _) ->
        lhsArgsEnv lhs env args -- TODO think about what this function needs; do I need to overwrite or can we just recurse? 
      Nothing -> lhsArgsEnv lhs env args -- TODO perhaps none of this matters: ^^^
    lhsArgsEnv (Make t1 t2 lhs)       env              (f :>: args) = case first getCompose $ takeBuffers t1 (justEnv env) of
      (Just (BEE (ArrArg r sh buf) _), env') -> consBuffers t2 (BEE (OutArg r sh buf) (outToSh f)) (lhsArgsEnv lhs (fromJustEnv env') args)
      _ -> error "urk"
    lhsArgsEnv (ExpArg     lhs) (Push env (BEE arg _)) (f :>: args) = Push (lhsArgsEnv lhs env  args) (BEE arg f)
    lhsArgsEnv (Adju       lhs) (Push env (BEE arg _)) (f :>: args) = Push (lhsArgsEnv lhs env  args) (BEE arg f)
    lhsArgsEnv (Ignr       lhs) (Push env arg)                      args  = Push (lhsArgsEnv lhs env  args) arg

    getOutputEnv :: ClusterIO args i o -> Args env args -> BackendCluster op args -> BackendEnv op env o
    getOutputEnv P.Empty       ArgsNil           _ = Empty
    getOutputEnv (Vertical t r io) (arg@(ArgVar vars) :>: args) (info :>: infos) = put' t (BEE (ArrArg r (toGrounds vars) (error "accessing a fused away buffer")) (varToValue $ def arg env info)) (getOutputEnv io args infos) -- there is no buffer!
    getOutputEnv (Input io) (arg@(ArgArray In r sh buf) :>: args) (info :>: infos) = Push (getOutputEnv io args infos) (BEE (ArrArg r sh buf) (inToValue $ def arg env info))
    getOutputEnv (Output t s e io) (arg@(ArgArray Out r sh buf) :>: args) (info :>: infos) = put' t (BEE (ArrArg (ArrayR (arrayRshape r) e) sh (biggenBuffers s buf)) (outToValue $ shrinkOrGrow $ def arg env info)) (getOutputEnv io args infos)
    getOutputEnv (MutPut     io) (arg :>: args) (info :>: infos) = Push (getOutputEnv io args infos) (BEE (Others arg) (def arg env info))
    getOutputEnv (ExpPut'    io) (arg :>: args) (info :>: infos) = Push (getOutputEnv io args infos) (BEE (Others arg) (def arg env info))
    getOutputEnv (Trivial    io) (arg :>: args) (info :>: infos) = getOutputEnv io args infos

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
evalIO1 n (Input io) (ArgArray In r sh buf :>: args) (info :>: infos) env =
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
evalLHS1 (Reqr t _ lhs) i env = let BAE x info = tupRindex i t in Push (evalLHS1 lhs i env) $ BAE x info
evalLHS1 (Make _ t lhs) i env = let (BAE x info, i') = unconsBuffers t i in Push (evalLHS1 lhs i' env) (BAE x info)
evalLHS1 (EArg     lhs) (Push i' (BAE x info)) env = Push (evalLHS1 lhs i' env) (BAE x info)
evalLHS1 (FArg     lhs) (Push i' (BAE x info)) env = Push (evalLHS1 lhs i' env) (BAE x info)
evalLHS1 (VArg     lhs) (Push i' (BAE x info)) env = Push (evalLHS1 lhs i' env) (BAE x info)
evalLHS1 (Adju     lhs) (Push i' (BAE x info)) env = Push (evalLHS1 lhs i' env) (BAE x info)
evalLHS1 (Ignr     lhs) (Push i' (BAE _ _   )) env =       evalLHS1 lhs i' env

evalLHS2 :: EvalOp op => LeftHandSideArgs body i scope -> BackendArgEnv op env i -> Val env -> Env (FromArg' env) (OutArgs body) -> BackendArgEnv op env scope
evalLHS2 Base Empty _ Empty = Empty
evalLHS2 (Reqr t1 t2 lhs) i env o = evalLHS2 lhs i env o -- TODO ignoring here?
evalLHS2 (Make t1 t2 lhs) i env (Push o (FromArg y)) = let (BAE _ info, i') = unconsBuffers t2 i in putBuffers t1 (BAE y (shToValue info)) (evalLHS2 lhs i'  env o)
evalLHS2 (EArg   lhs) (Push i (BAE x info)) env           o  = Push (evalLHS2 lhs i env o) (BAE x info)
evalLHS2 (FArg   lhs) (Push i (BAE x info)) env           o  = Push (evalLHS2 lhs i env o) (BAE x info)
evalLHS2 (VArg   lhs) (Push i (BAE x info)) env           o  = Push (evalLHS2 lhs i env o) (BAE x info)
evalLHS2 (Adju   lhs) (Push i (BAE _ info)) env (PushFA m o) = Push (evalLHS2 lhs i env o) (BAE m info)
evalLHS2 (Ignr   lhs) (Push i (BAE x info)) env           o  = Push (evalLHS2 lhs i env o) (BAE x info)

first' :: (a -> b -> c) -> (a,b) -> (c,b)
first' f (a,b) = (f a b, b)

instance StaticClusterAnalysis op => TupRmonoid (Compose Maybe (BackendEnvElem op env)) (Value sh) where
  unit = Compose $ Compose Nothing
  pair (Compose (Compose x)) (Compose (Compose y)) = Compose . Compose $ f x y
    where
      f :: forall e1 e2
        .  Maybe (BackendEnvElem op env (Value sh e1))
        -> Maybe (BackendEnvElem op env (Value sh e2))
        -> Maybe (BackendEnvElem op env (Value sh (e1, e2)))
      f Nothing Nothing = Nothing --oh no, this means the unsafeCoerces go wrong :(
        -- instead of a Maybe, keep track of the type? :S
      f Nothing (Just (BEE (ArrArg (ArrayR shr tyr) sh buf) d)) = case unsafeCoerce @(Int :~: Int) @(e1 :~: ()) Refl of
        Refl -> Just $ BEE (ArrArg (ArrayR shr (TupRpair TupRunit tyr)) sh (TupRpair TupRunit buf)) (addTup d)
      f _ _ = undefined
  unpair xy = undefined

instance TupRmonoid (BackendEnvElem op env) (Sh sh) where

instance TupRmonoid (BackendArgEnvElem op env) (Value sh) where

instance TupRmonoid (BackendArgEnvElem op env) (Sh sh) where


justEnv     :: Env a env -> Env (Compose Maybe a) env
justEnv     = mapEnv (Compose . Just)
fromJustEnv :: Env (Compose Maybe a) env -> Env a env
fromJustEnv = mapEnv (fromJust . getCompose)


data ClusterOperations op env where
  ClusterOperations
    :: TypeR e
    -> GLeftHandSide (Buffers e) env env'
    -> [ApplyOperation op env']
    -> ClusterOperations op env

data ApplyOperation op env where
  ApplyOperation :: op f -> Args env f -> ApplyOperation op env

data Arg' env t where
  ArgArray' :: Arg env (m sh t)   -> Arg' env (m' sh t) -- Used for Value and Sh
  ArgOther' :: Arg env t          -> Arg' env t

instance Sink Arg' where
  weaken k (ArgArray' arg) = ArgArray' $ weaken k arg
  weaken k (ArgOther' arg) = ArgOther' $ weaken k arg

data BoundIO env input output where
  BoundIO
    :: TypeR e
    -> GLeftHandSide (Buffers e) env env'
    -> Env (Arg' env') input
    -> Env (Arg' env') output
    -> BoundIO env input output

clusterOperations :: Cluster op f -> Args env f -> ClusterOperations op env
clusterOperations (Cluster _ (Cluster' io ast)) args
  | BoundIO tp lhs input  _ <- bindIO io args
  = ClusterOperations tp lhs (traverseClusterAST input ast)
  where
    bindIO :: ClusterIO f' input output -> Args env f' -> BoundIO env input output
    bindIO P.Empty ArgsNil = BoundIO TupRunit (LeftHandSideWildcard TupRunit) Empty Empty
    bindIO (P.Vertical t repr@(ArrayR _ tp) io) (ArgVar sh :>: args)
      | BoundIO bndTp lhs input output <- bindIO io args
      , k <- weakenWithLHS lhs
      -- Create variables for the buffers which were fused away
      , DeclareVars lhs' k' vars <- declareVars (buffersR tp)
      , arg <- ArgArray Mut repr (mapVars GroundRscalar $ mapTupR (weaken $ k' .> k) sh) (vars weakenId)
      , input'  <- mapEnv (weaken k') input
      , output' <- mapEnv (weaken k') output
      = BoundIO
        (bndTp `TupRpair` tp)
        (lhs `LeftHandSidePair` lhs')
        (Push input' $ ArgArray' arg)
        (put' t (ArgArray' arg) output')
    bindIO (P.Input io) (arg@(ArgArray In _ _ _) :>: args)
      | BoundIO bndTp lhs input output <- bindIO io args
      , k <- weakenWithLHS lhs
      = BoundIO bndTp lhs
        (Push input  $ ArgArray' $ weaken k arg)
        (Push output $ ArgArray' $ weaken k arg)
    bindIO (P.Output t s tp io) (arg :>: args)
      -- Output which was fully preserved
      | Just Refl <- subTupPreserves tp s
      , BoundIO bndTp lhs input output <- bindIO io args
      , k <- weakenWithLHS lhs
      , arg' <- weaken k arg
      = BoundIO bndTp lhs
        (Push input $ ArgArray' arg')
        (put' t (ArgArray' arg') output)
    bindIO (P.Output t s tp io) (ArgArray Out (ArrayR shr _) sh buffers :>: args)
      -- Part of the output is used. The operation has more output, but doesn't use that.
      -- We need to declare variables for those buffers here.
      | BoundIO bndTp lhs input output <- bindIO io args
      , k <- weakenWithLHS lhs
      , DeclareMissingDistributedVars tp' lhs' k' buffers' <-
          declareMissingDistributedVars @Buffer tp (buffersR tp) s $ mapTupR (weaken k) buffers
      , arg' <- ArgArray Out (ArrayR shr tp) (mapTupR (weaken $ k' .> k) sh) (buffers' weakenId)
      , input'  <- mapEnv (weaken k') input
      , output' <- mapEnv (weaken k') output
      = BoundIO (bndTp `TupRpair` tp') (LeftHandSidePair lhs lhs')
        (Push input' $ ArgArray' arg')
        (put' t (ArgArray' arg') output')
    -- For Mut, Exp, Var and Fun we must simply put them on top of the environments.
    bindIO (P.MutPut io) (arg :>: args)
      | BoundIO bndTp lhs input output <- bindIO io args
      , k <- weakenWithLHS lhs
      , arg' <- weaken k arg
      = BoundIO bndTp lhs
        (Push input  $ ArgOther' arg')
        (Push output $ ArgOther' arg')
    bindIO (P.ExpPut io) (arg :>: args)
      | BoundIO bndTp lhs input output <- bindIO io args
      , k <- weakenWithLHS lhs
      , arg' <- weaken k arg
      = BoundIO bndTp lhs
        (Push input  $ ArgOther' arg')
        (Push output $ ArgOther' arg')
    bindIO (P.VarPut io) (arg :>: args)
      | BoundIO bndTp lhs input output <- bindIO io args
      , k <- weakenWithLHS lhs
      , arg' <- weaken k arg
      = BoundIO bndTp lhs
        (Push input  $ ArgOther' arg')
        (Push output $ ArgOther' arg')
    bindIO (P.FunPut io) (arg :>: args)
      | BoundIO bndTp lhs input output <- bindIO io args
      , k <- weakenWithLHS lhs
      , arg' <- weaken k arg
      = BoundIO bndTp lhs
        (Push input  $ ArgOther' arg')
        (Push output $ ArgOther' arg')

    traverseClusterAST
      :: Env (Arg' env') input
      -> ClusterAST op input output
      -> [ApplyOperation op env']
    traverseClusterAST _     None = []
    traverseClusterAST input (Bind lhs op ast) =
      ApplyOperation op (prjArgs input lhs)
      : traverseClusterAST (lhsArgsOutput retypeSh lhs input) ast

    prjArgs
      :: Env (Arg' env') input
      -> LeftHandSideArgs f input output
      -> Args env' f
    prjArgs input = \case
      Base -> ArgsNil
      -- Reqr t _ lhs
      --   | (arg, input') <- take' t input
      --   -> case arg of
      --       ArgArray' (ArgArray _ repr sh buffers) -> ArgArray In repr sh buffers :>: prjArgs input' lhs
      --       ArgOther' (ArgArray m _ _ _) -> case m of {}
      -- Make _ lhs
      --   | input' `Push` arg <- input
      --   -> case arg of
      --       ArgArray' (ArgArray _ repr sh buffers) -> ArgArray Out repr sh buffers :>: prjArgs input' lhs
      --       ArgOther' (ArgArray m _ _ _) -> case m of {}
      Adju lhs
        | input' `Push` arg <- input
        -> case arg of
            ArgArray' (ArgArray _ repr sh buffers) -> ArgArray Mut repr sh buffers :>: prjArgs input' lhs
            ArgOther' (ArgArray _ repr sh buffers) -> ArgArray Mut repr sh buffers :>: prjArgs input' lhs
      Ignr lhs
        | input' `Push` _ <- input
        -> prjArgs input' lhs
      EArg lhs
        | input' `Push` ArgOther' arg <- input
        -> arg :>: prjArgs input' lhs
      VArg lhs
        | input' `Push` ArgOther' arg <- input
        -> arg :>: prjArgs input' lhs
      FArg lhs
        | input' `Push` ArgOther' arg <- input
        -> arg :>: prjArgs input' lhs
  
    retypeSh :: Arg' env (Sh sh t) -> Arg' env (m' sh t)
    retypeSh (ArgArray' arg) = ArgArray' arg
    retypeSh (ArgOther' (ArgArray m _ _ _)) = case m of {}

lhsArgsOutput
  :: forall f t input output.
     (forall sh e. f (Sh sh e) -> f (Value sh e))
  -> LeftHandSideArgs t input output
  -> Env f input
  -> Env f output
lhsArgsOutput make lhsArgs input = case lhsArgs of
  Base -> Empty
  -- Reqr t t' args
  --   | (arg, input') <- take' t input
  --   -> put' t' arg $ go args input'
  -- Make t args
  --   | input' `Push` arg <- input
  --   -> put' t (make arg) $ go args input'
  Adju args
    | input' `Push` arg <- input
    -> go args input' `Push` arg
  Ignr args
    | input' `Push` arg <- input
    -> go args input' `Push` arg
  EArg args
    | input' `Push` arg <- input
    -> go args input' `Push` arg
  VArg args
    | input' `Push` arg <- input
    -> go args input' `Push` arg
  FArg args
    | input' `Push` arg <- input
    -> go args input' `Push` arg
  where
    go :: LeftHandSideArgs t' input' output' -> Env f input' -> Env f output'
    go = lhsArgsOutput make
