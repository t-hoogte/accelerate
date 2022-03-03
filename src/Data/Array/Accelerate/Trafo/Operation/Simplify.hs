{-# LANGUAGE FlexibleInstances   #-}
{-# LANGUAGE GADTs               #-}
{-# LANGUAGE KindSignatures      #-}
{-# LANGUAGE LambdaCase          #-}
{-# LANGUAGE MultiWayIf          #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE PatternGuards       #-}
{-# LANGUAGE RankNTypes          #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections       #-}
{-# LANGUAGE TypeApplications    #-}
{-# LANGUAGE TypeFamilies        #-}
{-# LANGUAGE TypeOperators       #-}
{-# OPTIONS_HADDOCK hide #-}
-- |
-- Module      : Data.Array.Accelerate.Trafo.Operation.Simplify
-- Copyright   : [2012..2020] The Accelerate Team
-- License     : BSD3
--
-- Maintainer  : Trevor L. McDonell <trevor.mcdonell@gmail.com>
-- Stability   : experimental
-- Portability : non-portable (GHC extensions)
--

module Data.Array.Accelerate.Trafo.Operation.Simplify (
  simplify, simplifyFun
) where

import Data.Array.Accelerate.AST.Environment
import Data.Array.Accelerate.AST.Idx
import Data.Array.Accelerate.AST.IdxSet                     ( IdxSet )
import qualified Data.Array.Accelerate.AST.IdxSet           as IdxSet
import Data.Array.Accelerate.AST.LeftHandSide
import Data.Array.Accelerate.AST.Operation
import Data.Array.Accelerate.Error
import Data.Array.Accelerate.Array.Buffer
import Data.Array.Accelerate.Representation.Type
import qualified Data.Array.Accelerate.Trafo.Exp.Simplify   as Exp
import Data.Array.Accelerate.Trafo.Exp.Substitution
import Data.Array.Accelerate.Trafo.Substitution             hiding ( weakenArrayInstr )
import Data.Array.Accelerate.Trafo.WeakenedEnvironment
import Data.Array.Accelerate.Trafo.Operation.Substitution
import Data.Maybe                                           ( mapMaybe )

data Info env t where
  InfoConst :: t         -> Info env t
  InfoAlias :: Idx env t -> Info env t
  InfoUnit  :: Idx env t -> Info env (Buffer t)
  InfoNone  ::              Info env t

newtype InfoEnv env = InfoEnv { unInfoEnv :: WEnv Info env }

emptySimplifyEnv :: InfoEnv ()
emptySimplifyEnv = InfoEnv wempty

instance Sink Info where
  weaken k (InfoAlias idx) = InfoAlias $ weaken k idx
  weaken _ (InfoConst c)   = InfoConst c
  weaken k (InfoUnit idx)  = InfoUnit $ weaken k idx
  weaken _ InfoNone        = InfoNone

infoFor :: Idx env t -> InfoEnv env -> Info env t
infoFor ix (InfoEnv env) = wprj ix env

-- Substitutions for aliasing.
-- This substitution only assures that we use the original declaration instead
-- of the alias. It does not remove the definition of the alias, a later pass
-- should remove that (with a (strongly) live variable analysis).
--
substitute :: InfoEnv env -> env :> env
substitute env = Weaken $ \idx -> case infoFor idx env of
  InfoAlias idx' -> idx'
  _              -> idx

simplifyFun :: OperationAfun op () t -> OperationAfun op () t
simplifyFun = fst . simplifyFun' emptySimplifyEnv

-- Returns the simplified function and a set of array variables which may have been written to
simplifyFun' :: InfoEnv env -> OperationAfun op env t -> (OperationAfun op env t, IdxSet env)
simplifyFun' env (Alam lhs f) = (Alam lhs f', IdxSet.drop' lhs set)
  where
    env' = bindEnv lhs env
    (f', set) = simplifyFun' env' f
simplifyFun' env (Abody body)  = (Abody body', set)
  where
    (body', set) = simplify' env body

simplify :: OperationAcc op () t -> OperationAcc op () t
simplify = fst . simplify' emptySimplifyEnv

-- Returns the simplified program and a set of array variables which may have been written to
simplify' :: InfoEnv env -> OperationAcc op env t -> (OperationAcc op env t, IdxSet env)
simplify' env = \case
  Exec op args ->
    let
      args' = mapArgs (simplifyArg env) args
    in
      (Exec op args', outputArrays args')
  Return vars ->
    -- Note that we do not need to check for writes to variables here.
    -- This construct may cause aliassing of variables, but an aliassed
    -- variable cannot be unique and thus we do not need to signal the
    -- original variable as mutated if it's returned.
    (Return $ mapTupR (weaken $ substitute env) vars, IdxSet.empty)
  Compute expr ->
    let expr' = simplifyExp env expr
    in
      if
        | Just vars <- extractParams expr' ->
          (Return $ mapTupR (\(Var tp ix) -> Var (GroundRscalar tp) ix) vars, IdxSet.empty)
        | otherwise ->
          (Compute expr', IdxSet.empty)
  Alet lhs us bnd body ->
    let
      (bnd', setBnd) = simplify' env bnd
      env' = bindingEnv lhs bnd' $ InfoEnv $ wremoveSet InfoNone setBnd $ unInfoEnv env
      (body', setBody) = simplify' env' body
    in
      (bindLet lhs us bnd' body', setBnd `IdxSet.union` IdxSet.drop' lhs setBody)
  Alloc shr tp sh -> (Alloc shr tp $ mapTupR (weaken $ substitute env) sh, IdxSet.empty)
  Use tp n buffer -> (Use tp n buffer, IdxSet.empty)
  Unit var -> (Unit $ weaken (substitute env) var, IdxSet.empty)
  Acond cond true false ->
    let
      (true',  setT) = simplify' env true
      (false', setF) = simplify' env false
      set = IdxSet.union setT setF
    in case infoFor (varIdx cond) env of
        InfoConst 0  -> (false', setF)
        InfoConst _  -> (true', setT)
        InfoAlias ix -> (Acond (cond{varIdx = ix}) true' false', set)
        InfoNone     -> (Acond cond                true' false', set)
  Awhile us cond step initial ->
    let
      (cond', setC) = simplifyFun' env cond
      (step', setS) = simplifyFun' env step
      initial' = mapTupR (weaken $ substitute env) initial
      -- Similar to Return, we don't need to track aliassing in 'initial' to find whether
      -- variables may be mutated: aliassed buffers cannot be unique.
    in (Awhile us cond' step' initial', setC `IdxSet.union` setS)

bindLet :: forall env env' op t s. GLeftHandSide t env env' -> Uniquenesses t -> OperationAcc op env t -> OperationAcc op env' s -> OperationAcc op env s
bindLet (LeftHandSidePair l1 l2) (TupRpair u1 u2) (Compute (Pair e1 e2))
  = bindLet l1 u1 (Compute e1) . bindLet l2 u2 (Compute $ weakenArrayInstr (weakenWithLHS l1) e2)
bindLet (LeftHandSidePair l1 l2) (TupRpair u1 u2) (Return (TupRpair v1 v2))
  = bindLet l1 u1 (Return v1) . bindLet l2 u2 (Return $ mapTupR (weaken $ weakenWithLHS l1) v2)
bindLet lhs@(LeftHandSideWildcard _) us bnd = case bnd of
  Compute _ -> id -- Drop this binding, as it has no observable effect
  Return _  -> id
  Alloc{}   -> id
  Use{}     -> id
  Unit _    -> id
  _ -> Alet lhs us bnd -- Might have a side effect
bindLet lhs@(LeftHandSideSingle _) us (Compute (ArrayInstr (Parameter (Var tp ix)) _))
  = Alet lhs us $ Return $ TupRsingle $ Var (GroundRscalar tp) ix
bindLet lhs us bnd = Alet lhs us bnd

bindingEnv :: forall op t env env'. GLeftHandSide t env env' -> OperationAcc op env t -> InfoEnv env -> InfoEnv env'
bindingEnv lhs (Compute expr) (InfoEnv environment) = InfoEnv $ weaken (weakenWithLHS lhs) $ go lhs expr environment
  where
    go :: GLeftHandSide s env1 env2 -> Exp env s -> WEnv' Info env env1 -> WEnv' Info env env2
    go (LeftHandSideSingle _) e env
      | ArrayInstr (Parameter var) _ <- e = wpush' env (InfoAlias $ varIdx var)
      | Const _ c <- e = wpush' env (InfoConst c)
      | otherwise = wpush' env InfoNone

    go (LeftHandSidePair l1 l2) (Pair e1 e2) env
      = go l2 e2 $ go l1 e1 env

    go (LeftHandSideWildcard _) _ env = env

    go l _ env = goUnknown l env

    goUnknown :: GLeftHandSide s env1 env2 -> WEnv' Info env env1 -> WEnv' Info env env2
    goUnknown (LeftHandSideSingle _)   env = wpush' env InfoNone
    goUnknown (LeftHandSideWildcard _) env = env
    goUnknown (LeftHandSidePair l1 l2) env = goUnknown l2 $ goUnknown l1 env
bindingEnv lhs (Return variables) (InfoEnv environment) = InfoEnv $ weaken (weakenWithLHS lhs) $ go lhs variables environment
  where
    go :: GLeftHandSide s env1 env2 -> GroundVars env s -> WEnv' Info env env1 -> WEnv' Info env env2
    go (LeftHandSideSingle _)   (TupRsingle (Var _ ix)) env = wpush' env $ InfoAlias ix
    go (LeftHandSidePair l1 l2) (TupRpair v1 v2)        env = go l2 v2 $ go l1 v1 env
    go (LeftHandSideWildcard _) _                       env = env
    go _                        _                       _   = internalError "Tuple mismatch"
bindingEnv (LeftHandSideSingle _) (Unit (Var _ idx)) (InfoEnv env) = InfoEnv $ wpush env $ InfoUnit $ SuccIdx idx
bindingEnv lhs _ env = bindEnv lhs env

outputArrays :: Args env args -> IdxSet env
outputArrays = IdxSet.fromList . mapMaybe f . argsVars
  where
    f :: Exists (Var AccessGroundR env) -> Maybe (Exists (Idx env))
    f (Exists (Var (AccessGroundRbuffer In _) _)) = Nothing
    f (Exists (Var (AccessGroundRbuffer _ _) idx)) = Just (Exists idx) -- Out or Mut
    f _ = Nothing

simplifyExp :: forall env t. InfoEnv env -> Exp env t -> Exp env t
simplifyExp env = Exp.simplifyExp . runIdentity . rebuildArrayInstrOpenExp (simplifyArrayInstr env)

simplifyExpFun :: forall env t. InfoEnv env -> Fun env t -> Fun env t
simplifyExpFun env = Exp.simplifyFun . runIdentity . rebuildArrayInstrFun (simplifyArrayInstr env)

simplifyArrayInstr :: InfoEnv env -> RebuildArrayInstr Identity (ArrayInstr env) (ArrayInstr env)
simplifyArrayInstr env instr@(Parameter (Var tp idx)) = case infoFor idx env of
  InfoAlias idx' -> simplifyArrayInstr env (Parameter $ Var tp idx')
  InfoConst c    -> Identity $ const $ Const tp c
  InfoUnit _     -> bufferImpossible tp
  InfoNone       -> Identity $ \arg -> ArrayInstr instr arg
simplifyArrayInstr env instr@(Index (Var tp idx)) = case infoFor idx env of
  InfoAlias idx' -> simplifyArrayInstr env (Index $ Var tp idx')
  InfoUnit idx'  -> Identity $ const $ runIdentity (simplifyArrayInstr env $ Parameter $ Var eltTp idx') Nil
  _              -> Identity $ \arg -> ArrayInstr instr arg
  where
    eltTp = case tp of
      GroundRscalar t -> bufferImpossible t
      GroundRbuffer t -> t

simplifyArg :: InfoEnv env -> Arg env t -> Arg env t
simplifyArg env (ArgVar var)  = ArgVar $ mapTupR (weaken $ substitute env) var
simplifyArg env (ArgExp expr) = ArgExp $ simplifyExp env expr
simplifyArg env (ArgFun fun)  = ArgFun $ simplifyExpFun env fun
simplifyArg env (ArgArray m repr sh buffers)
  = ArgArray m repr (mapTupR (weaken $ substitute env) sh) (mapTupR (weaken $ substitute env) buffers)

bindEnv :: GLeftHandSide t env env' -> InfoEnv env -> InfoEnv env'
bindEnv lhs (InfoEnv env') = InfoEnv $ go lhs $ weaken k env'
  where
    k = weakenWithLHS lhs

    go :: GLeftHandSide t env1 env1' -> WEnv' Info env' env1 -> WEnv' Info env' env1'
    go (LeftHandSideWildcard _) env1 = env1
    go (LeftHandSideSingle _)   env1 = wpush' env1 InfoNone
    go (LeftHandSidePair l1 l2) env1 = go l2 $ go l1 env1
