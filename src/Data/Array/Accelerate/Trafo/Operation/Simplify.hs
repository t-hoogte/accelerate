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
import Data.Array.Accelerate.Analysis.Match
import qualified Data.Array.Accelerate.Trafo.Exp.Simplify   as Exp
import Data.Array.Accelerate.Trafo.Exp.Substitution
import Data.Array.Accelerate.Trafo.Var
import Data.Array.Accelerate.Trafo.Substitution             hiding ( weakenArrayInstr )
import Data.Array.Accelerate.Trafo.WeakenedEnvironment
import Data.Array.Accelerate.Trafo.Operation.Substitution
import Data.Array.Accelerate.Trafo.LiveVars                 ( SubTupR(..), subTupR, subTupRpair )
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
    in (awhileSimplifyInvariant us cond' step' initial', setC `IdxSet.union` setS)

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

unionSubTupR :: SubTupR t s -> SubTupR t s' -> Exists (SubTupR t)
unionSubTupR SubTupRskip s = Exists s
unionSubTupR s SubTupRskip = Exists s
unionSubTupR (SubTupRpair l1 r1) (SubTupRpair l2 r2)
  | Exists l <- unionSubTupR l1 l2
  , Exists r <- unionSubTupR r1 r2
  = Exists $ subTupRpair l r
unionSubTupR _ _ = Exists SubTupRkeep


awhileSimplifyInvariant
  :: Uniquenesses a
  -> PreOpenAfun op env (a -> PrimBool)
  -> PreOpenAfun op env (a -> a)
  -> GroundVars     env a
  -> PreOpenAcc  op env a
awhileSimplifyInvariant us cond step initial = case awhileDropInvariantFun step of
  Exists SubTupRkeep -> Awhile us cond step initial
  Exists sub
    | DeclareVars lhs k value <- declareVars $ subTupR sub tp ->
      Alet lhs (subTupR sub us)
        (Awhile (subTupR sub us)
          (subTupFunctionArgument sub initial cond)
          (subTupFunctionArgument sub initial $ subTupFunctionResult sub step)
          (subTupR sub initial))
        (Return $ subTupResult sub (mapTupR (weaken k) initial) (value weakenId))
  where
    tp = case cond of
      Alam lhs _ -> lhsToTupR lhs
      Abody body -> groundFunctionImpossible $ groundsR body

awhileDropInvariantFun :: OperationAfun op env (t -> t) -> Exists (SubTupR t)
awhileDropInvariantFun (Alam lhs (Abody body)) = awhileDropInvariant (lhsMaybeVars lhs) body
awhileDropInvariantFun (Alam lhs (Alam _ _))   = groundFunctionImpossible (lhsToTupR lhs)
awhileDropInvariantFun (Abody body)            = groundFunctionImpossible (groundsR body)

awhileDropInvariant :: MaybeVars GroundR env t -> OperationAcc op env t -> Exists (SubTupR t)
awhileDropInvariant argument = \case
  Return vars
    -> matchReturn argument vars
  Alet (LeftHandSideWildcard _) _ _ body
    -> awhileDropInvariant argument body
  Alet lhs _ _ body
    -> awhileDropInvariant (mapTupR (weaken $ weakenWithLHS lhs) argument) body
  Acond _ t f
    | Exists subTupT <- awhileDropInvariant argument t
    , Exists subTupF <- awhileDropInvariant argument f
    -> unionSubTupR subTupT subTupF
  _ -> Exists SubTupRkeep -- No invariant variables
  where
    matchReturn :: MaybeVars GroundR env t' -> GroundVars env t' -> Exists (SubTupR t')
    matchReturn (TupRpair a1 a2) (TupRpair v1 v2)
      | Exists s1 <- matchReturn a1 v1
      , Exists s2 <- matchReturn a2 v2
      = Exists $ subTupRpair s1 s2
    matchReturn (TupRsingle (JustVar arg)) (TupRsingle var)
      | Just Refl <- matchVar arg var = Exists SubTupRskip
    matchReturn _ _ = Exists SubTupRkeep

subTupFunctionResult :: SubTupR t t' -> OperationAfun op env (ta -> t) -> OperationAfun op env (ta -> t')
subTupFunctionResult sub (Alam lhs (Abody body)) = Alam lhs $ Abody $ subTupAcc sub body
subTupFunctionResult _ _ = internalError "Illegal function"

subTupAcc :: SubTupR t t' -> OperationAcc op env t -> OperationAcc op env t'
subTupAcc sub = \case
  Return vars -> Return $ subTupR sub vars
  Alet lhs us bnd body -> Alet lhs us bnd $ subTupAcc sub body
  Acond c t f -> Acond c (subTupAcc sub t) (subTupAcc sub f)
  _ -> internalError "Cannot subTup this program"

subTupFunctionArgument :: SubTupR t t' -> GroundVars env t -> OperationAfun op env (t -> tr) -> OperationAfun op env (t' -> tr)
subTupFunctionArgument sub initial (Alam lhs body)
  | SubTupSubstitution lhs' k <- subTupSubstitution sub lhs initial
  = Alam lhs' $ weaken k body
subTupFunctionArgument _ _ (Abody body) = groundFunctionImpossible $ groundsR body

subTupResult :: SubTupR t t' -> GroundVars env t -> GroundVars env t' -> GroundVars env t
subTupResult SubTupRkeep _ result = result
subTupResult SubTupRskip initial _ = initial
subTupResult (SubTupRpair s1 s2) (TupRpair i1 i2) (TupRpair r1 r2) = subTupResult s1 i1 r1 `TupRpair` subTupResult s2 i2 r2
subTupResult _ _ _ = internalError "Tuple mismatch"

data SubTupSubstitution env env1 t t' where
  SubTupSubstitution
    :: GLeftHandSide t' env1 env2
    -> env :> env2
    -> SubTupSubstitution env env1 t t'

subTupSubstitution :: SubTupR t t' -> GLeftHandSide t env env' -> GroundVars env t -> SubTupSubstitution env' env t t'
subTupSubstitution SubTupRskip lhs vars = SubTupSubstitution (LeftHandSideWildcard TupRunit) (go lhs vars weakenId)
  where
    go :: GLeftHandSide s env1 env2 -> GroundVars env s -> env1 :> env -> env2 :> env
    go (LeftHandSideWildcard _) _ k = k
    go (LeftHandSideSingle _)   (TupRsingle (Var _ ix)) k = Weaken $ \case
      ZeroIdx -> ix
      SuccIdx ix' -> k >:> ix'
    go (LeftHandSidePair l1 l2) (TupRpair v1 v2) k = go l2 v2 $ go l1 v1 k
    go _ _ _ = internalError "Tuple mismatch"
subTupSubstitution SubTupRkeep lhs _ = SubTupSubstitution lhs weakenId
subTupSubstitution (SubTupRpair s1 s2) (LeftHandSidePair l1 l2) (TupRpair v1 v2)
  | SubTupSubstitution l1' k1 <- subTupSubstitution s1 l1 v1
  , Exists l2'' <- rebuildLHS l2
  , SubTupSubstitution l2' k2 <- subTupSubstitution s2 l2'' (mapTupR (weaken $ weakenWithLHS l1') v2)
  = SubTupSubstitution (LeftHandSidePair l1' l2') (k2 .> sinkWithLHS l2 l2'' k1)
subTupSubstitution _ _ _ = internalError "Tuple mismatch"
