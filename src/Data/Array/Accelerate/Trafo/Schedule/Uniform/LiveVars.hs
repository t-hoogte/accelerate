{-# LANGUAGE ConstraintKinds     #-}
{-# LANGUAGE FlexibleInstances   #-}
{-# LANGUAGE GADTs               #-}
{-# LANGUAGE KindSignatures      #-}
{-# LANGUAGE LambdaCase          #-}
{-# LANGUAGE MultiWayIf          #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE PatternGuards       #-}
{-# LANGUAGE RankNTypes          #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell     #-}
{-# LANGUAGE TupleSections       #-}
{-# LANGUAGE TypeApplications    #-}
{-# LANGUAGE TypeFamilies        #-}
{-# LANGUAGE TypeOperators       #-}
{-# LANGUAGE ViewPatterns        #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}
{-# OPTIONS_HADDOCK hide #-}
-- |
-- Module      : Data.Array.Accelerate.Trafo.Schedule.Uniform.LiveVars
-- Copyright   : [2012..2020] The Accelerate Team
-- License     : BSD3
--
-- Maintainer  : Trevor L. McDonell <trevor.mcdonell@gmail.com>
-- Stability   : experimental
-- Portability : non-portable (GHC extensions)
--

module Data.Array.Accelerate.Trafo.Schedule.Uniform.LiveVars (
  stronglyLiveVariablesFun
) where

import Data.Array.Accelerate.AST.Environment
import Data.Array.Accelerate.AST.Idx
import Data.Array.Accelerate.AST.IdxSet ( IdxSet(..) )
import qualified Data.Array.Accelerate.AST.IdxSet as IdxSet
import Data.Array.Accelerate.AST.LeftHandSide
import Data.Array.Accelerate.AST.Schedule.Uniform
import Data.Array.Accelerate.Error
import Data.Array.Accelerate.Representation.Type
import Data.Array.Accelerate.Trafo.Exp.Substitution
import Data.Array.Accelerate.Trafo.LiveVars
import Data.Array.Accelerate.Trafo.Substitution

import Data.Maybe

stronglyLiveVariablesFun :: UniformScheduleFun kernel () t -> UniformScheduleFun kernel () t
stronglyLiveVariablesFun schedule = schedule' ReEnvEnd
  where
    LVAnalysis _ schedule' = stronglyLiveVariablesFun' emptyLivenessEnv schedule

stronglyLiveVariablesFun' :: LivenessEnv env -> UniformScheduleFun kernel env t -> LVAnalysis (UniformScheduleFun kernel) env t
stronglyLiveVariablesFun' liveness = \case
  Sbody body
    | LVAnalysis' liveness2 body' <- stronglyLiveVariables' liveness body
      -> LVAnalysis liveness2 $ \re -> Sbody $ body' re
  Slam lhs f
    | liveness1 <-
      setIndicesLive
        (mapMaybe (\(Exists (Var tp idx)) -> if isOutput tp then Just $ Exists idx else Nothing) $ lhsVars lhs)
        (pushLivenessEnv lhs liveness)
    , LVAnalysis liveness2 f' <- stronglyLiveVariablesFun' liveness1 f
      -> LVAnalysis
          (dropLivenessEnv lhs liveness2)
          $ \re -> if -- A one-way "multi way if" to pattern match on a GADT
            | BindLiveness lhs' re' <- bind lhs re liveness2
              -> Slam lhs' $ f' re'

stronglyLiveVariables' :: LivenessEnv env -> UniformSchedule kernel env -> LVAnalysis' (UniformSchedule kernel) env
stronglyLiveVariables' liveness = \case
  Return -> LVAnalysis' liveness $ const Return
  Alet lhs binding body ->
    let
      liveness1 = analyseBinding (weakenWithLHS lhs) (lhsIndices lhs) binding $ pushLivenessEnv lhs liveness
      LVAnalysis' liveness2 body' = stronglyLiveVariables' liveness1 body
    in
      LVAnalysis'
        (dropLivenessEnv lhs liveness2)
        $ \re -> if -- A one-way "multi way if" to pattern match on a GADT
          | BindLiveness lhs' re' <- bind lhs re liveness2 -> case lhs' of
            LeftHandSideWildcard _ -> body' re' -- Entire binding wasn't used
            _ -> Alet lhs' (reEnvBinding re binding) (body' re')
  Effect (SignalAwait signals) (Effect (SignalResolve resolvers) Return) ->
    let
      liveness1 = setLivenessImplications (IdxSet.fromList $ map Exists resolvers) (IdxSet.fromList $ map Exists signals) liveness
    in
      LVAnalysis'
        liveness1
        $ \re -> await (reEnvIndices' re signals) $ resolve (reEnvIndices' re resolvers) Return
  Effect effect next ->
    let
      liveness1 = analyseEffect effect liveness
      LVAnalysis' liveness2 next' = stronglyLiveVariables' liveness1 next
    in
      LVAnalysis'
        liveness2
        $ \re -> reEnvEffect re effect $ next' re
  Acond condition true false next ->
    let
      liveness1 = setLive (varIdx condition) liveness
      LVAnalysis' liveness2 true'  = stronglyLiveVariables' liveness1 true
      LVAnalysis' liveness3 false' = stronglyLiveVariables' liveness2 false
      LVAnalysis' liveness4 next'  = stronglyLiveVariables' liveness3 next
    in
      LVAnalysis'
        liveness4
        $ \re -> Acond
          (expectJust $ reEnvVar re condition)
          (true' re)
          (false' re)
          (next' re)
  Awhile io step initial next ->
    let
      -- TODO: We could track which parts of the state are used
      liveness1 = setVarsLive initial liveness
      LVAnalysis  liveness2 step' = stronglyLiveVariablesFun' liveness1 step
      LVAnalysis' liveness3 next' = stronglyLiveVariables' liveness2 next
    in
      LVAnalysis'
        liveness3
        $ \re -> Awhile io
          (step' re)
          (expectJust $ reEnvVars re initial)
          (next' re)
  Fork a b ->
    let
      LVAnalysis' liveness1 a' = stronglyLiveVariables' liveness  a
      LVAnalysis' liveness2 b' = stronglyLiveVariables' liveness1 b
    in
      LVAnalysis'
        liveness2
        $ \re -> Fork
          (a' re)
          (b' re)

analyseBinding :: env :> env' -> IdxSet env' -> Binding env t -> LivenessEnv env' -> LivenessEnv env'
analyseBinding k lhs binding liveness = case binding of
  Compute expr ->
    let
      -- If the LHS of the binding is live, then all free variables of this
      -- expression are live as well.
      free = map (\(Exists (Var _ idx)) -> Exists $ k >:> idx) $ expGroundVars expr
    in
      setLivenessImplications lhs (IdxSet.fromList free) liveness
  NewSignal
    | IdxSet (_ `PPush` _ `PPush` _) <- lhs ->
      -- If the signal is live, then the resolver is live as well.
      setLivenessImplies
        (SuccIdx ZeroIdx) 
        (IdxSet.singleton ZeroIdx)
        liveness
    | otherwise -> liveness
  NewRef _
    | IdxSet (_ `PPush` _ `PPush` _) <- lhs ->
      -- If the Ref is live, then the OutputRef is live as well.
      setLivenessImplies
        (SuccIdx ZeroIdx) 
        (IdxSet.singleton ZeroIdx)
        liveness
    | otherwise -> liveness
  Alloc _ _ sh ->
    -- If this buffer is live, then the shape variables are live as well.
    setLivenessImplications lhs (IdxSet.fromVars $ mapTupR (weaken k) sh) liveness
  Use _ _ _ -> liveness
  Unit (Var _ idx) -> -- If the lhs is live, then the argument of Unit is live as well.
    setLivenessImplications lhs (IdxSet.singleton $ k >:> idx) liveness
  RefRead (Var _ idx) -> -- If the lhs is live, then the Ref is live as well.
    setLivenessImplications lhs (IdxSet.singleton $ k >:> idx) liveness

reEnvBinding :: ReEnv env subenv -> Binding env t -> Binding subenv t
reEnvBinding re = \case
  Compute expr     -> Compute $ mapArrayInstr (reEnvArrayInstr re) expr
  NewSignal        -> NewSignal
  NewRef tp        -> NewRef tp
  Alloc shr tp sh  -> Alloc shr tp $ expectJust $ reEnvVars re sh
  Use tp sh buffer -> Use tp sh buffer
  Unit var         -> Unit $ expectJust $ reEnvVar re var
  RefRead var      -> RefRead $ expectJust $ reEnvVar re var

reEnvArrayInstr :: ReEnv env subenv -> ArrayInstr env t -> ArrayInstr subenv t
reEnvArrayInstr re (Parameter var) = Parameter $ expectJust $ reEnvVar re var
reEnvArrayInstr re (Index buffer)  = Index $ expectJust $ reEnvVar re buffer

analyseEffect :: Effect kernel env -> LivenessEnv env -> LivenessEnv env
analyseEffect (Exec _ args) liveness = setIndicesLive (argsIndices args) liveness
analyseEffect (SignalAwait signals) liveness = setIndicesLive (map Exists signals) liveness
analyseEffect (SignalResolve _) liveness = liveness
analyseEffect (RefWrite ref value) liveness = setLivenessImplies (varIdx ref) (IdxSet.singleton $ varIdx value) liveness

reEnvEffect :: ReEnv env subenv -> Effect kernel env -> UniformSchedule kernel subenv -> UniformSchedule kernel subenv
reEnvEffect re = \case
  Exec kernel args -> Effect $ Exec kernel $ mapArgs (reEnvArg re) args
  SignalAwait signals -> Effect $ SignalAwait $ reEnvIndices' re signals
  SignalResolve resolvers -> resolve $ reEnvIndices' re resolvers
  RefWrite ref value -> case (reEnvVar re ref, reEnvVar re value) of
    (Just ref', Just value') -> Effect $ RefWrite ref' value'
    (Nothing  , _          ) -> id
    (Just _   , Nothing    ) -> internalError "Substitution in live variable analysis failed. A reference was live, but the value written to it was dead."

reEnvArg :: ReEnv env subenv -> SArg env t -> SArg subenv t
reEnvArg re (SArgScalar   var) = SArgScalar   $ expectJust $ reEnvVar re var
reEnvArg re (SArgBuffer m var) = SArgBuffer m $ expectJust $ reEnvVar re var

argsIndices :: SArgs env t -> [Exists (Idx env)]
argsIndices = map (\(Exists a) -> argIndex a) . argsToList

argIndex :: SArg env t -> Exists (Idx env)
argIndex (SArgScalar   var) = Exists $ varIdx var
argIndex (SArgBuffer _ var) = Exists $ varIdx var

isOutput :: BaseR t -> Bool
isOutput BaseRrefWrite{} = True
isOutput BaseRsignalResolver = True
isOutput _ = False

expectJust :: HasCallStack => Maybe a -> a
expectJust (Just a) = a
expectJust Nothing  = internalError "Substitution in live variable analysis failed. A variable which was assumed to be dead appeared to be live."
