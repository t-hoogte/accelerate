{-# LANGUAGE FlexibleInstances   #-}
{-# LANGUAGE GADTs               #-}
{-# LANGUAGE InstanceSigs        #-}
{-# LANGUAGE LambdaCase          #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE PatternGuards       #-}
{-# LANGUAGE RankNTypes          #-}
{-# LANGUAGE RecordWildCards     #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications    #-}
{-# LANGUAGE TypeOperators       #-}
{-# LANGUAGE StandaloneDeriving       #-}
{-# LANGUAGE ViewPatterns        #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}
{-# LANGUAGE InstanceSigs #-}
-- |
-- Module      : Data.Array.Accelerate.Pretty.Operation
-- Copyright   : [2008..2020] The Accelerate Team
-- License     : BSD3
--
-- Maintainer  : Trevor L. McDonell <trevor.mcdonell@gmail.com>
-- Stability   : experimental
-- Portability : non-portable (GHC extensions)
--

module Data.Array.Accelerate.Pretty.Partitioned ({- instance PrettyOp (Cluster op) -}) where

import Data.Array.Accelerate.Pretty.Exp hiding (Val(..), prj)
import qualified Data.Array.Accelerate.Pretty.Exp as Pretty
import Data.Array.Accelerate.Pretty.Operation
import Data.Array.Accelerate.AST.Environment (Env)
import qualified Data.Array.Accelerate.AST.Environment as Env
import Data.Array.Accelerate.AST.Partitioned
import Data.Array.Accelerate.AST.LeftHandSide
import Data.Array.Accelerate.Type
import Data.Array.Accelerate.Trafo.Operation.LiveVars
import Data.Array.Accelerate.Error

import Prettyprinter

import Prelude hiding (exp)
import Data.Array.Accelerate.Representation.Type
import Data.Array.Accelerate.Representation.Shape
import Data.Array.Accelerate.Representation.Array
import Data.Array.Accelerate.AST.Idx (Idx (..))
import Data.Bifunctor (second)
import Data.Array.Accelerate.AST.Var (varsType)

instance PrettyOp op => PrettyOp (Clustered op) where
  prettyOp :: PrettyOp op => Clustered op t -> Adoc
  prettyOp (Clustered c _) = prettyOp c
  prettyOpWithArgs env (Clustered c _) = prettyOpWithArgs env c

instance PrettyOp op => PrettyOp (Cluster op) where
  prettyOp _ = "cluster"

  prettyOpWithArgs env cluster args
    | isSingle cluster = body
    | otherwise = annotate Execute "execute" <+> "{" <> line
      <> indent 2 body <> line <> "}"
    where
      body = fst $ prettyCluster True cluster (mapArgs (toPrettyArg env) args) 0

isSingle :: Cluster op t -> Bool
isSingle SingleOp{} = True
isSingle _ = False

data PrettyArg t where
  PrettyArgArray
    :: Modifier m
    -> Adoc -- shape variables
    -> TupR Adoc' (Buffers e) -- buffer variables
    -> PrettyArg (m sh e)

  PrettyArgVarShape
    :: Adoc -- Pretty printed as normal variables
    -> Adoc -- Pretty printed as shape
    -> PrettyArg t
  
  PrettyArgOther
    :: Adoc
    -> PrettyArg t

type PrettyArgs = PreArgs PrettyArg

newtype Adoc' t = Adoc' Adoc

prettyCluster :: Bool -> PrettyOp op => Cluster op t -> PrettyArgs t -> Int -> (Adoc, Int)
prettyCluster topLevel (SingleOp singleOp _) args fresh = (prettySingleOp topLevel singleOp args, fresh)
prettyCluster _ (Fused fusion left right) args fresh
  | (leftArgs, rightArgs, horizontals, verticals, diagonals, fresh') <- splitEnv fusion args fresh
  , (leftDoc, fresh'') <- prettyCluster False left leftArgs fresh'
  , (rightDoc, fresh''') <- prettyCluster False right rightArgs fresh''
  = ( leftDoc <> line <>
      prettyFuseList (annotate Statement "fused horizontally") horizontals <>
      prettyFuseList (annotate Statement "fused vertically") verticals <>
      prettyFuseList (annotate Statement "fused diagonally") diagonals <>
      rightDoc
    , fresh''')

prettySingleOp :: PrettyOp op => Bool -> SingleOp op t -> PrettyArgs t -> Adoc
prettySingleOp topLevel (Single op opArgs) args =
  hang 2 $ group $ vsep $
    [ annotate Execute "execute" | topLevel ]
    ++
    [
      prettyOp op,
      tupled $ map (\(Exists a) -> prettyPrettyArg $ prettyClusterArg args a) $ argsToList opArgs
    ]

prettyClusterArg :: forall f t. PrettyArgs f -> ClusterArg (FunToEnv f) t -> PrettyArg t
prettyClusterArg pArgs = \case
  ClusterArgSingle idx -> funToEnvPrj pArgs idx
  ClusterArgArray m _ _ buffers -> prettyBuffers m buffers
  where
    prettyBuffers :: Modifier m -> ClusterArgBuffers (FunToEnv f) m sh e -> PrettyArg (m sh e)
    prettyBuffers _ (ClusterArgBuffersDead _ idx) = case funToEnvPrj pArgs idx of
      PrettyArgVarShape _ sh ->
        PrettyArgArray Out sh (TupRsingle $ Adoc' "_")
      PrettyArgOther sh ->
        PrettyArgArray Out sh (TupRsingle $ Adoc' "_")
    prettyBuffers _ (ClusterArgBuffersLive _ idx) = funToEnvPrj pArgs idx
    prettyBuffers m (ClusterArgBuffersPair l r) = prettyBuffers m l `prettyPairArg` prettyBuffers m r

toPrettyArg :: Val env -> Arg env t -> PrettyArg t
toPrettyArg env (ArgArray m _ sh buffers) = PrettyArgArray m (prettyShapeVars env sh) (mapTupR (Adoc' . prettyVar env) buffers)
toPrettyArg env arg@(ArgVar vars)
  | Just _ <- typeShape $ varsType vars
  = PrettyArgVarShape (prettyArg env arg) (prettyShapeVars env vars)
toPrettyArg env arg = PrettyArgOther $ prettyArg env arg

prettyPrettyArg :: PrettyArg t -> Adoc
prettyPrettyArg (PrettyArgArray m sh buffers) = group $ vsep [prettyModifier m, "(" <> sh <> ")", prettyTupR (\_ (Adoc' doc) -> doc) 0 buffers]
prettyPrettyArg (PrettyArgVarShape doc _) = doc
prettyPrettyArg (PrettyArgOther doc) = doc

prettyPairArg :: PrettyArg (f left) -> PrettyArg (f right) -> PrettyArg (f (left, right))
prettyPairArg (PrettyArgArray m sh left) (PrettyArgArray _ _ right) = PrettyArgArray m sh $ TupRpair left right
prettyPairArg _ _ = PrettyArgOther "?"

splitEnv :: Fusion largs rargs t -> PrettyArgs t -> Int -> (PrettyArgs largs, PrettyArgs rargs, [Adoc], [Adoc], [Adoc], Int)
splitEnv EmptyF _ fresh = (ArgsNil, ArgsNil, [], [], [], fresh)
splitEnv (Vertical _ next) (a :>: as) fresh =
  let
    (left, right, horizontals, verticals, diagonals, fresh') = splitEnv next as (fresh + 1)
    sh = case a of
      PrettyArgVarShape _ sh' -> sh'
      _ -> "?"
    buffer = "%" <> viaShow fresh
    buffers = TupRsingle $ Adoc' buffer
  in
    ( PrettyArgArray Out sh buffers :>: left
    , PrettyArgArray In  sh buffers :>: right
    , horizontals
    , buffer : verticals
    , diagonals
    , fresh'
    )
splitEnv (Horizontal next) (a :>: as) fresh =
  let
    (left, right, horizontals, verticals, diagonals, fresh') = splitEnv next as fresh
    buffer = case a of
      PrettyArgArray _ _ (TupRsingle (Adoc' b)) -> b
      _ -> prettyPrettyArg a
  in
    ( a :>: left
    , a :>: right
    , buffer : horizontals
    , verticals
    , diagonals
    , fresh'
    )
splitEnv (Diagonal next) (a :>: as) fresh =
  let
    (left, right, horizontals, verticals, diagonals, fresh') = splitEnv next as fresh
    a' = case a of
      PrettyArgArray _ sh bs -> PrettyArgArray In sh bs
      _ -> PrettyArgOther "?"
    buffer = case a of
      PrettyArgArray _ _ (TupRsingle (Adoc' b)) -> b
      _ -> prettyPrettyArg a
  in
    ( a :>: left
    , a' :>: right
    , horizontals
    , verticals
    , buffer : diagonals
    , fresh'
    )
splitEnv (IntroI1 next) as fresh = splitEnv (IntroL next) as fresh
splitEnv (IntroO1 next) as fresh = splitEnv (IntroL next) as fresh
splitEnv (IntroI2 next) as fresh = splitEnv (IntroR next) as fresh
splitEnv (IntroO2 next) as fresh = splitEnv (IntroR next) as fresh
splitEnv (IntroL next) (a :>: as) fresh =
  let
    (left, right, horizontals, verticals, diagonals, fresh') = splitEnv next as fresh
  in
    (a :>: left, right, horizontals, verticals, diagonals, fresh')
splitEnv (IntroR next) (a :>: as) fresh =
  let
    (left, right, horizontals, verticals, diagonals, fresh') = splitEnv next as fresh
  in
    (left, a :>: right, horizontals, verticals, diagonals, fresh')

prettyFuseList :: Adoc -> [Adoc] -> Adoc
prettyFuseList _ [] = ""
prettyFuseList name docs = (hang 2 $ group $ vsep $ [name, tupled docs]) <> line

instance PrettyOp op => PrettyOp (FlatCluster op) where
  prettyOp _ = "cluster"
  prettyOpWithArgs env (FlatCluster lhs sizes ops) args
    | [op] <- ops = -- Cluster of one operation: print as normal operation
      prettyFlatOp True env'' op
    | otherwise =
      annotate Execute "execute" <+> "{" <> line
      <> indent 2 (vsep body) <> line <> "}"
    where
      env' = toEnv $ mapArgs (toPrettyArg env) args
      (env'', count) = prettyFusedLHS env' env' 0 lhs sizes
      ops' = map (prettyFlatOp False env'') ops
      body
        | count == 0 = ops'
        | count < 10 = (let_ <+> hsep (punctuate comma
            [ "%" <> viaShow i | i <- [0..count] ]
          )) : ops'
        | otherwise = (let_ <+> "%0 .. %" <> viaShow count) : ops'

toEnv :: PreArgs f args -> Env f (FunToEnv args)
toEnv ArgsNil = Env.Empty
toEnv (a :>: as) = toEnv as `Env.Push` a

prettyFusedLHS :: Env PrettyArg env0 -> Env PrettyArg env -> Int -> LeftHandSide OutR t env env' -> OutShapes env0 t -> (Env PrettyArg env', Int)
prettyFusedLHS _ env fresh (LeftHandSideWildcard _) _ = (env, fresh)
prettyFusedLHS env0 env fresh (LeftHandSideSingle _) (TupRsingle (OutShape idx)) =
  (env `Env.Push` arg, fresh + 1)
  where
    arg = case Env.prj' idx env0 of
      PrettyArgVarShape _ sh
        -> PrettyArgArray Out sh $ TupRsingle $ Adoc' $ "%" <> viaShow fresh
      PrettyArgOther sh
        -> PrettyArgArray Out sh $ TupRsingle $ Adoc' $ "%" <> viaShow fresh
prettyFusedLHS env0 env fresh (LeftHandSidePair lhs1 lhs2) (TupRpair o1 o2)
  | (env', fresh') <- prettyFusedLHS env0 env fresh lhs1 o1
  = prettyFusedLHS env0 env' fresh' lhs2 o2
prettyFusedLHS _ _ _ _ _ = internalError "Tuple mismatch"

prettyFlatOp :: PrettyOp op => Bool -> Env PrettyArg env -> FlatOp op env -> Adoc
prettyFlatOp single env (FlatOp op args) =
  hang 2 $ group $ vsep $
    [ annotate Execute "execute" | single ]
    ++
    [
      prettyOp op,
      tupled $ map (\(Exists a) -> prettyPrettyArg $ prettyFlatArg env a) $ argsToList args
    ]

prettyFlatArg :: forall env t. Env PrettyArg env -> FlatArg env t -> PrettyArg t
prettyFlatArg env (FlatArgSingle idx) = Env.prj' idx env
prettyFlatArg env (FlatArgArray _ _ tp bs) = go tp bs
  where
    go :: TypeR e -> FlatArgBuffers env m sh e -> PrettyArg (m sh e)
    go (TupRpair t1 t2) (FlatArgBuffersPair l r)
      | PrettyArgArray m' sh l' <- go t1 l
      , PrettyArgArray _ _ r' <- go t2 r
      = PrettyArgArray m' sh (TupRpair l' r')
      | otherwise = PrettyArgOther "?"
    go _ (FlatArgBuffersLive _ idx) = Env.prj' idx env
    go _ (FlatArgBuffersFused _ idx) = case Env.prj' idx env of
      PrettyArgArray _ sh (TupRsingle (Adoc' d))
        -> PrettyArgArray In sh
          $ TupRsingle $ Adoc' $ d <> " [fused]"
      _ -> PrettyArgOther "?"
    go _ _ = internalError "Tuple mismatch"
