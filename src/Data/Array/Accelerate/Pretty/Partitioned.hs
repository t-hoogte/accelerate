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

import Data.Array.Accelerate.Pretty.Exp hiding (Val(..))
import qualified Data.Array.Accelerate.Pretty.Exp as Pretty
import Data.Array.Accelerate.Pretty.Operation
import Data.Array.Accelerate.AST.Partitioned
import Data.Array.Accelerate.AST.LeftHandSide
import Data.Array.Accelerate.Type
import Data.Array.Accelerate.Trafo.Operation.LiveVars

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
prettySingleOp topLevel (Single op soas (SA _ sortArgs) subArgs) args =
  hang 2 $ group $ vsep $
    [ annotate Execute "execute" | topLevel]
    ++
    [
      prettyOp op,
      tupled $ map (\(Exists a) -> prettyPrettyArg a) $ argsToList args'''
    ]
  where
    args' = prettyExtendArgs subArgs args
    args'' = sortArgs args'
    args''' = prettySoaArgs soas args''

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

prettyExtendArgs :: SubArgs a b -> PrettyArgs b -> PrettyArgs a
prettyExtendArgs SubArgsNil ArgsNil = ArgsNil
prettyExtendArgs (SubArgsLive subArg subArgs) (a :>: as) = prettyExtendArg subArg a :>: prettyExtendArgs subArgs as
prettyExtendArgs (SubArgsDead subArgs) (a :>: as) = case a of
  PrettyArgVarShape _ sh
    -> PrettyArgArray Out sh (TupRsingle $ Adoc' "_") :>: prettyExtendArgs subArgs as
  _ -> PrettyArgOther "?" :>: prettyExtendArgs subArgs as

prettyExtendArg :: SubArg a b -> PrettyArg b -> PrettyArg a
prettyExtendArg (SubArgOut subTup) (PrettyArgArray m sh buffers) = PrettyArgArray m sh $ prettyExtendTup subTup buffers
prettyExtendArg (SubArgOut _) _ = PrettyArgOther "?"
prettyExtendArg SubArgKeep arg = arg

prettyExtendTup :: SubTupR a b -> TupR Adoc' (Buffers b) -> TupR Adoc' (Buffers a)
prettyExtendTup SubTupRskip _ = TupRsingle $ Adoc' "_"
prettyExtendTup SubTupRkeep a = a
prettyExtendTup (SubTupRpair s1 s2) (TupRpair t1 t2) = prettyExtendTup s1 t1 `TupRpair` prettyExtendTup s2 t2

prettySoaArgs :: SOAs args expanded -> PrettyArgs expanded -> PrettyArgs args
prettySoaArgs SOArgsNil _ = ArgsNil
prettySoaArgs (SOArgsCons xs x) args
  | (arg, args') <- prettySoaArg x args
  = arg :>: prettySoaArgs xs args'

prettySoaArg :: SOA arg appendto result -> PrettyArgs result -> (PrettyArg arg, PrettyArgs appendto)
prettySoaArg SOArgSingle (a :>: as) = (a, as)
prettySoaArg (SOArgTup right left) as
  | (left', as') <- prettySoaArg left as
  , (right', as'') <- prettySoaArg right as'
  = (prettyPairArg left' right', as'')

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
