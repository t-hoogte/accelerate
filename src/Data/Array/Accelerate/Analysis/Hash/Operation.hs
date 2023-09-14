{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE GADTs               #-}
{-# LANGUAGE MagicHash           #-}
{-# LANGUAGE PatternGuards       #-}
{-# LANGUAGE RankNTypes          #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell     #-}
{-# LANGUAGE TypeApplications    #-}
{-# OPTIONS_HADDOCK hide #-}
-- |
-- Module      : Data.Array.Accelerate.Analysis.Hash
-- Copyright   : [2017..2020] The Accelerate Team
-- License     : BSD3
--
-- Maintainer  : Trevor L. McDonell <trevor.mcdonell@gmail.com>
-- Stability   : experimental
-- Portability : non-portable (GHC extensions)
--

module Data.Array.Accelerate.Analysis.Hash.Operation ( EncodeOperation(..), hashOperation ) where

import Data.Array.Accelerate.Analysis.Hash.Exp
import Data.Array.Accelerate.AST.Idx
import Data.Array.Accelerate.AST.Var
import Data.Array.Accelerate.AST.Partitioned
import Data.Array.Accelerate.Trafo.LiveVars
import Data.Array.Accelerate.Trafo.Partitioning.ILP.Graph

import Crypto.Hash.XKCP
import Data.ByteString.Builder

hashOperation :: EncodeOperation op => op t -> Args env t -> Hash
hashOperation op args
  = hashlazy
  $ toLazyByteString
  $ encodeOperation op <> encodePreArgs encodeArg args

class EncodeOperation op where
  encodeOperation :: op t -> Builder

instance (MakesILP op, EncodeOperation op) => EncodeOperation (Cluster op) where
  -- encodeOperation (Cluster backendCluster cluster') = encodePreArgs encodeBackendClusterArg backendCluster <> encodeCluster' cluster'

encodePreArgs :: (forall t. arg t -> Builder) -> PreArgs arg f -> Builder
encodePreArgs f (a :>: as) = intHost $(hashQ ":>:") <> f a <> encodePreArgs f as
encodePreArgs f ArgsNil    = intHost $(hashQ "ArgsNil")

encodeArg :: Arg env t -> Builder
encodeArg (ArgArray m repr sh buffers)
  = intHost $(hashQ "Array") <> encodeModifier m <> encodeArrayType repr <> encodeGroundVars sh <> encodeGroundVars buffers
encodeArg (ArgVar var) = intHost $(hashQ "Var") <> encodeTupR encodeExpVar var
encodeArg (ArgExp exp) = intHost $(hashQ "Exp") <> encodeOpenExp exp
encodeArg (ArgFun fun) = intHost $(hashQ "Fun") <> encodeOpenFun fun

encodeGroundVars :: GroundVars env t -> Builder
encodeGroundVars = encodeTupR encodeGroundVar

encodeGroundVar :: GroundVar env t -> Builder
encodeGroundVar (Var tp ix) = encodeGroundR tp <> encodeIdx ix

encodeGroundR :: GroundR t -> Builder
encodeGroundR (GroundRscalar tp) = intHost $(hashQ "Scalar") <> encodeScalarType tp
encodeGroundR (GroundRbuffer tp) = intHost $(hashQ "Buffer") <> encodeScalarType tp

encodeModifier :: Modifier m -> Builder
encodeModifier In  = intHost $(hashQ "In")
encodeModifier Out = intHost $(hashQ "Out")
encodeModifier Mut = intHost $(hashQ "Mut")

-- encodeCluster' :: EncodeOperation op => Cluster' op args -> Builder
-- encodeCluster' (Cluster' io ast) = encodeClusterIO io <> encodeClusterAST ast

-- encodeClusterIO :: ClusterIO args input output -> Builder
-- encodeClusterIO Empty                 = intHost $(hashQ "Empty")
-- encodeClusterIO (Vertical t repr io)  = intHost $(hashQ "Vertical") <> encodeTake t <> encodeArrayType repr <> encodeClusterIO io
-- encodeClusterIO (Input io)            = intHost $(hashQ "Input") <> encodeClusterIO io
-- encodeClusterIO (Output t subT tp io) = intHost $(hashQ "Output") <> encodeTake t <> encodeSubTupR subT <> encodeTypeR tp <> encodeClusterIO io
-- encodeClusterIO (MutPut io)           = intHost $(hashQ "MutPut") <> encodeClusterIO io
-- encodeClusterIO (ExpPut io)           = intHost $(hashQ "ExpPut") <> encodeClusterIO io
-- encodeClusterIO (VarPut io)           = intHost $(hashQ "VarPut") <> encodeClusterIO io
-- encodeClusterIO (FunPut io)           = intHost $(hashQ "FunPut") <> encodeClusterIO io
-- encodeClusterIO (Trivial io)          = intHost $(hashQ "Trivial") <> encodeClusterIO io

-- encodeTake :: Take x xargs args -> Builder
-- encodeTake = intHost . idxToInt . takeIdx

encodeSubTupR :: SubTupR s t -> Builder
encodeSubTupR SubTupRskip       = intHost $(hashQ "skip")
encodeSubTupR SubTupRkeep       = intHost $(hashQ "keep")
encodeSubTupR (SubTupRpair a b) = intHost $(hashQ "pair") <> encodeSubTupR a <> encodeSubTupR b

-- encodeClusterAST :: EncodeOperation op => ClusterAST op env result -> Builder
-- encodeClusterAST None = intHost $(hashQ "None")
-- encodeClusterAST (Bind lhs op l ast) = intHost $(hashQ "Bind") <> encodeLeftHandSideArgs lhs <> encodeOperation op <> encodeClusterAST ast

-- encodeLeftHandSideArgs :: LeftHandSideArgs body env scope -> Builder
-- encodeLeftHandSideArgs _ = intHost $(hashQ "If I just don't hash this, that's fine right? :)")
-- encodeLeftHandSideArgs Base = intHost $(hashQ "Base")
-- encodeLeftHandSideArgs (Reqr t1 t2 lhs) = intHost $(hashQ "Reqr") <> encodeTake t1 <> encodeTake t2 <> encodeLeftHandSideArgs lhs
-- encodeLeftHandSideArgs (Make t lhs) = intHost $(hashQ "Make") <> encodeTake t <> encodeLeftHandSideArgs lhs
-- encodeLeftHandSideArgs (Adju lhs) = intHost $(hashQ "Adju") <> encodeLeftHandSideArgs lhs
-- encodeLeftHandSideArgs (Ignr lhs) = intHost $(hashQ "Ignr") <> encodeLeftHandSideArgs lhs
-- encodeLeftHandSideArgs (EArg lhs) = intHost $(hashQ "EArg") <> encodeLeftHandSideArgs lhs
-- encodeLeftHandSideArgs (VArg lhs) = intHost $(hashQ "VArg") <> encodeLeftHandSideArgs lhs
-- encodeLeftHandSideArgs (FArg lhs) = intHost $(hashQ "FArg") <> encodeLeftHandSideArgs lhs
