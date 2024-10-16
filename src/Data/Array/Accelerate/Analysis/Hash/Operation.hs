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

module Data.Array.Accelerate.Analysis.Hash.Operation ( EncodeOperation(..), hashOperation, encodePreArgs, encodeArg ) where

import Data.Array.Accelerate.Analysis.Hash.Exp
import Data.Array.Accelerate.AST.Idx
import Data.Array.Accelerate.AST.Var
import Data.Array.Accelerate.AST.Partitioned
import Data.Array.Accelerate.Trafo.LiveVars
import Data.Array.Accelerate.Trafo.Partitioning.ILP.Graph (MakesILP, encodeBackendClusterArg)
import Data.Array.Accelerate.Trafo.Operation.LiveVars

import Crypto.Hash.XKCP
import Data.ByteString.Builder

hashOperation :: EncodeOperation op => op t -> Args env t -> Hash
hashOperation op args
  = hashlazy
  $ toLazyByteString
  $ encodeOperation op <> encodePreArgs encodeArg args

class EncodeOperation op where
  encodeOperation :: op t -> Builder

instance (MakesILP op, EncodeOperation op) => EncodeOperation (Clustered op) where
  encodeOperation (Clustered cluster backendCluster) = 
    encodePreArgs encodeBackendClusterArg backendCluster <> encodeCluster cluster

encodePreArgs :: (forall t. arg t -> Builder) -> PreArgs arg f -> Builder
encodePreArgs f (a :>: as) = intHost $(hashQ ":>:") <> f a <> encodePreArgs f as
encodePreArgs f ArgsNil    = intHost $(hashQ "ArgsNil")

encodeArg :: Arg env t -> Builder
encodeArg (ArgArray m repr sh buffers)
  = intHost $(hashQ "Array") <> encodeModifier m <> encodeArrayType repr <> encodeGroundVars sh <> encodeGroundVars buffers
encodeArg (ArgVar var) = intHost $(hashQ "Var") <> encodeTupR encodeExpVar var
encodeArg (ArgExp exp) = intHost $(hashQ "Exp") <> encodeOpenExp exp
encodeArg (ArgFun fun) = intHost $(hashQ "Fun") <> encodeOpenFun fun

encodeModifier :: Modifier m -> Builder
encodeModifier In  = intHost $(hashQ "In")
encodeModifier Out = intHost $(hashQ "Out")
encodeModifier Mut = intHost $(hashQ "Mut")

encodeCluster :: EncodeOperation op => Cluster op args -> Builder
encodeCluster (SingleOp op label)
  = intHost $(hashQ "SingleOp") <> encodeSingleOp op <> encodeLabel label
encodeCluster (Fused fusion left right)
  = intHost $(hashQ "Fused") <> encodeFusion fusion <> encodeCluster left <> encodeCluster right

encodeLabel :: Label -> Builder
encodeLabel (Label idx Nothing) = intHost idx <> intHost $(hashQ "Nothing")
encodeLabel (Label idx (Just l)) = intHost idx <> intHost $(hashQ "Just") <> encodeLabel l

encodeFusion :: Fusion largs rargs args -> Builder
encodeFusion EmptyF         = intHost $(hashQ "EmptyF")
encodeFusion (Vertical r f) = intHost $(hashQ "Vertical")   <> encodeArrayType r <> encodeFusion f
encodeFusion (Horizontal f) = intHost $(hashQ "Horizontal") <> encodeFusion f
encodeFusion (Diagonal f)   = intHost $(hashQ "Diagonal")   <> encodeFusion f
encodeFusion (IntroI1 f)    = intHost $(hashQ "IntroI1")    <> encodeFusion f
encodeFusion (IntroI2 f)    = intHost $(hashQ "IntroI2")    <> encodeFusion f
encodeFusion (IntroO1 f)    = intHost $(hashQ "IntroO1")    <> encodeFusion f
encodeFusion (IntroO2 f)    = intHost $(hashQ "IntroO2")    <> encodeFusion f
encodeFusion (IntroL f)     = intHost $(hashQ "IntroL")     <> encodeFusion f
encodeFusion (IntroR f)     = intHost $(hashQ "IntroR")     <> encodeFusion f

encodeSingleOp :: EncodeOperation op => SingleOp op args -> Builder
encodeSingleOp (Single op soa sorted sub)
  = encodeOperation op
  <> encodeSOAs soa
  <> encodeSortedArgs sorted
  <> encodeSubArgs sub

encodeSOAs :: SOAs args expanded -> Builder
encodeSOAs SOArgsNil = intHost $(hashQ "SOArgsNil")
encodeSOAs (SOArgsCons soas soa) = intHost $(hashQ "SOArgsCons") <> encodeSOAs soas <> encodeSOA soa

encodeSOA :: SOA arg appendto result -> Builder
encodeSOA SOArgSingle = intHost $(hashQ "SOArgSingle")
encodeSOA (SOArgTup a b) = intHost $(hashQ "SOArgTup") <> encodeSOA a <> encodeSOA b

encodeSortedArgs :: SortedArgs args sorted -> Builder
encodeSortedArgs _ = intHost $(hashQ "todo") -- TODO: Encode SortedArgs. I think we need to defunctionalize this data type to encode it.

encodeSubArgs :: SubArgs a b -> Builder
encodeSubArgs SubArgsNil = intHost $(hashQ "SubArgsNil")
encodeSubArgs (SubArgsDead subArgs) = intHost $(hashQ "SubArgsDead") <> encodeSubArgs subArgs
encodeSubArgs (SubArgsLive SubArgKeep subArgs) = intHost $(hashQ "SubArgsLive Keep") <> encodeSubArgs subArgs
encodeSubArgs (SubArgsLive (SubArgOut subTup) subArgs) = intHost $(hashQ "SubArgsLive Out") <> encodeSubTupR subTup <> encodeSubArgs subArgs

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
