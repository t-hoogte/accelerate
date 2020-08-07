{-# LANGUAGE ConstraintKinds     #-}
{-# LANGUAGE FlexibleInstances   #-}
{-# LANGUAGE GADTs               #-}
{-# LANGUAGE KindSignatures      #-}
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
{-# OPTIONS_HADDOCK hide #-}
-- |
-- Module      : Data.Array.Accelerate.Trafo.Operation.Substitution
-- Copyright   : [2012..2020] The Accelerate Team
-- License     : BSD3
--
-- Maintainer  : Trevor L. McDonell <trevor.mcdonell@gmail.com>
-- Stability   : experimental
-- Portability : non-portable (GHC extensions)
--

module Data.Array.Accelerate.Trafo.Operation.Substitution (

  -- ** Renaming & Substitution
  inline, inlineVars, compose,
  subTop, subAtop,

  -- ** Weakening
  (:>), Sink(..), SinkExp(..), weakenVars,

  -- ** Strengthening
  (:?>), strengthen, strengthenE,

  -- ** Rebuilding terms
  RebuildAcc, Rebuildable(..), RebuildableAcc,
  RebuildableExp(..), rebuildWeakenVar, rebuildLHS,
  OpenAccFun(..), OpenAccExp(..),

  -- ** Checks
  isIdentity, isIdentityIndexing, extractExpVars,
  bindingIsTrivial,

) where

import Data.Array.Accelerate.AST.Operation
import Data.Array.Accelerate.AST.LeftHandSide
import Data.Array.Accelerate.AST.Var
import Data.Array.Accelerate.AST.Idx
import Data.Array.Accelerate.AST.Environment
import Data.Array.Accelerate.Analysis.Match
import Data.Array.Accelerate.Error
import Data.Array.Accelerate.Representation.Type
import Data.Array.Accelerate.Representation.Array
import qualified Data.Array.Accelerate.Debug.Stats      as Stats
import Data.Array.Accelerate.Trafo.Substitution (lhsFullVars, bindingIsTrivial)

import Data.Kind
import Control.Applicative                              hiding ( Const )
import Control.Monad
import Prelude                                          hiding ( exp, seq )


isIdentity :: OpenFun env aenv (a -> b) -> Maybe (a :~: b)
isIdentity (Lam lhs (Body (extractExpVars -> Just vars))) = bindingIsTrivial lhs vars
isIdentity _ = Nothing
