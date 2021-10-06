{-# LANGUAGE GADTs                #-}
{-# LANGUAGE LambdaCase           #-}
{-# LANGUAGE RankNTypes           #-}
{-# LANGUAGE TypeOperators        #-}
{-# OPTIONS_HADDOCK hide #-}
-- |
-- Module      : Data.Array.Accelerate.Trafo.Delayed
-- Copyright   : [2012..2020] The Accelerate Team
-- License     : BSD3
--
-- Maintainer  : Trevor L. McDonell <trevor.mcdonell@gmail.com>
-- Stability   : experimental
-- Portability : non-portable (GHC extensions)
--
-- Utilties for creating a dead variable / (strongly) live
-- variable analysis on one of our ASTs.
--

module Data.Array.Accelerate.Trafo.DeadVars
  ( ReEnv(..), reEnvIdx
    
  ) where

import Data.Array.Accelerate.AST.Idx
import Data.Array.Accelerate.Trafo.Substitution
import Data.Array.Accelerate.Trafo.WeakenedEnvironment

data ReEnv genv fenv where
  ReEnvEnd  :: ReEnv genv fenv
  ReEnvSkip :: ReEnv genv fenv -> ReEnv (genv, t) fenv
  ReEnvKeep :: ReEnv genv fenv -> ReEnv (genv, t) (fenv, t)

reEnvIdx :: ReEnv genv fenv -> genv :?> fenv
reEnvIdx (ReEnvKeep _) ZeroIdx = Just ZeroIdx
reEnvIdx (ReEnvKeep r) (SuccIdx ix) = SuccIdx <$> reEnvIdx r ix
reEnvIdx (ReEnvSkip r) (SuccIdx ix) = reEnvIdx r ix
reEnvIdx _             _            = Nothing

