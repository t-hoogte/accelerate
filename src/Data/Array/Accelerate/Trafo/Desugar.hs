{-# LANGUAGE GADTs                #-}
{-# LANGUAGE RankNTypes           #-}
{-# LANGUAGE ScopedTypeVariables  #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE TypeFamilies         #-}
{-# LANGUAGE TypeOperators        #-}
-- |
-- Module      : Data.Array.Accelerate.Trafo.Desugar
-- Copyright   : [2012..2020] The Accelerate Team
-- License     : BSD3
--
-- Maintainer  : Trevor L. McDonell <trevor.mcdonell@gmail.com>
-- Stability   : experimental
-- Portability : non-portable (GHC extensions)
--

module Data.Array.Accelerate.Trafo.Desugar
  where

import qualified Data.Array.Accelerate.AST as Named
import Data.Array.Accelerate.AST.Operation
import Data.Array.Accelerate.Representation.Array
import Data.Array.Accelerate.Representation.Shape
import Data.Array.Accelerate.Representation.Slice
import Data.Array.Accelerate.Representation.Tag
import Data.Array.Accelerate.Representation.Type
import Data.Array.Accelerate.Representation.Vec
import Data.Array.Accelerate.Sugar.Foreign
import Data.Array.Accelerate.Type
import Data.Array.Accelerate.Error
import Data.Primitive.Vec

class DesugarAcc op where

type family DesugaredArrays a where
  DesugaredArrays ()           = ()
  DesugaredArrays (a, b)       = (DesugaredArrays a, DesugaredArrays b)
  DesugaredArrays (Array sh e) = (sh, Buffers e)

type family DesugaredAfun a where
  DesugaredAfun (a -> b) = DesugaredArrays a -> DesugaredAfun b
  DesugaredAfun a        = DesugaredArrays a

desugar :: Named.Acc a -> OperationAcc (Execute op) () (DesugaredArrays a)
desugar = undefined

desugarFun :: Named.Afun a -> OperationAcc (Execute op) () (DesugaredAfun a)
desugarFun = undefined
