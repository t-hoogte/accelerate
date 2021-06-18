{-# LANGUAGE BangPatterns          #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE LambdaCase            #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE TemplateHaskell       #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE TypeOperators         #-}

-- |
-- Module      : Data.Array.Accelerate.AST.Partitioned
-- Copyright   : [2008..2020] The Accelerate Team
-- License     : BSD3
--
-- Maintainer  : Trevor L. McDonell <trevor.mcdonell@gmail.com>
-- Stability   : experimental
-- Portability : non-portable (GHC extensions)
--
module Data.Array.Accelerate.AST.Partitioned where

import Data.Array.Accelerate.AST.Operation

import Prelude hiding ( take )
import Data.Bifunctor (second)
import Data.Array.Accelerate.Trafo.Partitioning.ILP.Labels
import Data.Array.Accelerate.AST.CoDeBruijn



type PartitionedAcc  op = PreOpenAcc  (Cluster op)
type PartitionedAfun op = PreOpenAfun (Cluster op)

data Cluster op args where
  CNil ::         op args 
      -> Cluster op args
  -- We could branch into two Clusters (symmetrically),
  -- but the semantics are associative so I prefer to
  -- make it list-like over tree-like.
  Cons :: SplitCoEnv args largs rargs
       ->         op largs
       -> Cluster op rargs
       -> Cluster op args

take :: Take x xc c -> Args env xc -> (Arg env x, Args env c)
take Here      (x :>: xs) = (x, xs)
take (There t) (x :>: xs) = second (x :>:) $ take t xs

labelledTake :: Take x xc c -> LabelArgs xc -> (ALabels x, LabelArgs c)
labelledTake Here      (x :>>: xs) = (x, xs)
labelledTake (There t) (x :>>: xs) = second (x :>>:) $ labelledTake t xs


put :: Take x xc c -> (Arg env x, Args env c) -> Args env xc
put Here       (x, xs) = x :>: xs
put (There t') (x, y :>: xs) = y :>: put t' (x, xs)

