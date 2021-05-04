{-# LANGUAGE GADTs #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeFamilyDependencies #-}
module Data.Array.Accelerate.Trafo.Partitioning.ILP.Solver where

import qualified Data.Map as M
-- Uses an hs-boot file to break an unfortunate cyclic import situation with D.A.A.T.P.ILP.Graph:
-- `ILPSolver` references `Var` in type signatures, `Var` contains `BackendVar`,
-- `BackendVar` is in the class `MakesILP`, which references `Information`,
-- `Information` contains `Constraint` and `Bounds` from `ILPSolver`.
-- I did not want to put them in the same module, so here we are.
import {-# SOURCE #-} Data.Array.Accelerate.Trafo.Partitioning.ILP.Graph ( Var, MakesILP )


data OptDir = Maximise | Minimise

data ILP op = ILP OptDir (Expression op) (Constraint op) (Bounds op)

type Solution op = M.Map (Var op) Int

data Expression op where
  Constant :: Int -> Expression op
  (:+)  :: Expression op -> Expression op -> Expression op
  (:-)  :: Expression op -> Expression op -> Expression op
  (:*)  :: Int -> Var op -> Expression op 

data Constraint op where
  (:>=) :: Expression op -> Expression op -> Constraint op
  (:<=) :: Expression op -> Expression op -> Constraint op
  (:==) :: Expression op -> Expression op -> Constraint op

  (:&&) :: Constraint op -> Constraint op -> Constraint op
  TrueConstraint :: Constraint op

instance Semigroup (Constraint op) where (<>) = (:&&)
instance Monoid    (Constraint op) where mempty = TrueConstraint


data Bounds op where
  Binary :: Var op -> Bounds op
  LowerUpper :: Int -> Var op -> Int -> Bounds op
  (:<>) :: Bounds op -> Bounds op -> Bounds op
  NoBounds :: Bounds op

instance Semigroup (Bounds op) where (<>) = (:<>)
instance Monoid    (Bounds op) where mempty = NoBounds


-- Synonyms for the constructors above
(.+.)  :: Expression op -> Expression op -> Expression op
(.+.) = (:+)
(.-.)  :: Expression op -> Expression op -> Expression op
(.-.) = (:-)
(.*.)  :: Int               -> Var            op -> Expression op 
(.*.) = (:*)
int :: Int -> Expression op
int = Constant
(.>=.) :: Expression op -> Expression op -> Constraint op
(.>=.) = (:>=)
(.<=.) :: Expression op -> Expression op -> Constraint op
(.<=.) = (:<=)
(.==.) :: Expression op -> Expression op -> Constraint op
(.==.) = (:==)
binary :: Var op -> Bounds op
binary = Binary
lowerUpper :: Int -> Var op -> Int -> Bounds op
lowerUpper = LowerUpper

-- Convenience
(.>.)  :: Expression op -> Expression op -> Constraint op
x .>. y = x .>=. (y .+. int 1)
(.<.)  :: Expression op -> Expression op -> Constraint op
x .<. y = (x .+. int 1) .<=. y
between :: Expression op -> Expression op -> Expression op -> Constraint op
between x y z = x .<=. y <> y .<=. z



-- Currently the only instance is for MIP, which gives bindings to a couple of solvers.
-- Still, this way we minimise the surface that has to interact with MIP, can more easily
-- adapt if it changes, and we could easily add more bindings.
class (MakesILP op) => ILPSolver ilp op where
  solve :: ilp -> ILP op -> IO (Maybe (Solution op))

