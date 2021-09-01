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

data ILP op = ILP OptDir (Expression op) (Constraint op) (Bounds op) Int

type Solution op = M.Map (Var op) Int

-- given `n` (for the number of nodes in the ILP), make an Int
newtype Number = Number (Int -> Int)

data Expression op where
  Constant :: Number -> Expression op
  (:+)  :: Expression op -> Expression op -> Expression op
  (:*)  :: Number -> Var op -> Expression op 

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
  Lower :: Int -> Var op -> Bounds op
  Upper :: Var op -> Int -> Bounds op
  (:<>) :: Bounds op -> Bounds op -> Bounds op
  NoBounds :: Bounds op

instance Semigroup (Bounds op) where (<>) = (:<>)
instance Monoid    (Bounds op) where mempty = NoBounds


-- Synonyms for the constructors above
infixl 8 .+.
infixl 8 .-.
infixl 8 .*.
(.+.)  :: Expression op -> Expression op -> Expression op
(.+.) = (:+)
(.-.)  :: Expression op -> Expression op -> Expression op
e1 .-. e2 = e1 .+. ((-1) .*. e2)
(.*.)  :: Int           -> Expression op -> Expression op 
i .*. (Constant (Number f)) = Constant $ Number $ (*i) . f
i .*. (e1 :+ e2) = (:+) (i .*. e1) (i .*. e2)
i .*. (Number f :* v) = (:*) (Number ((*i) . f)) v
timesN :: Expression op -> Expression op
timesN (Constant (Number f)) = Constant (Number (\n -> n * f n))
timesN ((:+) e1 e2) = (:+) (timesN e1) (timesN e2)
timesN ((:*) (Number f) v) = (:*) (Number (\n -> n * f n)) v
c :: Var op -> Expression op
c = (Number (const 1) :*)
int :: Int -> Expression op
int = Constant . Number . const

infixr 7 .>=.
infixr 7 .<=.
infixr 7 .==.
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
lower :: Int -> Var op -> Bounds op
lower = Lower
upper :: Var op -> Int -> Bounds op
upper = Upper

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

