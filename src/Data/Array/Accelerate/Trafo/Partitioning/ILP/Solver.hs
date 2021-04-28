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


-- (data)types that are needed for/used in the class, but need to be defined outside of it.
data OptDir = Maximise | Minimise
data ILP op = ILP OptDir (Expression op) (Constraint op) (Bounds op)
type Solution op = M.Map (Var op) Int


-- Has an instance for LIMP, could add more. The MIP library binds to many solvers,
-- and I enjoyed using that with Gurobi for a different project. Sadly, Gurobi is
-- proprietary (though they provide free licenses to academics).
-- TODO once stuff works, benchmark some large accelerate programs to find a fast
-- solver that we can integrate with Accelerate easily.
-- -David


data Expression op where
  Constant :: Int -> Expression op
  (:+)  :: Expression op -> Expression op -> Expression op
  (:-)  :: Expression op -> Expression op -> Expression op
  (:*)  :: Int               -> Var            op -> Expression op 

data Constraint op where
  (:>=) :: Expression op -> Expression op -> Constraint op
  (:<=) :: Expression op -> Expression op -> Constraint op
  (:==) :: Expression op -> Expression op -> Constraint op
  
  (:>)  :: Expression op -> Expression op -> Constraint op
  (:<)  :: Expression op -> Expression op -> Constraint op
  Between :: Expression op -> Expression op -> Expression op -> Constraint op

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

(.>.)  :: Expression op -> Expression op -> Constraint op
(.>.) = (:>)
(.<.)  :: Expression op -> Expression op -> Constraint op
(.<.) = (:<)
between :: Expression op -> Expression op -> Expression op -> Constraint op
between = Between

defaultBigger :: Expression op -> Expression op -> Constraint op
x `defaultBigger`  y = x .>=. (y .+. int 1)
defaultSmaller :: Expression op -> Expression op -> Constraint op
x `defaultSmaller` y = (x .+. int 1) .<=. y
defaultBetween :: Expression op -> Expression op -> Expression op -> Constraint op
defaultBetween x y z = x .<=. y <> y .<=. z

binary :: Var op -> Bounds op
binary = Binary
lowerUpper :: Int -> Var op -> Int -> Bounds op
lowerUpper = LowerUpper

class (MakesILP op) => ILPSolver ilp op where
  solve :: ilp -> ILP op -> IO (Maybe (Solution op))

