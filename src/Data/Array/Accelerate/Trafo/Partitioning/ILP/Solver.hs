{-# LANGUAGE TypeFamilyDependencies #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ScopedTypeVariables #-}
module Data.Array.Accelerate.Trafo.Partitioning.ILP.Solver where
-- Uses an hs-boot file to break an unfortunate cyclic import situation with D.A.A.T.P.ILP.Graph:
-- `ILPSolver` references `Var` in type signatures, `Var` contains `BackendVar`,
-- `BackendVar` is in the class `MakesILP`, which references `Information`,
-- `Information` contains `Constraint` and `Bounds` from `ILPSolver`.
-- I did not want to put them in the same module, so here we are.
import {-# SOURCE #-} Data.Array.Accelerate.Trafo.Partitioning.ILP.Graph ( Var )


import Data.Kind (Type)
import qualified Data.Map as M

data OptDir = Maximise | Minimise

data ILP      ilp op = ILP OptDir (Expression ilp op) (Constraint ilp op) (Bounds ilp op)
type Solution ilp op = M.Map (Var op) Int

-- Has an instance for LIMP, could add more. The MIP library binds to many solvers,
-- and I enjoyed using that for a different project.
-- -David
class ( Monoid (Bounds     ilp op)
      , Monoid (Constraint ilp op)) 
    => ILPSolver ilp (op :: Type -> Type) where

  -- The functional dependencies aid type inference
  type Bounds     ilp op = a | a -> ilp op
  type Constraint ilp op = a | a -> ilp op
  type Expression ilp op = a | a -> ilp op

  (.+.)  :: Expression ilp op -> Expression ilp op -> Expression ilp op
  (.-.)  :: Expression ilp op -> Expression ilp op -> Expression ilp op
  (.*.)  :: Int               -> Var            op -> Expression ilp op 
  -- ^ Note: Asymmetric!
  
  (.>=.) :: Expression ilp op -> Expression ilp op -> Constraint ilp op
  (.<=.) :: Expression ilp op -> Expression ilp op -> Constraint ilp op
  (.==.) :: Expression ilp op -> Expression ilp op -> Constraint ilp op
  (.>.)  :: Expression ilp op -> Expression ilp op -> Constraint ilp op
  (.<.)  :: Expression ilp op -> Expression ilp op -> Constraint ilp op
  -- Has a default implementation, but Limp has a (perhaps faster?) specialisation (or it's just convenience...)
  between :: Expression ilp op -> Expression ilp op -> Expression ilp op -> Constraint ilp op
  between x y z = x .<=. y <> y .<=. z

  int :: Int -> Expression ilp op
  
  binary :: Var op -> Bounds ilp op
  lowerUpper :: Int -> Var op -> Int -> Bounds ilp op

  solve :: ILP ilp op -> IO (Maybe (Solution ilp op))


