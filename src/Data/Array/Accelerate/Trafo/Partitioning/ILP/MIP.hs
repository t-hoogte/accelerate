{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}

{-# OPTIONS_GHC -fno-warn-orphans #-} -- Shame on me!
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE TupleSections #-}

module Data.Array.Accelerate.Trafo.Partitioning.ILP.MIP (
  -- Exports default paths to 6 solvers, as well as an instance to ILPSolver for all of them
  cbc, cplex, glpsol, gurobiCl, lpSolve, scip
  ) where

import Data.Array.Accelerate.Trafo.Partitioning.ILP.Graph (MakesILP)
import qualified Data.Array.Accelerate.Trafo.Partitioning.ILP.Graph as Graph (Var)

import Data.Array.Accelerate.Trafo.Partitioning.ILP.Solver
import qualified Data.Map as M

import Numeric.Optimization.MIP hiding (Bounds, Constraint, Var, Solution, name)
import qualified Numeric.Optimization.MIP as MIP
import qualified Numeric.Optimization.MIP.Solver.Base as MIP
import Data.Scientific ( Scientific )
import Data.Bifunctor (bimap)

import Numeric.Optimization.MIP.Solver
    ( cbc, cplex, glpsol, gurobiCl, lpSolve, scip )
import Data.Char (ord)
import Data.Maybe (mapMaybe)
import Control.Monad.State
import Control.Monad.Reader
import qualified Debug.Trace



instance (MakesILP op, MIP.IsSolver s IO) => ILPSolver s op where
  solve s (ILP dir obj constr bnds n) = Debug.Trace.traceShow problem $ makeSolution names <$> MIP.solve s options problem
    where
      options
        | M.size (fst names) > 255*26 = error "Too many variables: Fix Data.Array.Accelerate.Trafo.Partitioning.ILP.MIP/freshName"
        | otherwise = MIP.SolveOptions{ MIP.solveTimeLimit   = Nothing
                                , MIP.solveLogger      = putStrLn . ("AccILPSolver: "      ++)
                                , MIP.solveErrorLogger = putStrLn . ("AccILPSolverError: " ++) }

      stateProblem = Problem (Just "AccelerateILP") <$> (mkFun dir <$> expr n obj) <*> cons n constr <*> pure [] <*> pure [] <*> vartypes <*> (bounds bnds >>= finishBounds)
      (problem, names) = runState stateProblem (mempty, mempty)

      mkFun Maximise = ObjectiveFunction (Just "AccelerateObjective") OptMax
      mkFun Minimise = ObjectiveFunction (Just "AccelerateObjective") OptMin

      vartypes = allIntegers -- assuming that all variables have bounds

-- MIP has a Num instance for expressions, but it's scary (because 
-- you can't guarantee linearity with arbitrary multiplications).
-- We use that instance here, knowing that our own Expression can only be linear.
expr :: MakesILP op => Int -> Expression op -> STN op (MIP.Expr Scientific)
expr n (Constant (Number f)) = pure $ fromIntegral (f n)
expr n (x :+ y) = (+) <$> expr n x <*> expr n y
expr n ((Number f) :* y) = (fromIntegral (f n) *) . varExpr <$> var y

cons :: MakesILP op => Int -> Constraint op -> STN op [MIP.Constraint Scientific]
cons n (x :>= y) = (\a b -> [a MIP..>=. b]) <$> expr n x <*> expr n y
cons n (x :<= y) = (\a b -> [a MIP..<=. b]) <$> expr n x <*> expr n y
cons n (x :== y) = (\a b -> [a MIP..==. b]) <$> expr n x <*> expr n y

cons n (x :&& y) = (<>) <$> cons n x <*> cons n y
cons _ TrueConstraint = pure mempty

bounds :: MakesILP op => Bounds op -> STN op (M.Map MIP.Var (Extended Scientific, Extended Scientific))
bounds (Binary v) = (`M.singleton` (Finite 0, Finite 1)) <$> var v
bounds (Lower      l v  ) = (`M.singleton` (Finite (fromIntegral l), PosInf                 )) <$> var v
bounds (     Upper   v u) = (`M.singleton` (NegInf                 , Finite (fromIntegral u))) <$> var v
bounds (LowerUpper l v u) = (`M.singleton` (Finite (fromIntegral l), Finite (fromIntegral u))) <$> var v
bounds (x :<> y) = M.unionWith (\(l1, u1) (l2, u2) -> (max l1 l2, min u1 u2)) <$> bounds x <*> bounds y
bounds NoBounds = pure mempty

-- For all variables not yet in bounds, we add infinite bounds. This is apparently required.
-- Potentially, it's more efficient to simply make a bounds map giving (NegInf, PosInf) to all variables (like in `allIntegers`), and then use `unionWith const`?
finishBounds :: M.Map MIP.Var (Extended Scientific, Extended Scientific) -> STN op (M.Map MIP.Var (Extended Scientific, Extended Scientific))
finishBounds x = do
  vars' <- gets $ map toVar . M.keys . fst
  let y = M.keys x
  return $ x <> (M.fromList . map (,(NegInf,PosInf)) . filter (not . (`elem` y)) $ vars')

allIntegers :: STN op (M.Map MIP.Var VarType)
allIntegers = gets $ M.fromList . map ((,IntegerVariable) . toVar) . M.keys . fst

-- Apparently, solvers don't appreciate variable names longer than 255 characters!
-- Instead, we generate small placeholders here and store their meaning :)

type Names op = (M.Map String (Graph.Var op), M.Map (Graph.Var op) String)
type STN op = State (Names op)
freshName :: STN op String
freshName = do
  maybeLast <- gets $ M.lookupMax . fst
  case maybeLast of
    Nothing -> return "a"
    Just (name, _) -> return $ increment name
  where
    -- "a" to "z", followed by "za" to "zz", then "zza" to "zzz", etc.
    -- This method isn't _optimal_ in that all non-final letters are always 'z',
    -- but at least `M.lookupMax` does work and we get 26 options per length.
    -- I believe the limit is a variable name of 256 characters, which allows us
    -- 6656 distinct variables at the moment. TODO improve once we get there,
    -- by explicitly keeping track of the last name in the state.
    increment "" = "a"
    increment (char:cs)
      | ord char < ord 'z' = toEnum (ord char + 1) : cs
      | otherwise = char : increment cs

var :: MakesILP op => Graph.Var op -> STN op MIP.Var
var v = do
  maybeName <- gets $ (M.!? v) . snd
  case maybeName of
    Just name -> return $ toVar name
    Nothing -> do
      name <- freshName
      modify $ bimap (M.insert name v) (M.insert v name)
      return $ toVar name

unvar :: MakesILP op => MIP.Var -> Reader (Names op) (Maybe (Graph.Var op))
unvar (fromVar -> name) = asks $ (M.!? name) . fst

-- var   :: MakesILP op => Graph.Var op -> MIP.Var
-- var   = toVar . Debug.Trace.traceShowId . filter (not . isSpace) . show
-- unvar :: MakesILP op => MIP.Var -> Maybe (Graph.Var op)
-- unvar = readMaybe . Debug.Trace.traceShowId . fromVar



makeSolution :: MakesILP op => Names op -> MIP.Solution Scientific -> Maybe (Solution op)
--                                   ------- Matching on solutions with a value: If this is Nothing, the model was infeasable or unbounded.
--                                   |    -- Instead matching on `MIP.Solution StatusOptimal often works too, but that doesn't work for
--                                   v    -- the identity program (which has an empty ILP).
makeSolution names (MIP.Solution _ (Just _) m) = Just . M.fromList . mapMaybe (sequence' . bimap (\v -> runReader (unvar v) names) round) $ M.toList m
makeSolution _ _ = Nothing

-- tuples traversable instance works on the second argument
sequence' :: (Maybe a, b) -> Maybe (a, b)
sequence' (Nothing, _) = Nothing
sequence' (Just x, y) = Just (x, y)
