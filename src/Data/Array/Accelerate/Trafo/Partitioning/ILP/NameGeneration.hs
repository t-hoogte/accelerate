module Data.Array.Accelerate.Trafo.Partitioning.ILP.NameGeneration where

import Control.Monad.State ( State, gets, modify )
import Data.Char ( ord )
import qualified Data.Map as M
import qualified Data.Array.Accelerate.Trafo.Partitioning.ILP.Graph as Graph
import Lens.Micro.Mtl (zoom)
import Lens.Micro (_2)
import Data.Array.Accelerate.Trafo.Partitioning.ILP.Graph
import Control.Monad.Reader
import Data.Bifunctor


-- Apparently, solvers don't appreciate variable names longer than 255 characters!
-- Instead, we generate small placeholders here and store their meaning
type Names op = (M.Map String (Graph.Var op), M.Map (Graph.Var op) String)
type STN op = State (Names op, String)
-- to avoid generating keywords, we simply prepend every name with an 'x'. This still leaves 26^254 options, more than enough!
freshName' :: STN op String
freshName' = zoom _2 $ freshName "x" 

-- Iterates in the following order:
-- ["", "a", .., "z", "aa", .., "za", "ab", .., "zz", "aaa", "baa", ...]
-- The prefix disembiguates from other uses of freshName, and avoids generating keywords.
freshName :: String -> State String String
freshName prefix = do
  modify increment
  gets ((prefix <> "_") <>)
  where
    increment (char:cs)
      | ord char < ord 'z' = toEnum (ord char + 1) : cs
      | otherwise = 'a' : increment cs
    increment "" = "a"

var' :: MakesILP op => Graph.Var op -> STN op String
var' v = do
  maybeName <- gets $ (M.!? v) . snd . fst
  case maybeName of
    Just name -> return name
    Nothing -> do
      name <- freshName'
      modify $ first $ bimap (M.insert name v) (M.insert v name)
      return name

unvar' :: MakesILP op => String -> Reader (Names op) (Maybe (Graph.Var op))
unvar' name = asks $ (M.!? name) . fst

