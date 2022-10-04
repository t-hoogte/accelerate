module Data.Array.Accelerate.Trafo.Partitioning.ILP.NameGeneration (freshName) where

import Control.Monad.State ( State, gets, modify )
import Data.Char ( ord )

-- Iterates in the following order:
-- ["", "a", .., "z", "aa", .., "za", "ab", .., "zz", "aaa", "baa", ...]
-- The prefix disembiguates from other uses of freshName, or avoids generating keywords.
freshName :: String -> State String String
freshName prefix = do
  modify increment
  gets (prefix <>)
  where
    increment (char:cs)
      | ord char < ord 'z' = toEnum (ord char + 1) : cs
      | otherwise = 'a' : increment cs
    increment "" = "a"
