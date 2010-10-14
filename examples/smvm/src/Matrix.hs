{-# LANGUAGE BangPatterns, TupleSections #-}

module Matrix (readCSRMatrix) where

import Util
import MatrixMarket
import System.Random.MWC

import Data.Vector.Unboxed (Vector)
import qualified Data.Vector.Unboxed            as V
import qualified Data.Vector.Unboxed.Mutable    as M
import qualified Data.Vector.Algorithms.Intro   as V


-- Read a sparse matrix from a MatrixMarket file. Pattern matrices are filled
-- with random numbers in the range (-1,1).
--
{-# INLINE readCSRMatrix #-}
readCSRMatrix :: FilePath -> IO (Vector Int, Vector (Int,Float))
readCSRMatrix file = do
  gen <- create
  mtx <- readMatrix file
  case mtx of
    (RealMatrix    dim l vals) -> csr dim l vals
    (PatternMatrix dim l ix)   -> csr dim l =<< mapM' (\(a,b) -> (a,b,) `fmap` uniformR (-1,1) gen) ix


-- Read elements into unboxed arrays, convert to zero-indexed compress sparse
-- row format.
--
{-# INLINE csr #-}
csr :: (Int,Int) -> Int -> [(Int,Int,Float)] -> IO (Vector Int, Vector (Int,Float))
csr (m,_) l elems = do
  mu <- M.new l
  let goe  _ []     = return ()
      goe !n (x:xs) = let (i,j,v) = x in M.unsafeWrite mu n (i-1,j-1,v) >> goe (n+1) xs
  goe 0 elems

  let cmp (x1,y1,_) (x2,y2,_) | x1 == x2  = compare y1 y2
                              | otherwise = compare x1 x2
  V.sortBy cmp mu

  (i,j,v) <- V.unzip3 `fmap` V.unsafeFreeze mu
  mseg    <- M.new m
  let gos !n rows | n < m     = let (s,ss) = V.span (==n) rows in M.unsafeWrite mseg n (V.length s) >> gos (n+1) ss
                  | otherwise = V.unsafeFreeze mseg
  seg <- gos 0 i
  return (seg , V.zip j v)

