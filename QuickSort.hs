{-# language FlexibleInstances #-}
{-# language FlexibleContexts #-}
{-# language ScopedTypeVariables #-}

module QuickSort (quicksort, quickerror, initialFlags, writeFlags, propagateSegmentHead, propagateSegmentLast, postscanSegHead, undef) where

import qualified Data.Array.Accelerate as A
-- import qualified Data.Array.Accelerate.Unsafe as A
import qualified Data.Array.Accelerate.Pattern as A
import qualified Data.Array.Accelerate.Data.Bits as A
-- import qualified Data.Array.Accelerate.Examples.Internal as A
import Control.Monad

undef :: A.Exp Int
undef = 0

quickerror :: A.Acc (A.Vector Int) -> A.Acc (A.Vector Int)
quickerror inp = A.scatter (singleton 1) inp inp

initialFlags :: A.Acc (A.Vector Int) -> A.Acc (A.Vector Bool)
initialFlags input = A.scatter (singleton 0 A.++ A.fill (A.index1 1) (A.unindex1 $ A.shape input)) emptyFlags (A.use $ A.fromList (A.Z A.:. 2) [True, True])
  where
    emptyFlags = A.fill (A.index1 $ 1 + A.unindex1 (A.shape input)) (A.constant False)

quicksort :: A.Acc (A.Vector Int) -> A.Acc State
-- quicksort input = A.T3 result flags thing
quicksort input = A.T2 result flags
  where
    emptyFlags = A.fill (A.index1 $ 1 + A.unindex1 (A.shape input)) (A.constant False)
    -- Initially, we have one segment, namely the whole array
    initialFlags = A.scatter (singleton 0 A.++ A.fill (A.index1 1) (A.unindex1 $ A.shape input)) emptyFlags (A.use $ A.fromList (A.Z A.:. 2) [True, True])

    -- We stop when each segment contains just one element, as segments of one element are sorted.
    -- A.T3 result flags thing = {-A.awhile condition-} step $ A.T3 input initialFlags (A.fill (A.index1 undef) (A.index1 undef))
    -- A.T3 result flags thing = A.awhile condition step $ A.T3 input initialFlags (A.fill (A.index1 undef) (A.index1 undef))
    -- A.T2 result flags = {-A.awhile condition-} step $ A.T2 input initialFlags
    A.T2 result flags = A.awhile condition step $ A.T2 input initialFlags

singleton :: A.Elt e => e -> A.Acc (A.Vector e)
singleton e = A.use $ A.fromList (A.Z A.:. 1) [e]

type State =
  -- Values
  ( A.Vector Int
  -- Head flags, denoting the starting points of the unsorted segments
  , A.Vector Bool
  -- , A.Vector A.DIM1
  )

step :: A.Acc State -> A.Acc State
-- step (A.T3 values headFlags _) = (A.T3 values' headFlags' (writes 1))
step (A.T2 values headFlags) = (A.T2 values' headFlags')
  where
    -- Per element, the pivot of the segment of that element
    -- For each segment, we just take the first element as pivot
    pivots = propagateSegmentHead headFlags values

    -- Find which elements are larger than the pivot
    isLarger = A.zipWith (A.>=) values pivots

    -- Propagate the start index of a segment to all elements
    startIndex = propagateSegmentHead headFlags (A.generate (A.shape values) A.unindex1)

    -- Compute the offsets to which the elements must be moved using a scan
    indicesLarger, indicesSmaller :: A.Acc (A.Vector Int)
    indicesLarger  = A.map (\x -> x - 1) $ postscanSegHead (+) headFlags $ A.map (A.? (1, 0)) isLarger
    indicesSmaller = A.map (\x -> x - 1) $ postscanSegHead (+) headFlags $ A.map (A.? (0, 1)) isLarger

    -- Propagate the number of smaller elements to each segment
    -- This is needed as an offset for the larger elements
    countSmaller :: A.Acc (A.Vector Int)
    countSmaller = A.map (+1) $ propagateSegmentLast headFlags indicesSmaller

    -- Compute the new indices of the elements
    permutation = A.zipWith5 partitionPermuteIndex isLarger startIndex indicesSmaller indicesLarger countSmaller
    
    -- Perform the permutation
    values' = A.scatter permutation (A.fill (A.shape values) undef) values

    -- Update the head flags for the next iteration (the 'recursive call' in a traditional implementation)
    -- Mark new section starts at:
    -- * the position of the pivot
    -- * the position of the pivot + 1
    f :: Int -> A.Exp Bool -> A.Exp Int -> A.Exp Int -> A.Exp A.DIM1
    f inc headF start countSmall =
      headF A.? (A.index1 $ start + countSmall + A.constant inc, A.ignore)
    writes :: Int -> A.Acc (A.Vector A.DIM1)
    writes inc = A.zipWith3 (f inc) headFlags startIndex countSmaller

    headFlags' =
        -- Note that (writes 1) may go out of bounds of the values array.
        -- We made the headFlags array one larger, such that this gives no problems.
        writeFlags (writes 0) $ writeFlags (writes 1) $ headFlags
        -- writeFlags (writes 0) $ headFlags

-- Checks whether all segments have length 1. If that is the case, then the loop may terminate.
condition :: A.Acc State -> A.Acc (A.Scalar Bool)
-- condition (A.T3 _ headFlags _) = A.map A.not $ A.fold (A.&&) (A.constant True) headFlags
condition (A.T2 _ headFlags) = A.map A.not $ A.fold (A.&&) (A.constant True) headFlags

-- Finds the new index of an element of the list, as the result of the partition
partitionPermuteIndex :: A.Exp Bool -> A.Exp Int -> A.Exp Int -> A.Exp Int -> A.Exp Int -> A.Exp Int
partitionPermuteIndex isLarger start indexIfSmaller indexIfLarger countSmaller =
  start + (isLarger A.? (countSmaller + indexIfLarger, indexIfSmaller))

-- Given head flags, propagates the value of the head to all elements in the segment
propagateSegmentHead :: A.Acc (A.Vector Bool) -> A.Acc (A.Vector Int) -> A.Acc (A.Vector Int)
propagateSegmentHead headFlags values
  = A.map A.fst
  $ A.postscanl f (A.T2 undef $ A.constant True)
  $ A.zip values headFlags
  where
    f left (A.T2 rightValue rightFlag) =
      A.cond rightFlag (A.T2 rightValue $ A.constant True) left

-- Given head flags, propagates the value of the head to all elements in the segment
propagateSegmentLast :: A.Acc (A.Vector Bool) -> A.Acc (A.Vector Int) -> A.Acc (A.Vector Int)
propagateSegmentLast headFlags values
  = A.map A.fst
  $ A.postscanr f (A.T2 undef $ A.constant True)
  $ A.zip values 
  $ A.tail headFlags
  where
    f (A.T2 leftValue leftFlag) right =
      A.cond leftFlag (A.T2 leftValue $ A.constant True) right

-- Segmented postscan, where the segments are defined with head flags
postscanSegHead :: (A.Exp Int -> A.Exp Int -> A.Exp Int) -> A.Acc (A.Vector Bool) -> A.Acc (A.Vector Int) -> A.Acc (A.Vector Int)
postscanSegHead f headFlags values
  = A.map A.fst
  $ A.postscanl g (A.T2 undef $ A.constant True)
  $ A.zip values headFlags
  where
    g (A.T2 leftValue leftFlag) (A.T2 rightValue rightFlag)
      = A.T2
          (rightFlag A.? (rightValue, f leftValue rightValue))
          (leftFlag A..|. rightFlag)

-- TODO: IT GOES WRONG IN THIS FUNCTION
-- Writes True to the specified indices in a flags arrays
writeFlags :: A.Acc (A.Vector A.DIM1) -> A.Acc (A.Vector Bool) -> A.Acc (A.Vector Bool)
writeFlags writes flags = A.permute (A.||) flags (writes A.!) (A.fill (A.shape writes) $ A.constant True)