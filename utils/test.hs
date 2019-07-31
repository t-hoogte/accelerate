{-# LANGUAGE RecordWildCards #-}
{-# language TypeOperators #-}
{-# language ViewPatterns #-}
{-# language ScopedTypeVariables #-}
{-# language FlexibleContexts #-}
module Test

where

import Data.Array.Accelerate                              as A hiding (fromInteger, fromRational, fromIntegral)
import qualified Data.Array.Accelerate                    as A (fromInteger, fromRational, fromIntegral)
import Data.Array.Accelerate.Interpreter                  as I
import Data.Array.Accelerate.Debug.Flags

import qualified Prelude as P
import Prelude as P (fromIntegral, fromInteger, fromRational, String, return, (>>=), (>>), IO, Maybe(..), maybe, show)

import Data.Array.Accelerate.Trafo
import qualified Data.Array.Accelerate.Trafo.Sharing    as Sharing
import qualified Data.Array.Accelerate.AST              as AST
import Data.Array.Accelerate.Trafo.Vectorise  as Vectorise hiding (index1, the, unit)
import qualified Data.Array.Accelerate.Trafo.Rewrite    as Rewrite
import qualified Data.Array.Accelerate.Trafo.Simplify   as Rewrite
import qualified Data.Array.Accelerate.Trafo.Fusion     as Fusion
import Data.Array.Accelerate.Array.Lifted               as Lifted
import Data.Array.Accelerate.Trafo.Shape

import Data.Array.Accelerate.Pretty.Print (prettyArrays, Val(..), prettyEnv, PrettyEnv(..))
import Data.Array.Accelerate.Trafo.Base

import Text.PrettyPrint hiding (empty)
import Control.Monad.State.Lazy hiding (lift)

myshow :: (Kit acc, PrettyEnv aenv, Arrays a) => acc aenv a -> String
myshow = render . prettyAcc P.id prettyEnv

myshow2 :: AST.PreOpenAcc acc aenv arrs -> String
myshow2 = AST.showPreAccOp


flags = [dump_vectorisation, dump_phases]
setflags, clearflags :: IO ()
setflags = setFlags flags
clearflags = clearFlags flags

testflag = queryFlag dump_vectorisation


xs', xs2' :: Vector Int
xs' = fromList (Z :. 12) [0..]
xs2' = fromList (Z :. 9) [10..]

xs :: Acc (Vector Int)
xs = use xs'

xs3 :: Acc (Array DIM4 Int)
xs3 = use $ fromList (Z :. 2 :. 1 :. 1 :. 10) [0..]

xs4 :: Acc (Scalar Int) -> Acc (Vector Int, Scalar Int)
xs4 i' = let i = the i' in lift (reshape (index1 (i+5)) xs, use $ fromList Z [0])

xs5 :: Acc (Scalar Int) -> Acc (Vector Int, Vector Int)
xs5 i' = let i = the i' in lift (reshape (index1 (i+5)) xs, use $ fromList (Z:.1) [0])

ys :: Matrix Int
ys = fromList (Z :. 2 :. 10) [0..]

ysSeq1 :: Seq [Vector Int]
ysSeq1 = toSeqInner . use $ ys

ysSeq2 :: Seq [Vector Int]
ysSeq2 = toSeqOuter . use $ ys

ysSeq3 :: Seq [Matrix Int] 
ysSeq3 = subarrays (lift $ (Z :. 1 :. 10 :: Z :. Int :. Int)) $ ys

ysSeq4 :: Seq [Vector Int]
ysSeq4 = streamIn [xs', xs2', xs', xs']

ysSeq4' :: Acc (IrregularArray DIM1 Int)
ysSeq4' = result
  where
    (shs, vals) = unlift . collect . fromSeq $ ysSeq4
    segs = segmentsFromShapes shs
    result = irregular segs vals

ysSeq5 :: Seq [Array DIM3 Int]
ysSeq5 = toSeqOuter xs3

ysSeq6 = produce (constant 2) xs4
ysSeq7 = produce (constant 2) xs5

check :: Shape sh => Acc (Array sh Int) -> Acc (Scalar Bool) 
check = map (<100) . sum

checkF :: Shape sh => Acc (Array sh Int) -> Acc (Scalar Bool) 
checkF _ = unit . constant $ False

check2 :: Shape sh => Acc (Array sh Int, Scalar Int) -> Acc (Scalar Bool) 
check2 = map (<20) . asnd

check3 :: Shape sh => Acc (Array sh Int, Vector Int) -> Acc (Scalar Bool) 
check3 = reshape (constant Z) . map (<20) . asnd

f :: Shape sh => Acc (Array sh Int) -> Acc (Array sh Int)
f = map (+1)

f2 :: Shape sh => Acc (Array sh Int, Scalar Int) -> Acc (Array sh Int, Scalar Int)
f2 (unlift -> (a,n) :: (Acc (Array sh Int), Acc (Scalar Int))) = lift (map (+1) a, map (+1) n)

f3 :: Shape sh => Acc (Array sh Int, Vector Int) -> Acc (Array sh Int, Vector Int)
f3 (unlift -> (a,n) :: (Acc (Array sh Int), Acc (Vector Int))) = lift (map (+1) a, map (+1) n)

fSeq :: Shape sh => Seq [Array sh Int] -> Seq [Array sh Int]
fSeq = mapSeq f

loop :: Shape sh => Acc (Array sh Int) -> Acc (Array sh Int)
loop = awhile check f --P.id --f

loop2 :: Shape sh => Acc (Array sh Int, Scalar Int) -> Acc (Array sh Int, Scalar Int)
loop2 = awhile check2 f2

loop3 :: Shape sh => Acc (Array sh Int, Vector Int) -> Acc (Array sh Int, Vector Int)
loop3 = awhile check3 f3

tryCond :: Shape sh => Acc (Array sh Int) -> Acc (Array sh Int)
tryCond xs = let --pred = (<50) . the . maximum $ xs
                 pred = (<50) $ xs !! 0
                 res = map (+100) xs
             in acond pred res xs --(xs, res) undefined

loopSeq :: Shape sh => Seq [Array sh Int] -> Seq [Array sh Int]
loopSeq = mapSeq loop

travoSharing :: Arrays arrs => Acc arrs -> AST.Acc arrs
travoSharing = travoSharing' phases

travoSharing' :: Arrays arrs => Phase -> Acc arrs -> AST.Acc arrs
travoSharing' Phase{..} acc
  = (Sharing.convertAcc recoverAccSharing recoverExpSharing recoverSeqSharing floatOutAccFromExp)
  $ acc

travoSharingF :: Sharing.Afunction f => f -> AST.Afun (Sharing.AfunctionR f)
travoSharingF = travoSharingF' phases

travoSharingF' :: Sharing.Afunction f => Phase -> f -> AST.Afun (Sharing.AfunctionR f)
travoSharingF' Phase{..} f
  = (Sharing.convertAfun recoverAccSharing recoverExpSharing recoverSeqSharing floatOutAccFromExp)
  $ f

travoVectorise :: Arrays t => AST.Acc t -> AST.Acc t
travoVectorise = Vectorise.vectoriseAcc

travototal :: Arrays arrs => Acc arrs -> DelayedAcc arrs
travototal = travototal' phases

travototal' :: Arrays arrs => Phase -> Acc arrs -> DelayedAcc arrs
travototal' Phase{..} = Fusion.convertAcc enableAccFusion . travoVectorise . travoSharing

travoUptoVec :: Arrays t => Acc t -> AST.Acc t
travoUptoVec = travoVectorise . travoSharing

showing = travoVectorise . travoSharing . sum . f $ xs

showing2 = travoVectorise . travoSharing . loop $ xs

test1 = collect . tabulate . fSeq $ ysSeq1
test2 = collect . tabulate . fSeq $ ysSeq2
test3 = collect . tabulate . fSeq $ ysSeq3
test4 = collect . elements . fSeq $ ysSeq4
test5 = collect . tabulate . fSeq $ ysSeq5

testLoop1 = collect . tabulate . loopSeq $ ysSeq1
testLoop2 = collect . tabulate . loopSeq $ ysSeq2
testLoop3 = collect . tabulate . loopSeq $ ysSeq3
testLoop4 = collect . elements . loopSeq $ ysSeq4
testLoop4' = collect . tabulate . loopSeq $ ysSeq4
testCond1 = collect . elements . mapSeq tryCond $ ysSeq1
testCond2 = collect . tabulate . mapSeq tryCond $ ysSeq2
testCond3 = collect . fromSeq . mapSeq tryCond $ ysSeq3
testCond4 = collect . tabulate . mapSeq tryCond $ ysSeq4

testLoop3' = collect . fromSeq . loopSeq $ ysSeq3

testLoopTup = collect. fromSeq . P.fst . unzipSeq . mapSeq loop2 $ ysSeq6
testLoopTup2 = collect. fromSeq . P.fst . unzipSeq . mapSeq loop3 $ ysSeq7


showingLoop3 = travoVectorise . travoSharing $ testLoop3

--testACond = collect . tabulate . 

showing3_1 = travoSharing test1
showing3_2 = travoSharing test2
showing3_3 = travoSharing test3

showing4_1   = travoVectorise . travoSharing $ test1
showing4_2 = travoVectorise . travoSharing $ test2
showing4_3 = travoVectorise . travoSharing $ test3

showing5_1 = travoVectorise . travoSharing $ testLoop1
showing5_2 = travoVectorise . travoSharing $ testLoop2
showing5_3 = travoVectorise . travoSharing $ testLoop3

total_1   = travototal test1
total_2 = travototal test2
total_3 = travototal test3




myliftedCond :: (Shape sh, Elt e)
           => Acc (Vector Bool)          -- condition
           -> Acc (IrregularArray sh e)  -- then
           -> Acc (IrregularArray sh e)  -- else
           -> Acc (IrregularArray sh e)
myliftedCond = Vectorise.liftedCond

irAr :: Acc (IrregularArray DIM2 Int)
irAr = use (segs, vals)
  where
    segs = segs' 50
    (sz, ofs, ext) = segs
    n = indexArray sz Z
    vals = fromList (Z :. n) [0..]

segs' :: Int -> Lifted.Segments DIM2
segs' n = (sz, ofs, ext)
    where
      width = 10
      sz = fromList Z [width*n]
      ofs = fromList (Z:.n) [width * i | i <- [0..]]
      ext = fromList (Z:.n) (P.replicate n (Z :. 1 :. width))

pred :: forall sh . Shape sh => Acc (IrregularArray sh Int) -> Acc (Vector Bool)
pred (unlift -> (segs :: Acc (Lifted.Segments sh) , vals)) = let (sz :: Acc (Scalar Int), ofs, ext :: Acc (Vector sh)) = unlift segs
  in generate (shape ofs) (\x -> (vals !! (ofs ! x) + 0) < 50)

irAr2 :: forall sh . Shape sh =>  Acc (IrregularArray sh Int) -> Acc (IrregularArray sh Int)
irAr2 (unlift -> (segs :: Acc (Lifted.Segments sh) , vals)) = lift (segs, map (+50) vals)

{-
condTest :: Acc (IrregularArray DIM2 Int)
condTest = liftedCond2 c t e
    where
      c = pred irAr
      t = irAr
      e = irAr2 irAr-}

replsegTest :: Acc (Vector Int)
replsegTest = Vectorise.replicateSeg (use (segs' 2)) $ use $ fromList (Z :. 2) [0..]

condTest2 = result
  where
    result = acond allleft t $ acond allright e $ irregular segs vals
    pred = Test.pred ysSeq4'
    t = ysSeq4'
    e = irAr2 ysSeq4'

    allleft = the . and $ pred
    allright = not . the . or $ pred 

    shs_t = Vectorise.shapes (segments t)
    shs_e = Vectorise.shapes (segments e)
    shs   = zipWith3 (\f t e -> f ? (t, e))
                       pred shs_t shs_e

    segs = segmentsFromShapes shs

    offs_t = offsets (segments t)
    offs_e = offsets (segments e)
    sz_v   = totalSize segs --fold (+) 0 $ map shapeSize shs
    offs   = zipWith3 (\f t e -> f ? (t, e))
                       pred offs_t offs_e
    flag_offs = replicateSeg segs $ zip pred offs

    vals_t = irregularValues t
    vals_e = irregularValues e
    ones   = fill (index1 $ sz_v) (1 :: Exp Int)
    enums  = prescanlSeg (+) 0 ones $ map shapeSize shs
    vals   = zipWith (\t ind -> let (f,s) = unlift t in f ? (vals_t !! (s + ind), vals_e !! (s + ind)))
                       flag_offs
                       enums

    
    


liftedCond2 :: (Shape sh, Elt e)
           => Acc (Vector Bool)          -- condition
           -> Acc (IrregularArray sh e)  -- then
           -> Acc (IrregularArray sh e)  -- else
           -> Acc (IrregularArray sh e)
liftedCond2 pred t e = result
  where
    allt = the . and $ pred
    alle = not . the . or $ pred

    result = acond allt t $ acond alle e $ irregular segs vals

    shs_t = Vectorise.shapes (segments t)
    shs_e = Vectorise.shapes (segments e)
    shs   = zipWith3 (\f t e -> f ? (t, e))
                       pred shs_t shs_e

    segs = segmentsFromShapes shs

    offs_t = offsets (segments t)
    offs_e = offsets (segments e)
    sz_v   = totalSize segs
    offs   = zipWith3 (\f t e -> f ? (t, e))
                       pred offs_t offs_e
    flag_offs = replicateSeg segs $ zip pred offs

    vals_t = irregularValues t
    vals_e = irregularValues e
    ones   = fill (index1 $ sz_v) (1 :: Exp Int)
    enums  = prescanlSeg (+) 0 ones $ map shapeSize shs
    vals   = zipWith (\t ind -> let (f,s) = unlift t in f ? (vals_t !! (s + ind), vals_e !! (s + ind)))
                       flag_offs
                       enums

