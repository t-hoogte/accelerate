{-# LANGUAGE RecordWildCards #-}
{-# language TypeOperators #-}
{-# language ViewPatterns #-}
{-# language ScopedTypeVariables #-}
{-# language FlexibleContexts #-}
{-# language GADTs #-}
{-# language FlexibleInstances #-}
{-# language MultiParamTypeClasses #-}
{-# language RankNTypes #-}

module ShapeTests (doAllTest, counts, evalAllVecTests, setflags, clearflags, allIndTests)

where

import Data.Array.Accelerate                              as A hiding (fromIntegral, Segments)
import Data.Array.Accelerate.Prelude                      as A
import qualified Data.Array.Accelerate                    as A (fromIntegral)--, fromRational, fromInteger)
import Data.Array.Accelerate.Interpreter                  as I
import Data.Array.Accelerate.Data.Bits

import qualified Prelude as P
import Prelude as P (String, return, IO)

import Data.Array.Accelerate.Trafo
import qualified Data.Array.Accelerate.Trafo.Sharing    as Sharing
import qualified Data.Array.Accelerate.AST              as AST
import Data.Array.Accelerate.Debug.Flags
-- import Data.Array.Accelerate.Trafo.Vectorise  as Vectorise hiding (index1, the, unit, replicate)
-- import qualified Data.Array.Accelerate.Trafo.Rewrite    as Rewrite
-- import qualified Data.Array.Accelerate.Trafo.Simplify   as Rewrite
-- import qualified Data.Array.Accelerate.Trafo.Fusion     as Fusion
-- import Data.Array.Accelerate.Array.Lifted               as Lifted
import Data.Array.Accelerate.Trafo.Shape
import Data.Array.Accelerate.Analysis.ActionsCount
-- import Data.Array.Accelerate.Language
import Data.Array.Accelerate.Pattern
import Data.Array.Accelerate.Array.Lifted ({-IrregularArray,-} Segments)
-- import Data.Array.Accelerate.Trafo.Base as Base

-- import Data.Array.Accelerate.Pretty.Print (prettyArrays, Val(..), prettyEnv, PrettyEnv(..))
-- import Data.Array.Accelerate.Trafo.Base

-- import Text.PrettyPrint hiding (empty)
import Control.Monad.State.Lazy hiding (lift)
import Control.Lens (lens)
import Control.Lens.Tuple
import Control.Exception

import QuickSort

---------------------------------------
--Run all the tests

doAllTest :: IO Bool
doAllTest = do res <- mapM f allTests
               return $ P.and res
    where
        f (action, name) = do
            P.putStrLn $ "Running: " P.++ name
            action


allTests :: [(IO Bool, String)]
allTests = [(foldScalarTest, "foldScalarTest") ,(foldTest , "foldTest ") ,(foldTest2 , "foldTest2 ") ,(shapeExprTest, "shapeExprTest") ,(zipTest , "zipTest ")
           ,(zipTest2 , "zipTest2 ") ,(zipTest3 , "zipTest3 ") ,(zipTest4 , "zipTest4 ") ,(scanTest , "scanTest ") ,(scanTest2 , "scanTest2 ") ,(replicateTest, "replicateTest")
           ,(replicateTest2, "replicateTest2") ,(sliceTest , "sliceTest ") ,(sliceTest2 , "sliceTest2 ") ,(sliceTest3 , "sliceTest3 ") ,(takeTest , "takeTest ")
           ,(takeOnTest , "takeOnTest ") ,(takeOnTest2, "takeOnTest2") ,(tuppleTest , "tuppleTest ") ,(tuppleTest2 , "tuppleTest2 ") ,(tupIdxTest , "tupIdxTest ")
           ,(tupIdxTest2 , "tupIdxTest2 ") ,(condTest , "condTest ") ,(condTest2 , "condTest2 ") ,(awhileTest , "awhileTest ") ,(awhileTest2 , "awhileTest2 ")
           ,(awhileTest3 , "awhileTest3 ") ,(stencilTest , "stencilTest ") ,(stencilTest2 , "stencilTest2 ")
           ]

flags :: [Mode]
flags = [dump_vectorisation, dump_phases]
setflags, clearflags :: IO ()
setflags = setFlags flags
clearflags = clearFlags flags

-------------------------------------
-- Helpfull definitions for the tests
instance (Slice sh, Elt a, Elt a')
    => Field1 (Exp (sh :. a)) (Exp (sh :. a')) (Exp a) (Exp a') where
  _1 = lens indexHead (\sh b -> lift (indexTail sh :. b))

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

----------------------------------------------
-- Shape test
test2Funcs :: (P.Eq sh2, Shape sh1, Shape sh2, Elt e1, Elt e2, Elt e3, Elt e4, a ~ Acc (Array sh1 e1), b ~ Acc (Array sh2 e2), c ~ Acc (Array sh1 e3), d ~ Acc (Array sh2 e4))
        => a -> c -> (a -> b) -> (c -> d) -> IO Bool
test2Funcs x1 x2 f1 f2 =
    let
        x1S = travoSharing x1
        x2S = travoSharing x2
        f1S = travoSharingF f1
        f2S = travoSharingF f2
        res = do 
            stx1 <- shOpenAcc SEEmpty x1S
            stx2 <- shOpenAcc SEEmpty x2S
            f1applied <- shOpenAF1 SEEmpty f1S stx1
            f2applied <- shOpenAF1 SEEmpty f2S stx2
            equalShape shOpenAcc f1applied f2applied
        resEval = evalState res 0

        f1Run = arrayShape . I.run $ f1 x1 
        f2Run = arrayShape . I.run $ f2 x2
        resRun = f1Run P.== f2Run
        str = if resRun then "Same shape" else "Not same shape"
    in do
    if resRun P.== resEval
        then do P.putStrLn ("Analysis and run agree: " P.++ str); return True
        else if resRun
                then do P.putStrLn "Analysis couldn't deduce that it is same shaped, but it is"; return True
                else do P.putStrLn "Error analysis says it is same shaped, but it isn't"; return False

test2Funcs' :: (P.Eq sh2, Shape sh1, Shape sh2, Elt e1, Elt e2, Elt e3, a ~ Acc (Array sh1 e1), b ~ Acc (Array sh2 e2), c ~ Acc (Array sh2 e3))
        => a -> (a -> b) -> (a -> c) -> IO Bool
test2Funcs' x1 f1 f2 =
    let
        x1S = travoSharing x1
        f1S = travoSharingF f1
        f2S = travoSharingF f2
        res = do 
            stx1 <- shOpenAcc SEEmpty x1S
            f1applied <- shOpenAF1 SEEmpty f1S stx1
            f2applied <- shOpenAF1 SEEmpty f2S stx1
            equalShape shOpenAcc f1applied f2applied
        resEval = evalState res 0

        f1Run = arrayShape . I.run $ f1 x1 
        f2Run = arrayShape . I.run $ f2 x1
        resRun = f1Run P.== f2Run
        str = if resRun then "Same shape" else "Not same shape"
    in do
    if resRun P.== resEval
        then do P.putStrLn ("Analysis and run agree: " P.++ str); return True
        else if resRun
                then do P.putStrLn "Analysis couldn't deduce that it is same shaped, but it is"; return True
                else do P.putStrLn "Error analysis says it is same shaped, but it isn't"; return False


test1Func :: (P.Eq sh2, Shape sh1, Shape sh2, Elt e1, Elt e2, Elt e3, a ~ Acc (Array sh1 e1), b ~ Acc (Array sh2 e2), c ~ Acc (Array sh2 e3))
         => a -> b -> (a -> c) -> IO Bool
test1Func input input2 = test2Funcs' input (P.const input2)

testFuncOutput :: (P.Eq sh, Shape sh, Elt e, a ~ Acc (Array sh e))
               => a -> (a -> a) -> IO Bool
testFuncOutput x f = test1Func x x f

test2FuncsTup :: (P.Eq sh2, Shape sh1, Shape sh2, Elt e1, Elt e2, a ~ Acc (Array sh1 e1, Array sh1 e1), b ~ Acc (Array sh2 e2, Array sh2 e2)) 
           => a -> (a -> b) -> (a -> b) -> IO Bool
test2FuncsTup input f1 f2 =
    let
        inputS = travoSharing input
        f1S    = travoSharingF f1
        f2S    = travoSharingF f2
        res = do 
            stx <- shOpenAcc SEEmpty inputS
            f1applied <- shOpenAF1 SEEmpty f1S stx
            f2applied <- shOpenAF1 SEEmpty f2S stx
            equalShape shOpenAcc f1applied f2applied
        resEval = evalState res 0

        f1Run = I.run $ f1 input 
        f2Run = I.run $ f2 input
        f1Runa = arrayShape . P.fst $ f1Run
        f1Runb = arrayShape . P.snd $ f1Run
        f2Runa = arrayShape . P.fst $ f2Run
        f2Runb = arrayShape . P.snd $ f2Run
        resRun = f1Runa P.== f2Runa P.&& f1Runb P.== f2Runb
        str = if resRun then "Same shape" else "Not same shape"
    in do
    if resRun P.== resEval
        then do P.putStrLn ("Analysis and run agree: " P.++ str); return True
        else if resRun
                then do P.putStrLn "Analysis couldn't deduce that it is same shaped, but it is"; return True
                else do P.putStrLn "Error analysis says it is same shaped, but it isn't"; return False

--------------------------------
-- Inputs
inputScalar :: Acc (Scalar Int)
inputScalar = unit 10

inputVector :: Acc (Vector Int)
inputVector = generate (lift $ Z :. (10 :: Int)) indexHead

inputVector2 :: Acc (Vector Int)
inputVector2 = map (+1) $ generate (lift $ Z :. (10 :: Int)) indexHead

inputVector3 :: Acc (Vector Int)
inputVector3 = generate (lift $ Z :. (11 :: Int)) indexHead

inputVector4 :: Acc (Vector Int)
inputVector4 = generate (lift $ Z :. (9 :: Int)) indexHead

inputMatrix :: Acc (Matrix Int)
inputMatrix = generate (lift $ Z :. (10 :: Int) :. (6 :: Int)) (\sh -> (3 - indexHead sh) * (3 - indexHead sh))

inputMatrix' :: Acc (Vector Int)
inputMatrix' = generate (lift $ Z :. (6 :: Int)) (\sh -> (3 - indexHead sh) * (3 - indexHead sh))

inputTupple :: Acc (Vector Int, Vector Int)
inputTupple = lift (inputVector, inputVector2)

-- All the different tests are specified below
foldScalarTest :: IO Bool
foldScalarTest = test1Func inputVector inputScalar sum

foldTest :: IO Bool
foldTest = test1Func inputMatrix inputVector (fold (+) 0)

foldTest2 :: IO Bool
foldTest2 = test2Funcs' inputMatrix (fold (+) 0) (fold1 max)

shapeExprTest :: IO Bool
shapeExprTest = test2Funcs inputVector inputVector2 f f
  where
    f xs = generate (lift $ Z :. (2 :: Int) :. size xs) indexHead

zipTest :: IO Bool
zipTest = test1Func inputVector inputVector2 (zip inputVector)

zipTest2 :: IO Bool
zipTest2 = test2Funcs inputVector inputVector3 (zip inputVector3) (zip inputVector)

zipTest3 :: IO Bool
zipTest3 = test2Funcs inputVector inputVector3 (zip inputVector2) (zip inputVector)

zipTest4 :: IO Bool
zipTest4 = test2Funcs inputVector inputVector4 (zip inputVector2) (zip inputVector)

scanTest :: IO Bool
scanTest = test2Funcs' inputVector (scanl (+) 0) (scanr (+) 0)

scanTest2 :: IO Bool
scanTest2 = test2Funcs' inputVector (scanl1 (+)) (scanr (+) 0)

replicateTest :: IO Bool
replicateTest = test2Funcs' inputVector f f
    where
        f = replicate (lift (Z :. (4::Int) :. All))

replicateTest2 :: IO Bool
replicateTest2 = test2Funcs' inputVector f g
    where
        f = replicate (lift (Z :. (4::Int) :. All))
        g = replicate (lift (Z :. (3::Int) :. All))

sliceTest :: IO Bool
sliceTest = test2Funcs' inputMatrix f f
    where
        f xs = slice xs (lift (Z :. (2::Int) :. All))

sliceTest2 :: IO Bool
sliceTest2 = test2Funcs' inputMatrix f g
    where
        f xs = slice xs (lift (Z :. (2::Int) :. All))
        g xs = slice xs (lift (Z :. (1::Int) :. All))

sliceTest3 :: IO Bool
sliceTest3 = test2Funcs' inputMatrix f g
    where
        f xs = slice xs (lift (Z :. (2::Int) :. All))
        g xs = slice xs (lift (Z :. (1::Int) :. All))

--This test only goes right, if we change the prelude function `take` to not use 'the' and 'unit' in succesion.
-- Because using "the" means you are indexing. Which can be unpredictable if the arrays are different.
-- But in newer version, it is used with lenses and that works.    
takeTest :: IO Bool
takeTest = test2Funcs inputVector inputVector2 (take (constant 9)) (take (constant 9))

takeOnTest :: IO Bool
takeOnTest = test2Funcs inputVector inputVector2 f f
    where
        f :: Acc (Vector Int) -> Acc (Vector Int)
        f = takeOn _1 (constant 9)

takeOnTest2 :: IO Bool
takeOnTest2 = test2Funcs inputVector inputVector2 (f 9) (f 2)
    where
        f :: Int -> Acc (Vector Int) -> Acc (Vector Int)
        f x = takeOn _1 (constant x)

tuppleTest :: IO Bool
tuppleTest = test2FuncsTup inputTupple f (P.const inputTupple)
    where
        f (unlift -> (a,b) :: (Acc (Vector Int), Acc (Vector Int))) = lift (generate (shape a) indexHead, b)

tuppleTest2 :: IO Bool
tuppleTest2 = test2FuncsTup inputTupple f (P.const inputTupple)
    where
        f (unlift -> (a,b) :: (Acc (Vector Int), Acc (Vector Int))) = lift (generate (shape a) indexHead, takeOn _1 (constant 9) b)

tupIdxTest :: IO Bool
tupIdxTest = testFuncOutput inputVector f
  where
    f xs = let tup = lift (map (+1) xs, take (constant 9) xs)
           in afst tup

tupIdxTest2 :: IO Bool
tupIdxTest2 = testFuncOutput inputVector f
  where
    f xs = let tup = lift (map (+1) xs, take (constant 9) xs)
           in asnd tup

condTest :: IO Bool
condTest = testFuncOutput inputVector f
  where
    f xs = acond (xs!!(constant 0) > 10) inputVector (map (+1) inputVector)

condTest2 :: IO Bool
condTest2 = testFuncOutput inputVector f
  where
    f xs = acond (xs!!(constant 0) > 10) inputVector (take (constant 9) inputVector)

awhileTest :: IO Bool
awhileTest = testFuncOutput inputVector f
  where
    f = awhile (\x -> unit $ x!!5 <10 ) (map (+1))

awhileTest2 :: IO Bool
awhileTest2 = testFuncOutput inputVector f
  where
    f = awhile (\x -> unit $ x!!0 <10 ) (map (+1) . take (constant 9))


awhileTest3 :: IO Bool
awhileTest3 = testFuncOutput inputVector f
  where
    f = awhile (\x -> unit $ x!!0 >10 ) (map (+1) . take (constant 9))

stencilTest :: IO Bool
stencilTest = testFuncOutput inputVector f
 where
    f = stencil st Clamp
    st (l,c,r) = l + c + r

stencilTest2 :: IO Bool
stencilTest2 = testFuncOutput inputVector f
 where
    f = stencil st Clamp . take (constant 9)
    st (l,c,r) = l + c + r

----------------------------------
-- Vectorize tests

inputSeq1 :: Seq [Vector Int]
inputSeq1 = toSeqOuter inputMatrix

inputSeq2Broken :: Seq [Vector Int]
inputSeq2Broken = streamIn [I.run inputVector, I.run inputVector2]

inputSeq3 :: Seq [Vector Int]
inputSeq3 = produce (constant 10) f
    where
        f (the -> x) = generate (index1 (x + 1)) indexHead

inputSeq4Broken :: Seq [Vector Int]
inputSeq4Broken = streamInReg (Z :. 10) [I.run inputVector, I.run inputVector2]

inputSeq5Broken :: Int -> Seq [Vector Int]
inputSeq5Broken n = streamInReg (Z :. 10) [I.run inputVector | _ <- [1..n]]

inputSeqPair1 :: Seq [(Vector Int, Vector Int)]
inputSeqPair1 = produce (constant 10) f
  where
    f (the -> x) = lift . unzip $ generate (index1 (x + 1)) (\sh -> lift (indexHead sh, indexHead sh - constant 10) )

inputSeqPair2 :: Seq [(Vector Int, Vector Int)]
inputSeqPair2 = zipSeq inputSeq1 inputSeq3

inputSeqPair3 :: Seq [(Vector Int, Vector Int)]
inputSeqPair3 = produce (constant 10) f
  where
    f (the -> _) = lift . unzip $ generate (index1 (constant 5)) (\sh -> lift (indexHead sh, indexHead sh - constant 10) )

inputSeqPair4 :: Seq [(Vector Int, Vector Int)]
inputSeqPair4 = zipSeq inputSeq1 (mapSeq (map (+(constant 10)) ) inputSeq1)

whileSeqTest' :: Seq [Vector Int] -> Acc (Vector Int)
whileSeqTest' = collect . elements . mapSeq f
  where
    f = awhile (\x -> unit $ x!!0 <10 ) (map (+1))

whileSeqTest2' :: Seq [Vector Int] -> Acc (Vector Int)
whileSeqTest2' = collect . elements . mapSeq f
  where
    f = awhile (\x -> unit $ x!!0 <3 ) iter
    iter xs =  map (+1) $ enumFromN (index1 . (+1) . shapeSize $ shape xs) (xs !! (constant 0))

whileSeqTest3' :: Seq [Vector Int] -> Acc (Vector Int)
whileSeqTest3' = collect . elements . mapSeq f
  where
    f xs = asnd . w $ lift (unit (constant 0), xs)
    w = awhile (\x -> unit $ (afst x) !! 0 <3 ) iter
    iter (unlift -> (xs1, xs2) :: (Acc (Scalar Int), Acc (Vector Int))) = lift (map (+1) xs1, map (+1) xs2)

whileSeqTest4' :: Seq [Vector Int] -> Acc (Vector Int)
whileSeqTest4' = collect . elements . mapSeq f
  where
    f xs = asnd . w $ lift (unit (constant 0), xs)
    w = awhile (\x -> unit $ (afst x) !! 0 <3 ) iter
    iter (unlift -> (xs1, xs2) :: (Acc (Scalar Int), Acc (Vector Int))) = lift (map (+1) xs1, g xs2)
    g = map (+1) . take (constant 9)

whileSeqTest5' :: Seq [Vector Int] -> Acc (Vector Int)
whileSeqTest5' = collect . elements . mapSeq f
  where
    f xs = asnd . w $ lift (fill (index1 . constant $ 10) (constant 0), xs)
    w = awhile (\x -> unit $ (size . afst $ x) >3 ) iter
    iter (unlift -> (xs1, xs2) :: (Acc (Vector Int), Acc (Vector Int))) = lift (take (size xs1 - (constant 1)) xs1, g xs2)
    g = map (+1)

acondTest1' :: Seq [(Vector Int, Vector Int)] -> Acc (Vector Int)
acondTest1' = collect . elements . P.uncurry (zipWithSeq f) . unzipSeq
  where
    -- f = zipWith (+)
    f x y = acond (x!! (constant 0) > 10) x y

acondTest2' :: Seq [Vector Int] -> Acc (Vector Int)
acondTest2' = collect . elements . mapSeq f
  where
    -- f = zipWith (+)
    f x = acond (x!! (constant 0) > 10) x (scanl1 (+) x)

acondTest22' :: Seq [Vector Int] -> Acc (Vector Int)
acondTest22' = collect . elements . mapSeq f
  where
    -- f = zipWith (+)
    f x = acond (x!! (constant 0) > 10) x (scanl (+) 0 x)

acondTest3' :: Seq [(Vector Int, Vector Int)] -> Acc (Vector Int)
acondTest3' = collect . elements . mapSeq f
  where
    f ::  Acc (Vector Int, Vector Int) -> Acc (Vector Int)
    f pair = afst $ acond ((afst pair)!! 0 > 10) (h pair) (g pair)
    g (unlift -> (x, y) :: (Acc (Vector Int), Acc (Vector Int)) ) = lift (y, x)
    h (unlift -> (x, y) :: (Acc (Vector Int), Acc (Vector Int)) ) = lift (map (+1) y, x)

acondTest4' :: Seq [(Vector Int, Vector Int)] -> Acc (Vector Int)
acondTest4' = collect . elements . mapSeq f
  where
    f ::  Acc (Vector Int, Vector Int) -> Acc (Vector Int)
    f pair = afst $ acond ((afst pair)!! 0 > 10) (h pair) (g pair)
    g (unlift -> (x, y) :: (Acc (Vector Int), Acc (Vector Int)) ) = lift (y, x)
    h (unlift -> (_, y) :: (Acc (Vector Int), Acc (Vector Int)) ) = lift (map (+1) y, generate (index1 10) indexHead)

zipWithTest' :: Seq [Vector Int] -> Acc (Vector Int)
zipWithTest' = collect . elements . mapSeq f
  where
    f xs = fold1 (+) $ zipWith (\x y -> (x + 2) * y - 10) (scanl1 (+) xs) (map (+ (xs!! 0)) xs)

zipWithTest2' :: Seq [Vector Int] -> Acc (Vector (Int,Int))
zipWithTest2' = collect . elements . mapSeq f
  where
    f xs = zip (scanl1 (+) xs) (map (+ (xs!! 0)) xs)

whileSeqTest1, whileSeqTest2, whileSeqTest3, whileSeqTest4, whileSeqTest5, whileSeqTest6, whileSeqTest7, whileSeqTest8, whileSeqTest9, whileSeqTest10 :: Acc (Vector Int)
whileSeqTest1 = whileSeqTest' inputSeq1
whileSeqTest2 = whileSeqTest' inputSeq3
whileSeqTest3 = whileSeqTest2' inputSeq1
whileSeqTest4 = whileSeqTest2' inputSeq3
whileSeqTest5 = whileSeqTest3' inputSeq1
whileSeqTest6 = whileSeqTest3' inputSeq3
whileSeqTest7 = whileSeqTest4' inputSeq1
whileSeqTest8 = whileSeqTest4' inputSeq3
whileSeqTest9 = whileSeqTest5' inputSeq1
whileSeqTest10 = whileSeqTest5' inputSeq3

acondTest1, acondTest2, acondTest3, acondTest4, acondTest5, acondTest6, acondTest66
  , acondTest7, acondTest8, acondTest9, acondTest10, acondTest11, acondTest12, acondTest13, acondTest14  :: Acc (Vector Int)
acondTest1 = acondTest1' inputSeqPair1
acondTest2 = acondTest1' inputSeqPair2
acondTest3 = acondTest1' inputSeqPair3
acondTest4 = acondTest1' inputSeqPair4
acondTest5 = acondTest2' inputSeq1
acondTest6 = acondTest2' inputSeq3
acondTest66 = acondTest22' inputSeq3
acondTest7 = acondTest3' inputSeqPair1
acondTest8 = acondTest3' inputSeqPair2
acondTest9 = acondTest3' inputSeqPair3
acondTest10 = acondTest3' inputSeqPair4
acondTest11 = acondTest4' inputSeqPair1
acondTest12 = acondTest4' inputSeqPair2
acondTest13 = acondTest4' inputSeqPair3
acondTest14 = acondTest4' inputSeqPair4

zipWithTest1, zipWithTest2 :: Acc (Vector Int) 
zipWithTest1 = zipWithTest' inputSeq1
zipWithTest2 = zipWithTest' inputSeq3
zipWithTest3 = zipWithTest2' inputSeq1
zipWithTest3, zipWithTest4 :: Acc (Vector (Int, Int))
zipWithTest4 = zipWithTest2' inputSeq3


whileSeqTestBroken1, whileSeqTestBroken2, whileSeqTestBroken3, whileSeqTestBroken4, whileSeqTestBroken5, whileSeqTestBroken6 :: Acc (Vector Int)
whileSeqTestBroken1 = whileSeqTest' inputSeq2Broken
whileSeqTestBroken2 = whileSeqTest2' inputSeq2Broken
whileSeqTestBroken3 = whileSeqTest3' inputSeq2Broken
whileSeqTestBroken4 = whileSeqTest' inputSeq4Broken
whileSeqTestBroken5 = whileSeqTest2' inputSeq4Broken
whileSeqTestBroken6 = whileSeqTest3' inputSeq4Broken
whileSeqTestBroken7 :: Int -> Acc (Vector Int)
whileSeqTestBroken7 n = whileSeqTest3' (inputSeq5Broken n)

evalAllVecTests' :: [Acc (Vector Int)] -> IO ()
evalAllVecTests' xs = mapM_ (evaluate . I.run) xs

allVecTests :: [Acc (Vector Int)]
allVecTests = [
    whileSeqTest1, whileSeqTest2, whileSeqTest3, whileSeqTest4, whileSeqTest5, whileSeqTest6, whileSeqTest7, whileSeqTest8, whileSeqTest9, whileSeqTest10
  , acondTest1, acondTest2, acondTest3, acondTest4, acondTest5, acondTest6, acondTest7
  , acondTest8, acondTest9, acondTest10, acondTest11, acondTest12, acondTest13, acondTest14
  , zipWithTest1, zipWithTest2, map fst zipWithTest3, map fst zipWithTest4
  , whileSeqTestBroken1, whileSeqTestBroken2, whileSeqTestBroken3, whileSeqTestBroken4, whileSeqTestBroken5, whileSeqTestBroken6, whileSeqTestBroken7 2 ]

evalAllVecTests :: IO ()
evalAllVecTests = evalAllVecTests' allVecTests
------------------------------------
-- Count parallel actions

average :: Acc (Vector Double) -> Acc (Scalar Double)
average xs = map (/n) sum
    where
      sum = fold1 (+) xs
      n = A.fromIntegral $ indexHead (shape xs) 

conditional :: Acc (Vector Double) -> Acc (Vector Double)
conditional xs = acond p xs (map (+1) xs)
      where
        p = xs!!0 > 1

conditional2 :: Acc (Vector Double) -> Acc (Vector Double)
conditional2 xs = acond p xs (scanl (+) 0 xs)
      where
        p = xs!!0 > 1

scanT :: Acc (Vector Double) -> Acc (Vector Double)
scanT xs = scanl (+) 0 xs

counts :: IO ()
counts = do P.putStrLn "average"
            countF average
            P.putStrLn "condtional"
            countF conditional
            P.putStrLn "condtional2"
            countF conditional2
            P.putStrLn "scanT"
            countF scanT


---------------------------------------------------------
-- Independece tests

predTest :: Acc (Vector Int) -> Acc (Scalar Bool)
predTest xs = let sh = shape xs
                  n = indexHead sh
              in  unit (n > 1)

predTest2 :: Acc (Vector Int) -> Acc (Scalar Bool)
predTest2 xs = unit (xs !! 0 > 10)

predTest3 :: Acc (Vector Int) -> Acc (Scalar Bool)
predTest3 xs = map (>10) (fold1 (+) xs)

predTest4 :: Acc (Vector Int) -> Acc (Scalar Bool)
predTest4 _ = let ys = generate (index2 5 2) indexHead :: Acc (Matrix Int)
                  ys' = fold1All (+) ys
               in map (>10) ys'

predTest5 :: Acc (Vector Int) -> Acc (Scalar Bool)
predTest5 xs = let ys = generate (shape xs) indexHead :: Acc (Vector Int)
                   ys' = fold1All (+) ys
               in  map (>10) ys'

predTest6 :: Acc (Vector Int) -> Acc (Scalar Bool)
predTest6 xs = let ys = backpermute (lift Z) (\sh -> lift (sh :. (0::Int))) xs :: Acc (Scalar Int)
               in  map (>10) ys

predTest7 :: Acc (Vector Int) -> Acc (Scalar Bool)
predTest7 xs = let ys = permute (+) (unit 0) indexTail xs :: Acc (Scalar Int)
               in  map (>10) ys

predTest8 :: Acc (Vector Int) -> Acc (Scalar Bool)
predTest8 xs = let ys = permute (+) (unit 0) indexTail xs :: Acc (Scalar Int)
                   ys' = unit (size ys)
               in  map (>10) ys'

predTest9 :: Acc (Vector Int) -> Acc (Scalar Bool)
predTest9 xs = let ys = generate (shape xs) indexHead :: Acc (Vector Int)
                   ys' = stencil f Clamp ys :: Acc (Vector Int)
                   f :: Stencil3 Int -> Exp Int
                   f (a,b,c) = a + b + c `div` 3

                   zs = unit (size ys') 
               in  map (>10) zs

predTest10 :: Acc (Vector Int) -> Acc (Scalar Bool)
predTest10 xs = let ys = generate (shape xs) indexHead :: Acc (Vector Int)
                    ys' = stencil f Clamp ys :: Acc (Vector Int)
                    f :: Stencil3 Int -> Exp Int
                    f (a,b,c) = a + b + c `div` 3
                    zs = unit (ys' !! 0) 
                in  map (>10) zs

testInds :: (Arrays a, Arrays b) => (Acc a -> Acc b) -> Independence -> Bool
testInds f i = let
    f' = travoSharingF f
    env = PushIE BaseIE undefined i
    ind = indOpenAfun1 env f' 
  in isInd ind


evalIndTests :: (Arrays a, Arrays b) => (String, (Acc a -> Acc b), Bool, Bool, Bool) -> IO (Bool)
evalIndTests (name, f, tI, sI, nI) = do
  let tIres = testInds f TotalInd P.== tI
      sIres = testInds f ShapeInd P.== sI
      nIres = testInds f NotInd   P.== nI
  if P.not tIres then P.putStrLn ("Function \'" P.++ name P.++ "\' gave a wrong answer for independece test for total independent. It should be: " P.++ P.show tI) else return ()
  if P.not sIres then P.putStrLn ("Function \'" P.++ name P.++ "\' gave a wrong answer for independece test for shape independent. It should be: " P.++ P.show sI) else return ()
  if P.not nIres then P.putStrLn ("Function \'" P.++ name P.++ "\' gave a wrong answer for independece test for not independent. It should be: " P.++ P.show nI) else return ()
  if tIres P.&& sIres P.&& nIres then P.putStrLn ("Function \'" P.++ name P.++ "\' is completely right") else return ()
  return (tIres P.&& sIres P.&& nIres)
    
allIndTests'  :: [(String, Acc (Vector Int) -> Acc (Scalar Bool), Bool, Bool, Bool)]
allIndTests' = [ ("predTest", predTest, True, True, False)
               , ("predTest2", predTest2, True, False, False)
               , ("predTest3", predTest3, True, False, False)
               , ("predTest4", predTest4, True, True, True)
               , ("predTest5", predTest5, True, True, False)
               , ("predTest6", predTest6, True, False, False)
               , ("predTest7", predTest7, True, False, False)
               , ("predTest8", predTest8, True, True, False)
               , ("predTest9", predTest9, True, True, False)
               , ("predTest10", predTest10, True, True, False)
              --  , ("predTest11", predTest11, True, True, False)
               ]

allIndTests :: IO [Bool]
allIndTests = mapM evalIndTests allIndTests'


myliftedTest :: Acc (Vector Int) -> Acc (Vector Int)
myliftedTest = liftedAcc (map (+1)) f
  where
    f :: LiftedType (Vector Int) a' -> LiftedType (Vector Int) b' -> P.Maybe (Acc a' -> Acc b')
    f = \ty ty2 -> case (ty,ty2) of
                                  (RegularT,RegularT) -> P.Just (map (+2))
                                  _ -> P.Nothing
                                  


myliftedTestSeq :: Seq [Vector Int] -> Acc (Vector Int)
myliftedTestSeq = collect . elements . mapSeq myliftedTest

data LiftedFunc f where
  LiftedFunc :: (forall b' a'. LiftedType a a' -> LiftedType b b' -> P.Maybe (Acc a' -> Acc b')) -> LiftedFunc (a -> b)


quicksortTestFI :: Seq [Vector Int] -> Acc (Vector Int)
-- quicksortTestFI = collect . elements . mapSeq (afst3 . quicksort)
quicksortTestFI = collect . elements . mapSeq (afst . quicksort)

quicksortTestFB :: Seq [Vector Int] -> Acc (Vector Bool)
-- quicksortTestFB = collect . elements . mapSeq (asnd3 . quicksort)
quicksortTestFB = collect . elements . mapSeq (asnd . quicksort)

-- quicksortTestFD :: Seq [Vector Int] -> Acc (Vector DIM1)
-- quicksortTestFD = collect . elements . mapSeq (athd3 . quicksort)

afst3 :: (Arrays a, Arrays b, Arrays c) => Acc (a,b,c) -> Acc a
afst3 (T3 a _ _) = a

asnd3 :: (Arrays a, Arrays b, Arrays c) => Acc (a,b,c) -> Acc b
asnd3 (T3 _ b _) = b

athd3 :: (Arrays a, Arrays b, Arrays c) => Acc (a,b,c) -> Acc c
athd3 (T3 _ _ c) = c


quicksortTestF2 :: Seq [Vector Int] -> Acc (Vector Int)
quicksortTestF2 = collect . elements . mapSeq quickerror
quicksortTestF3 :: Seq [Vector Int] -> Acc (Vector Int)
quicksortTestF3 = collect . elements . mapSeq f
  where
    f xs = backpermute (index1 6) P.id xs

quicksortTestF4 :: Seq [Vector Int] -> Acc (Vector Int)
quicksortTestF4 = collect . elements . mapSeq f
  where
    --f xs = permute (\x y ->x+y+100) xs (\sh -> index1 ((unindex1 sh + 1) `mod` size xs) ) xs
    f xs = permute (\x y ->x+y+100) xs P.id xs

quicksortTest ::  A.Acc (A.Vector Int)
quicksortTest = quicksortTestFI inputSeq1
quicksortTest' ::  A.Acc (A.Vector Int, A.Vector Bool)
quicksortTest' = quicksort inputMatrix'
quicksortTestB ::  A.Acc (A.Vector Bool)
quicksortTestB = quicksortTestFB inputSeq1
-- quicksortTestD = take 6 $ quicksortTestFD inputSeq1
quicksortTestD :: A.Acc (A.Vector DIM1)
quicksortTestD = generate (index1 6) (\sh -> cond (shapeSize sh > 1) (index1 (-1)) sh)

-- writeTest :: 
writeTest = writeFlags quicksortTestD (initialFlags inputMatrix')
(writeinpA, writeinpB) = I.run . lift $ (quicksortTestD, initialFlags inputMatrix')
writeinpS = zipSeq (streamInReg (Z:.6) [writeinpA, writeinpA]) (streamInReg (Z:.7) [writeinpB, writeinpB])

writeFlags2 :: A.Acc (A.Vector A.DIM1) -> A.Acc (A.Vector Bool) -> A.Acc (A.Vector Bool)
writeFlags2 writes flags = A.permute (&&) flags (writes A.!) t
  where
    -- t = use $ I.run (A.fill (index1 6) $ A.constant True)
    t = (A.fill (A.shape writes) $ A.constant True)

writeFlags' (T2 a b) = writeFlags2 a b

writeTest2 = collect . elements . mapSeq writeFlags' $ writeinpS
writeTest2' = writeFlags (use writeinpA) (use writeinpB)

enum :: Shape sh => Exp sh -> Acc (Array sh sh)
enum sh = generate sh P.id 

test :: (Shape sh, Slice sh, Eq sh) => Exp sh -> Exp Bool
test t = t == ignore

quicksortTest2 = quicksortTestF2 inputSeq1
quicksortTest3 = quicksortTestF3 inputSeq1
quicksortTest4 = quicksortTestF4 inputSeq1

permuteLReg :: (Exp Int -> Exp Int -> Exp Int) -> Acc (Array DIM3 Int) -> (Exp DIM1 -> Exp DIM2) -> Acc (Array DIM2 Int) -> Acc (Array DIM3 Int)
permuteLReg comb def p a =
  let
    p' :: (Exp DIM2 -> Exp DIM3)
    p' sh = let oldsh = indexInit sh
                outer = indexLast sh
            in p oldsh `indexSnoc` outer
  in permute comb def p' a

permuteLReg2 :: forall sh sh'. (Shape sh, Shape sh') => --sh ~ DIM2, sh'~DIM1) =>
  (Exp Int -> Exp Int -> Exp Int) -> Acc (Array (sh :. Int) Int) -> (Acc (Vector sh') -> Acc (Vector sh)) -> Acc (Array (sh' :. Int) Int) -> Acc (Array (sh :. Int) Int)
permuteLReg2 comb def p a =
  let
    --temp = generate (size a) p'

    reg = indexLast $ shape a
    innerInd = indexInit $ shape a
    maxn = shapeSize innerInd
    innerIndSh :: Exp Int -> Acc (Vector (sh :. Int))
    --innerIndSh i = map (\sh -> indexSnoc sh i) . p . fill (index1 reg) $ fromIndex innerInd i
    -- innerIndSh i = generate (index1 reg) $ \sh -> indexSnoc (fromIndex innerInd i) (unindex1 sh)
    innerIndSh i = imap (\j sh -> indexSnoc sh (unindex1 j)) . p . fill (index1 reg) $ fromIndex innerInd i

    thearray :: Acc (Array (sh' :. Int) (sh :. Int))
    thearray = reshape (shape a) . asnd $ awhile check iter init
      where
        check (unlift -> (n,xs :: Acc (Vector (sh :. Int)))) = unit (the n < maxn)
        iter  (unlift -> (n,xs )) = lift (map (+1) n, xs ++ innerIndSh (the n))
        init = lift (unit 0, fill (index1 0) (shape def) )
  in permute comb def (thearray!) a

permTest :: Acc (Array DIM3 Int)
permTest = res
  where
    comb = (+)
    def = generate (index3 4 4 2) (const 0)
    a = generate (index3 4 2 3) (const 1)
    -- p :: Acc (Vector DIM1) -> Acc (Vector DIM2)
    -- p = map (\sh -> lift (indexTrans sh :. (0::Exp Int)))
    p = map indexTrans
    res = permuteLReg2 comb def p a

inputN2' :: Int -> [Vector Int]
inputN2' n = P.replicate n (fromList (Z :. 32) [P.floor (100 * P.cos (x + 15)) | x <- [0..] ])

inputN2 :: Int -> [Vector Int]
inputN2 _ = [I.run . afst. quicksort . use . P.head $ inputN2' 1]

tester :: Acc (Matrix Int)
tester = collect . tabulate . mapSeq (afst . quicksort) . streamIn $ inputN2 2

tester' :: Acc (Matrix Int)
tester' = collect . tabulate . mapSeq (afst . quicksort) . streamInReg (Z :. 32) $ inputN2 2

testerB :: Acc (Matrix Bool)
testerB = collect . tabulate . mapSeq (asnd . quicksort) . streamIn $ inputN2 2

testPerm :: Acc (Vector Int) -> Acc (Vector Int)
testPerm xs = permute (+) (fill (shape xs) (constant 0)) f xs
  where
    f sh = cond (xs!sh >0) sh (indexMove sh)
    indexMove (unindex1->sh) = index1 $ n - sh - 1
    n = size xs

tester2 :: Acc (Matrix Int)
tester2 = collect . tabulate . mapSeq (testPerm) . streamIn $ inputN2 2

tester2' :: Acc (Matrix Int)
tester2' = collect . tabulate . mapSeq (testPerm) . streamInReg (Z :. 32) $ inputN2 2

backpermuteTest :: Acc (Vector Int) -> Acc (Vector Int)
backpermuteTest xs = backpermute (shape xs) f xs
  where
    f sh = cond (xs!sh <0) sh (indexMove sh)
    indexMove (unindex1->sh) = index1 $ n - sh - 1
    n = size xs

scatterTest :: Acc (Vector Int) -> Acc (Vector Int)
scatterTest xs = scatter ints (fill (shape xs) 0) xs 
  where 
    ints = map unindex1 $ imap f xs
    f sh _ = cond (xs!sh <0) sh (indexMove sh)
    indexMove (unindex1->sh) = index1 $ n - sh - 1
    n = size xs


tester3 :: Acc (Matrix Int)
tester3 = collect . tabulate . mapSeq (backpermuteTest) . streamIn $ inputN2 2

tester4 :: Acc (Matrix Int)
tester4 = collect . tabulate . mapSeq (scatterTest) . streamIn $ inputN2 2

tester5 :: Acc (Matrix Int)
tester5 = collect . tabulate . mapSeq (afst . quicksort) . streamIn $ inputN2 1

tester5' :: Acc (Vector Int)
tester5' = afst. quicksort . use . P.head $ inputN2 1

tester5B :: Acc (Matrix Bool)
tester5B = collect . tabulate . mapSeq (asnd . quicksort) . streamIn $ inputN2 1

tester5B' :: Acc (Vector Bool)
tester5B' = asnd. quicksort . use . P.head $ inputN2 1

scanl1Test :: Acc (Vector Int) -> Acc (Vector Int)
scanl1Test xs = scanl1 (+) xs 
  -- where 
    -- ints = map unindex1 $ imap f xs
    -- f sh _ = cond (xs!sh <0) sh (indexMove sh)
    -- indexMove (unindex1->sh) = index1 $ n - sh - 1
    -- n = size xs
flagsB :: Acc (Vector Bool)
flagsB = tester5B'
values :: Acc (Vector Int)
values = tester5'

inputVal' = I.run values
inputVal = streamIn $  [inputVal']


tester6 :: Acc (Matrix Int)
tester6 = collect . tabulate . mapSeq (scanl1Test) . streamIn $ inputN2 1

tester6' :: Acc (Vector Int)
tester6' =  (scanl1Test) . use . P.head $ inputN2 1

indicesSmaller :: Acc (Vector Int) -> Acc (Vector Int)
indicesSmaller xs = A.map (\x -> x - 1) $ postscanSegHead (+) headFlags $ A.map (A.? (0, 1)) isLarger
  where
    headFlags = flagsB
    values = xs
    isLarger = A.zipWith (A.>=) values pivots
    pivots = propagateSegmentHead headFlags values

tester7 :: Acc (Matrix Int)
tester7 = collect . tabulate . mapSeq (indicesSmaller) $ inputVal

tester7' :: Acc (Vector Int)
tester7' =  (indicesSmaller) . use $ inputVal'

propagateSegmentHead2 :: A.Acc (A.Vector Int) -> A.Acc (A.Vector (Int, Bool))
propagateSegmentHead2 values
  -- = A.map A.fst
  = postscanl2 f (T2 undef $ A.constant True)
  $ A.zip values headFlags
  where
    f left (T2 rightValue rightFlag) =
      A.cond rightFlag (T2 rightValue $ A.constant True) left
    headFlags = flagsB

    postscanl2 f e = map (e `f`) . scanl1 f


tester8 :: Acc (Vector (Int,Bool))
tester8 = collect . elements . mapSeq (propagateSegmentHead2) . streamIn $ inputN2 1

tester8' :: Acc (Vector (Int, Bool))
tester8' =  (propagateSegmentHead2) . use . P.head $ inputN2 1

indiceLarger :: Acc (Vector Int) -> Acc (Vector Int)
indiceLarger xs = A.map (\x -> x - 1) $ postscanSegHead (+) headFlags $ A.map (A.? (1, 0)) isLarger
  where
    headFlags = flagsB
    values = xs
    isLarger = A.zipWith (A.>=) values pivots
    pivots = propagateSegmentHead headFlags values

tester9 :: Acc (Matrix Int)
tester9 = collect . tabulate . mapSeq (indiceLarger) . streamIn $ inputN2 1

tester9' :: Acc (Vector Int)
tester9' =  (indiceLarger) . use . P.head $ inputN2 1

countSmaller :: A.Acc (A.Vector Int) -> A.Acc (A.Vector Int)
-- countSmaller xs = A.map (+1) . A.map fst $ propagateSegmentLast2 {-headFlags-} (indicesSmaller xs)
countSmaller xs = A.map (+1) $ propagateSegmentLast2' headFlags (indicesSmaller xs)
  where
    headFlags = flagsB


tester10 :: Acc (Matrix Int)
tester10 = collect . tabulate . mapSeq (countSmaller) $ inputVal

tester10' :: Acc (Vector Int)
tester10' =  (countSmaller) . use $ inputVal'

propagateSegmentLast2' hd = A.map A.fst . propagateSegmentLast2 hd

propagateSegmentLast2 :: A.Acc (A.Vector Bool) -> A.Acc (A.Vector Int) -> A.Acc (A.Vector (Int, Bool))
propagateSegmentLast2 headFlags values
  -- = A.map A.fst
  = postscanr f (T2 undef $ A.constant True)
  $ A.zip values 
  $ A.tail headFlags
  where
    f (T2 leftValue leftFlag) right =
      A.cond leftFlag (T2 leftValue $ A.constant True) right
    -- headFlags = flagsB

    postscanr2 f e = {-map (`f` e) .-} scanr1 f
                     


tester11 :: Acc (Vector (Int,Bool))
tester11 = collect . elements . mapSeq (propagateSegmentLast2 flagsB) . streamIn $ inputN2 1

tester11' :: Acc (Vector (Int, Bool))
tester11' =  (propagateSegmentLast2 flagsB) . use . P.head $ inputN2 1

------------------------------
-- Vectorize internal functions tests

mkHeadFlags :: forall sh. Shape sh => Acc (Segments (sh:.Int)) -> Acc (Vector Int)
mkHeadFlags seg
  = generateSeg seg (\_ _ ix -> shapeSize ix == 0 ? (1, 0))

mkHeadFlags2 :: Acc (Segments DIM1) -> Acc (Vector Int)
mkHeadFlags2 seg
  = init
  $ permute (+) zeros (\ix -> index1 (offset ! ix)) ones
  where
    offset = offsets seg
    len    = totalSize seg
    zeros  = fill (index1  $ len + 1) (0 :: Exp Int)
    ones   = fill (index1  $ size offset) (1 :: Exp Int)


mkTailFlags :: forall sh. Shape sh => Acc (Segments (sh:.Int)) -> Acc (Vector Int)
mkTailFlags seg
  = generateSeg seg (\_ sh ix -> shapeSize ix == shapeSize sh - 1 ? (1, 0))

mkTailFlags2 :: Acc (Segments DIM1) -> Acc (Vector Int)
mkTailFlags2 seg
  = init
  $ permute (+) zeros (\ix -> index1 (len - 1 - offset ! ix)) ones
  where
    offset = offsets seg
    len    = totalSize seg
    zeros  = fill (index1 $ len + 1) (0 :: Exp Int)
    ones   = fill (index1  $ size offset) (1 :: Exp Int)

generateSeg :: forall e sh. (Elt e, Shape sh)
            => Acc (Segments sh)
            -> (Exp Int -> Exp sh -> Exp sh -> Exp e)
            -> Acc (Vector e)
generateSeg segs f = map (\(unlift -> (seg,sh,i)) -> f seg sh (fromIndex sh i)) domain
  where
    shs   = shapes2 segs
    offs  = offsets segs
    ts    = totalSize segs

    -- Using a binary search for each element to preserve fusibility.

    search :: Exp Int -> Exp Int
    search i = fst $ while (uncurry nonconverged) (uncurry f) (lift (0::Exp Int,length offs))
      where
        nonconverged l h = h - l > 1
        f l h =
         let m = (h + l) `div` 2
         in offs !! m > i ?
              ( lift (l,m)
              , lift (m,h) )

    domain = imap (\i s -> lift (s, shs !! s, unindex1 i - offs !! s))
           $ generate (index1 ts) (search . unindex1)

offsets :: Shape sh => Acc (Segments sh) -> Acc (Vector Int)
offsets (unatup3 -> (_,o,_) :: (Acc (Scalar Int), Acc (Vector Int), Acc (Vector sh))) = o

shapes2 :: Shape sh => Acc (Segments sh) -> Acc (Vector sh)
shapes2 (unatup3 -> (_,_,shs)) = shs

totalSize :: Shape sh => Acc (Segments sh) -> Exp Int
totalSize (unatup3 -> (ts,_,_)) = the ts

unatup3 :: (Arrays a, Arrays b, Arrays c) => Acc (a, b, c) -> (Acc a, Acc b, Acc c)
unatup3 (unlift -> (a,b,c)) =
  ( a
  , b
  , c )


segs :: Acc (Segments DIM1)
segs = lift (sz, offsets, ext)
  where
    headFlags = zip flagsB tester5'
    osz = size $ headFlags
    sz = unit $ osz * 2
    offsets = generate (index1 2) (\sh -> shapeSize sh * osz)
    ext = fill (index1 2) (shape headFlags)

inputScan :: Acc (Vector (Int, (Int, Bool)))
inputScan = zip (mkHeadFlags segs) (zip tester5' tester5B')

inputScan2 :: Acc (Vector (Int, (Int, Bool)))
inputScan2 = zip (mkTailFlags segs) (zip tester5' (tail tester5B'))

inputScan3 :: Acc (Vector (Int, (Int, Bool)))
inputScan3 = zip (mkTailFlags2 segs) (zip tester5' (tail tester5B'))

-- type Segments sh = ( Scalar Int  -- Total size in scalar elements
--                    , Vector Int  -- Offsets
--                    , Vector sh   -- Extents
--                    )


-- segmented :: (Elt e, Kit acc)
--           => PreOpenFun acc env aenv (e -> e -> e)
--           -> PreOpenFun acc env aenv ((Int, e) -> (Int, e) -> (Int, e))
-- segmented f = Lam . Lam . Body
--   $ tup (PrimBOr integralType `PrimApp` tup (fstE var1) (fstE var0))
--         (Cond (PrimNEq scalarType `PrimApp` tup (fstE var0) (Const 0))
--               (sndE var0)
--               (subApplyE2 (weakenE2 f) (sndE var0) (sndE var1)))

segmented :: (Elt e) => (Exp e -> Exp e -> Exp e) -> Exp (Int, e) -> Exp (Int, e) -> Exp (Int, e)
segmented f (unlift -> (x1, x2)) (unlift -> (y1, y2)) = lift (x1 .|. y1, cond (y1 /= 0) y2 (f y2 x2))

segmented2 :: (Elt e) => (Exp e -> Exp e -> Exp e) -> Exp (Int, e) -> Exp (Int, e) -> Exp (Int, e)
segmented2 f (unlift -> (x1, x2)) (unlift -> (y1, y2)) = lift (x1 .|. y1, cond (y1 /= 0) y2 (f x2 y2))

segmented3 :: (Elt e) => (Exp e -> Exp e -> Exp e) -> Exp (Int, e) -> Exp (Int, e) -> Exp (Int, e)
segmented3 f (unlift -> (x1, x2)) (unlift -> (y1, y2)) = lift (x1 .|. y1, cond (x1 /= 0) x2 (f x2 y2))



scanTestVec :: Acc (Vector (Int, (Int, Bool))) 
scanTestVec = scanl1 (segmented f) inputScan
  where
    f left (T2 rightValue rightFlag) =
      A.cond rightFlag (T2 rightValue $ A.constant True) left

scanTestVec2 :: Acc (Vector (Int, (Int, Bool))) 
scanTestVec2 = scanl1 (segmented2 f) inputScan
  where
    f left (T2 rightValue rightFlag) =
      A.cond rightFlag (T2 rightValue $ A.constant True) left

scanrTestVec :: Acc (Vector (Int, (Int, Bool))) 
scanrTestVec = scanr1 (segmented f) inputScan2
  where
    f (T2 leftValue leftFlag) right =
      cond leftFlag (T2 leftValue $ constant True) right

scanrTestVec2 :: Acc (Vector (Int, (Int, Bool))) 
scanrTestVec2 = scanr1 (segmented2 f) inputScan2
  where
    f (T2 leftValue leftFlag) right =
      cond leftFlag (T2 leftValue $ constant True) right

scanrTestVec3 :: Acc (Vector (Int, (Int, Bool))) 
scanrTestVec3 = scanr1 (segmented3 f) inputScan2
  where
    f (T2 leftValue leftFlag) right =
      cond leftFlag (T2 leftValue $ constant True) right