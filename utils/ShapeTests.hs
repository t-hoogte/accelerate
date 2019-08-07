{-# LANGUAGE RecordWildCards #-}
{-# language TypeOperators #-}
{-# language ViewPatterns #-}
{-# language ScopedTypeVariables #-}
{-# language FlexibleContexts #-}
{-# language GADTs #-}
{-# language FlexibleInstances #-}
{-# language MultiParamTypeClasses #-}
module ShapeTests (doAllTest)

where

import Data.Array.Accelerate                              as A hiding (fromInteger, fromRational, fromIntegral)
import qualified Data.Array.Accelerate                    as A (fromInteger, fromRational, fromIntegral)
import Data.Array.Accelerate.Interpreter                  as I
-- import Data.Array.Accelerate.Debug.Flags

import qualified Prelude as P
import Prelude as P (fromIntegral, fromInteger, fromRational, String, return, (>>=), (>>), IO, Maybe(..), maybe, show)

import Data.Array.Accelerate.Trafo
import qualified Data.Array.Accelerate.Trafo.Sharing    as Sharing
import qualified Data.Array.Accelerate.AST              as AST
import Data.Array.Accelerate.Debug.Flags
-- import Data.Array.Accelerate.Trafo.Vectorise  as Vectorise hiding (index1, the, unit)
-- import qualified Data.Array.Accelerate.Trafo.Rewrite    as Rewrite
-- import qualified Data.Array.Accelerate.Trafo.Simplify   as Rewrite
-- import qualified Data.Array.Accelerate.Trafo.Fusion     as Fusion
-- import Data.Array.Accelerate.Array.Lifted               as Lifted
import Data.Array.Accelerate.Trafo.Shape

-- import Data.Array.Accelerate.Pretty.Print (prettyArrays, Val(..), prettyEnv, PrettyEnv(..))
-- import Data.Array.Accelerate.Trafo.Base

-- import Text.PrettyPrint hiding (empty)
import Control.Monad.State.Lazy hiding (lift)
import Control.Lens (lens)
import Control.Lens.Tuple

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

flags = [dump_vectorisation, dump_phases]
setflags, clearflags :: IO ()
setflags = setFlags flags
clearflags = clearFlags flags

-------------------------------------
-- Helpfull defenitions for the tests
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
inputMatrix = generate (lift $ Z :. (11 :: Int) :. (6 :: Int)) indexHead

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

inputSeqPair1 :: Seq [(Vector Int, Vector Int)]
inputSeqPair1 = produce (constant 10) f
  where
    f (the -> x) = lift . unzip $ generate (index1 (x + 1)) (\sh -> lift (indexHead sh, indexHead sh - constant 10) )

inputSeqPair2 :: Seq [(Vector Int, Vector Int)]
inputSeqPair2 = zipSeq inputSeq1 inputSeq3

inputSeqPair3 :: Seq [(Vector Int, Vector Int)]
inputSeqPair3 = produce (constant 10) f
  where
    f (the -> x) = lift . unzip $ generate (index1 (constant 5)) (\sh -> lift (indexHead sh, indexHead sh - constant 10) )

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
    f x = acond (x!! (constant 0) > 10) x (map (+ 10) x)

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
    h (unlift -> (x, y) :: (Acc (Vector Int), Acc (Vector Int)) ) = lift (map (+1) y, generate (index1 10) indexHead)

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

acondTest1, acondTest2, acondTest3, acondTest4, acondTest5, acondTest6 :: Acc (Vector Int)
acondTest1 = acondTest1' inputSeqPair1
acondTest2 = acondTest1' inputSeqPair2
acondTest3 = acondTest1' inputSeqPair3
acondTest4 = acondTest1' inputSeqPair4
acondTest5 = acondTest2' inputSeq1
acondTest6 = acondTest2' inputSeq3
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
zipWithTest4 = zipWithTest2' inputSeq3


whileSeqTestBroken1, whileSeqTestBroken2, whileSeqTestBroken3 :: Acc (Vector Int)
whileSeqTestBroken1 = whileSeqTest' inputSeq2Broken
whileSeqTestBroken2 = whileSeqTest2' inputSeq2Broken
whileSeqTestBroken3 = whileSeqTest3' inputSeq2Broken