-- |
-- Module      : Main
-- Copyright   : [2017..2020] The Accelerate Team
-- License     : BSD3
--
-- Maintainer  : Trevor L. McDonell <trevor.mcdonell@gmail.com>
-- Stability   : experimental
-- Portability : non-portable (GHC extensions)
--

-- module Main where

-- import Build_doctests                           ( flags, pkgs, module_sources )
-- import DatFoldable                            ( traverse_ )
-- import Test.DocTest

-- main :: IO ()
-- main = do
--   traverse_ putStrLn args
--   doctest args
--   where
--     args = flags ++ pkgs ++ module_sources

{-# language FlexibleInstances #-}
{-# language FlexibleContexts #-}
{-# language ScopedTypeVariables #-}
{-# language TemplateHaskell #-}
{-# language TypeApplications #-}
{-# language TypeOperators #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RebindableSyntax #-}
{-# OPTIONS_GHC -Wno-name-shadowing -Wno-unused-matches -Wno-unused-local-binds #-}
module Main where

import Data.Array.Accelerate
import Data.Array.Accelerate.Interpreter
import qualified Prelude as P

dotp :: Acc (Vector Int) -> Acc (Vector Int) -> Acc (Scalar Int)
dotp a b = fold (+) 0 $ zipWith (*) (map (+1) a) (map (`div` 2) b)


-- data Foo = Foo Int Int
--   deriving (Generic, Elt)
-- mkPattern ''Foo

-- mapGen :: Acc (Vector Foo) -> Acc (Matrix Int)
-- mapGen acc = map (match $ \(Foo_ x y) -> x * y) $ generate (I2 size size) (\(I2 i j) -> acc ! I1 (max i j))
--   where
--     I1 size = shape acc

awhile' :: Acc (Vector Int) -> Acc (Vector Int)
awhile' = awhile (\x -> unit ((x ! I1 0) == 0)) P.id

iffy :: Acc (Vector Int) -> Acc (Vector Int)
iffy acc = if size acc == 20 then twoMaps acc else reshape (Z_ ::. 1) (unit 1)
twoMaps :: Acc (Vector Int) -> Acc (Vector Int)
twoMaps = map (+1) . map (*2)

foo (a :: Acc (Vector Int)) = map (*2) $ if (a ! I1 0) == 2 then map (+1) a else a

-- Neither of the backpermutes is allowed to fuse with the map: otherwise the other backpermute cannot be computed.
-- Fusing both is possible, but only with work duplication (we still choose to never do that for now).
-- The backpermutes _are_ allowed to fuse with each other: This should however 1. not be rewarded 2. supported in codegen
-- Currently; the implementation and interpreter 1. does reward it (BAD) 2. gives the correct result (GOOD)
difficult :: Acc (Array DIM1 Int) -> Acc (Array DIM1 (Int, Int))
difficult acc = zip (backpermute sh (\(I1 y) -> I1 (y `div` 2)) x) (backpermute sh (\(I1 y) -> I1 (y + 1)) x)
  where
    x = map (+3) acc
    sh = I1 10

runningExample :: Acc (Array (Z :. Int) Int) -> Acc (Array (Z :. Int) Int, Array (Z :. Int) Int)
runningExample xs = let
  as = map (`div` 2) xs
  bs = map (`div` 3) xs
  cs = map (\a -> bs ! I1 a) as
  ds = map (\b -> as ! I1 b) bs
  in T2 cs ds

main :: P.IO ()
main =
  P.putStrLn $ test @UniformScheduleFun @InterpretKernel $ inputProgram
  -- P.print $ run1 @Interpreter (permute (+) (use $ fromList (Z:.10) (P.repeat @P.Int 0)) (\(I1 x) -> Just_ (I1 (x `div` 2)))) $ fromList (Z :. 10) [1..]
  -- P.putStrLn $ test @UniformScheduleFun @InterpretKernel $ permute (+) (use $ fromList (Z:.10) (P.repeat @P.Int 0)) (\(I1 x) -> Just_ (I1 (x `div` 2)))
  -- doNTimes 10 P.print
-- import qualified Data.Array.Accelerate as A
-- import qualified Data.Array.Accelerate.Interpreter as A
-- main = do
--   putStrLn $ A.test @A.UniformScheduleFun @A.InterpretKernel program
--   print $ A.run1 @A.Interpreter program $ A.fromList (A.Z) [20 :: Int]
--   where
--     program = collatzIndex

-- step :: A.Acc (A.Scalar Int, A.Scalar Int) -> A.Acc (A.Scalar Int, A.Scalar Int)
-- step (A.T2 x' count') = A.T2 (A.ifThenElse (x `mod` 2 A.== 0) (A.unit $ x `div` 2) (A.unit $ x * 3 + 1)) (A.unit $ count + 1)
--   where
--     x = A.the x'
--     count = A.the count'

-- collatzIndex :: A.Acc (A.Scalar Int) -> A.Acc (A.Scalar Int)
-- collatzIndex input = A.asnd $ A.awhile (A.unit . (A./= 1) . A.the . A.afst) step (A.T2 input $ A.unit 0)




-- inputProgram :: Acc GMMIn -> Acc (Vector Float, Matrix Float, Matrix Float)
inputProgram :: Acc (Vector Float)
             -> Acc (Matrix Float)
             -> Acc (Matrix Float)
             -> Acc (Matrix Float)
             -> Acc (Scalar Float)
             -> Acc (Scalar Int)
             -> Acc (Vector Float, Matrix Float, Matrix Float)
inputProgram a0 a1 a2 a3 a4 a5 =
    let
      a6 :: Acc (Scalar (Float, (Int, Float)))
      a6 = map (\x0 -> let x1 = fromIntegral x0 in T2 x1 (T2 x0 x1)) a5
      a7 :: Acc (Matrix Float)  -- Z :. 5 :. 2
      a7 = backpermute
             (I2 (let I1 x0 = shape a0 in x0) (let I2 x0 x1 = shape a3 in x1))
             (\(I2 x0 x1) -> I2 x0 x1)
             a2
      a8 :: Acc (Vector Float)  -- Z :. 5
      a8 = fold (\x0 x1 -> x0 + x1) 0.0 a7
      a9 = zipWith
             (\x0 x1 -> let x2 = x0 * x1 in T2 x2 (T3 x0 x1 x2))
             a8
             (replicate (let I1 x0 = shape a0 in I1 x0) (map (\(T2 x0 _) -> x0) a6))
      a10 = map (\x0 -> let x1 = 0.5 * x0
                            x2 = x1 * x0
                        in T2 x2 (T4 (0.5 :: Exp Float) x0 x1 x2)) a4
      a11 = map
              (\x0 -> let x1 = x0 * x0 in T2 x1 (T2 x0 x1))
              (backpermute
                 (I2 (let I1 x0 = shape a0 in x0)
                  (let I2 x0 x1 = shape a2 in x1 - let I2 x0 x1 = shape a3 in x1))
                 (\(I2 x0 x1) -> I2 x0 (x1 + let I2 x2 x3 = shape a3 in x3))
                 a2)
      a12 = map (\(T2 x0 _) -> x0) a11
      a13 = map (\x0 -> let x1 = exp x0 in T2 x1 (T2 x0 x1)) a7
      a14 = map (\(T2 x0 _) -> x0) a13
      a15 = map (\x0 -> let x1 = x0 * x0 in T2 x1 (T2 x0 x1)) a14
      a16 = map (\(T2 x0 _) -> x0) a15
      a17 = zipWith
              (\x0 x1 -> let x2 = x0 + x1 in T2 x2 (T3 x0 x1 x2))
              (fold (\x0 x1 -> x0 + x1) 0.0 a16)
              (fold (\x0 x1 -> x0 + x1) 0.0 a12)
      a18 = zipWith
              (\x0 x1 -> let x2 = x0 * x1 in T2 x2 (T3 x0 x1 x2))
              (map (\(T2 x0 _) -> x0) a17)
              (replicate (let I1 x0 = shape a0 in I1 x0) (map (\(T2 x0 _) -> x0) a10))
      a19 = zipWith
              (\x0 x1 -> let x2 = x0 - x1 in T2 x2 (T3 x0 x1 x2))
              (map (\(T2 x0 _) -> x0) a18)
              (map (\(T2 x0 _) -> x0) a9)
      a20 = map (\(T2 x0 _) -> x0) a19
      a21 = map
              (\x0 -> let x1 = x0 - (-12.655121) in T2 x1 (T3 x0 (-12.655121 :: Exp Float) x1))
              (fold (\x0 x1 -> x0 + x1) 0.0 a20)
      a22 = fold1 (\x0 x1 -> max x0 x1) a0
      a23 = zipWith
              (\x0 x1 -> let x2 = x0 - x1 in T2 x2 (T3 x0 x1 x2))
              a0
              (replicate (let I1 x0 = shape a0 in I1 x0) a22)
      a24 = map (\x0 -> let x1 = exp x0 in T2 x1 (T2 x0 x1)) (map (\(T2 x0 _) -> x0) a23)
      a25 = map (\(T2 x0 _) -> x0) a24
      a26 = map (\x0 -> let x1 = log x0 in T2 x1 (T2 x0 x1)) (fold (\x0 x1 -> x0 + x1) 0.0 a25)
      a27 = zipWith (\x0 x1 -> let x2 = x0 + x1 in T2 x2 (T3 x0 x1 x2)) (map (\(T2 x0 _) -> x0) a26) a22
      a28 = map
              (\x0 -> let I2 x1 x2 = shape a3
                          x3 = fromIntegral x1
                          x4 = x3 * x0
                      in T2 x4 (T5 x1 x2 x3 x0 x4))
              (map (\(T2 x0 _) -> x0) a27)
      a29 = zipWith
              (\x0 x1 -> let x2 = x0 - x1 in T2 x2 (T3 x0 x1 x2))
              (replicate (I3 All_ (let I1 x0 = shape a0 in x0) All_) a3)
              (replicate (I3 (let I2 x0 x1 = shape a3 in x0) All_ All_) a1)
      a30 = map (\(T2 x0 _) -> x0) a29
      a31 = generate
              (I2 (let I1 x0 = shape a0 in x0)
               (let I2 x0 x1 = shape a2 in x1 - (let I2 x0 x1 = shape a3 in x1) + 1))
              (\(I2 x0 x1) -> let x2 = x1 == 0
                                  x3 = if x2 then 0.0 else 1.0
                              in T2 x3 (T7 x0 x1 (0 :: Exp Int) x2 (0.0 :: Exp Float) (1.0 :: Exp Float) x3))
      a32 = zipWith
              (\x0 x1 -> let x2 = x0 * x1 in T2 x2 (T3 x0 x1 x2))
              (map (\(T2 x0 _) -> x0) a31)
              (backpermute
                 (I2 (let I1 x0 = shape a0 in x0)
                  (let I2 x0 x1 = shape a2 in x1 - (let I2 x0 x1 = shape a3 in x1) + 1))
                 (\(I2 x0 x1) -> I2 x0 (x1 + let I2 x2 x3 = shape a3 in x3 - 1))
                 a2)
      a33 = map (\(T2 x0 _) -> x0) a32
      a34 = zipWith
              (\x0 x1 -> let x2 = x0 * x1 in T2 x2 (T3 x0 x1 x2))
              (backpermute
                 (let I2 x0 x1 = shape a3 in I4 x0 (let I1 x2 = shape a0 in x2) x1 x1)
                 (\(I4 x0 x1 x2 x3) ->
                    if x2 > x3
                       then
                         I2 x1
                         (let I2 x4 x5 = shape a3 in div (x5 * (x5 - 1)) 2 - div ((x5 - 1 - x3) * (x5 - 1 - x3 + 1)) 2
                          + x2
                          - x3
                          - 1
                          + 1)
                       else I2 x1 0)
                 a33)
              (replicate (I4 All_ All_ (let I2 x0 x1 = shape a3 in x1) All_) a30)
      a35 = map (\(T2 x0 _) -> x0) a34
      a36 = zipWith
              (\x0 x1 -> let x2 = x0 * x1 in T2 x2 (T3 x0 x1 x2))
              (replicate (I3 (let I2 x0 x1 = shape a3 in x0) All_ All_) a14)
              a30
      a37 = zipWith
              (\x0 x1 -> let x2 = x0 + x1 in T2 x2 (T3 x0 x1 x2))
              (map (\(T2 x0 _) -> x0) a36)
              (fold (\x0 x1 -> x0 + x1) 0.0 a35)
      a38 = map (\x0 -> let x1 = x0 * x0 in T2 x1 (T2 x0 x1)) (map (\(T2 x0 _) -> x0) a37)
      a39 = map (\(T2 x0 _) -> x0) a38
      a40 = map (\x0 -> let x1 = x0 * 0.5 in T2 x1 (T3 x0 0.5 x1)) (fold (\x0 x1 -> x0 + x1) 0.0 a39)
      a41 = zipWith (\x0 x1 -> let x2 = x0 + x1 in T2 x2 (T3 x0 x1 x2)) a0 a8
      a42 = zipWith
              (\x0 x1 -> let x2 = x0 - x1 in T2 x2 (T3 x0 x1 x2))
              (replicate (I2 (let I2 x0 x1 = shape a3 in x0) All_) (map (\(T2 x0 _) -> x0) a41))
              (map (\(T2 x0 _) -> x0) a40)
      a43 = map (\(T2 x0 _) -> x0) a42
      a44 = fold1 (\x0 x1 -> max x0 x1) a43
      a45 = zipWith
              (\x0 x1 -> let x2 = x0 - x1 in T2 x2 (T3 x0 x1 x2))
              a43
              (replicate (I2 All_ (let I2 x0 x1 = shape a43 in x1)) a44)
      a46 = map (\x0 -> let x1 = exp x0 in T2 x1 (T2 x0 x1)) (map (\(T2 x0 _) -> x0) a45)
      a47 = map (\(T2 x0 _) -> x0) a46
      a48 = map (\x0 -> let x1 = log x0 in T2 x1 (T2 x0 x1)) (fold (\x0 x1 -> x0 + x1) 0.0 a47)
      a49 = zipWith (\x0 x1 -> let x2 = x0 + x1 in T2 x2 (T3 x0 x1 x2)) (map (\(T2 x0 _) -> x0) a48) a44
      a50 = map (\(T2 x0 _) -> x0) a49
      a51 = zipWith
              (\x0 x1 -> let x2 = x0 - x1 in T2 x2 (T3 x0 x1 x2))
              (fold (\x0 x1 -> x0 + x1) 0.0 a50)
              (map (\(T2 x0 _) -> x0) a28)
      a52 = zipWith
              (\x0 x1 -> let x2 = -1837.8771
                             x3 = x2 + x0
                             x4 = x3 + x1
                         in T2 x4 (T6 (1837.8771 :: Exp Float) x2 x0 x1 x3 x4))
              (map (\(T2 x0 _) -> x0) a51)
              (map (\(T2 x0 _) -> x0) a21)
      a53 = zipWith
              (\x0 (T6 x1 x2 x3 x4 x5 x6) -> T2 (0.0 + x0) (x0 + 0.0))
              (generate Z_ (\Z_ -> 1.0))
              (map (\(T2 _ (T6 x0 x1 x2 x3 x4 x5)) -> T6 x0 x1 x2 x3 x4 x5) a52)
      a54 = zipWith
              (\x0 (T3 x1 x2 x3) -> T2 (0.0 + x0) (-x0 + 0.0))
              (map (\(T2 x0 _) -> x0) a53)
              (map (\(T2 _ (T3 x0 x1 x2)) -> T3 x0 x1 x2) a51)
      a55 = map (\(T2 x0 _) -> x0) a54
      a56 = zipWith
              (\x0 (T3 x1 x2 x3) -> T2 (0.0 + x0) (x0 + 0.0))
              (generate (shape a50) (\(I1 _) -> a55 ! Z_))
              (map (\(T2 _ (T3 x0 x1 x2)) -> T3 x0 x1 x2) a49)
      a57 = zipWith
              (\x0 (T2 x1 x2) -> x0 / x1)
              (map (\(T2 x0 _) -> x0) a56)
              (map (\(T2 _ (T2 x0 x1)) -> T2 x0 x1) a48)
      a58 = zipWith
              (\x0 (T3 x1 x2 x3) -> T2 (0.0 + x0) (-x0 + 0.0))
              (zipWith
                 (\x0 (T2 x1 x2) -> x0 * x2)
                 (generate (shape a47) (\(I2 x0 _) -> a57 ! I1 x0))
                 (map (\(T2 _ (T2 x0 x1)) -> T2 x0 x1) a46))
              (map (\(T2 _ (T3 x0 x1 x2)) -> T3 x0 x1 x2) a45)
      a59 = scanl1 (\x0 x1 -> max x0 x1) a43
      a60 = backpermute (let I2 x0 x1 = shape a59 in I2 x0 (x1 - 1)) (\(I2 x0 x1) -> I2 x0 x1) a59
      a61 = zipWith
              (\x0 x1 -> x0 * x1)
              (let
                 a61 = zipWith
                         (\x0 x1 ->
                            let T2 _ x2 = let T2 x2 x3 = if x0 > x1 then T2 1.0 0.0 else T2 0.0 1.0
                                          in T2 (0.0 + x2 :: Exp Float) (x3 + 0.0)
                            in x2)
                         a60
                         (backpermute (let I2 x0 x1 = shape a43 in I2 x0 (x1 - 1)) (\(I2 x0 x1) -> I2 x0 (x1 + 1)) a43)
               in
               generate
                 (let I2 x0 x1 = shape a61 in I2 x0 (x1 + 1))
                 (\(I2 x0 x1) -> if x1 > 0 then a61 ! (I2 x0 (x1 - 1)) else 1.0))
              (scanr
                 (\x0 x1 -> x0 * x1)
                 1.0
                 (zipWith
                    (\x0 x1 ->
                       let T2 x2 _ = let T2 x2 x3 = if x0 > x1 then T2 1.0 0.0 else T2 0.0 1.0
                                     in T2 (0.0 + x2) (x3 + 0.0 :: Exp Float)
                       in x2)
                    a60
                    (backpermute (let I2 x0 x1 = shape a43 in I2 x0 (x1 - 1)) (\(I2 x0 x1) -> I2 x0 (x1 + 1)) a43)))
      a62 = zipWith
              (\x0 (T3 x1 x2 x3) -> T2 (0.0 + x0) (-x0 + 0.0))
              (zipWith
                 (\x0 x1 -> x0 + x1)
                 (zipWith
                    (\x0 x1 -> x0 * x1)
                    (replicate
                       (let I2 _ x0 = shape a61 in I2 All_ x0)
                       (zipWith
                          (\x0 x1 -> x0 + x1)
                          (let a62 = map (\(T2 _ x0) -> x0) a58
                           in
                           fold1
                             (\x0 x1 -> x0 + x1)
                             (reshape
                                (let I2 x0 x1 = let I2 x0 x1 = shape a62 in I2 x0 x1 in I2 x0 x1)
                                (backpermute (let I2 x0 x1 = shape a62 in I2 x0 x1) (\(I2 x0 x1) -> I2 x0 x1) a62)))
                          (map (\(T2 _ x0) -> x0) a56)))
                    a61)
                 (map (\(T2 x0 _) -> x0) a58))
              (map (\(T2 _ (T3 x0 x1 x2)) -> T3 x0 x1 x2) a42)
      a63 = zipWith
              (\x0 (T3 x1 x2 x3) -> T2 (0.0 + x0) (x0 + 0.0))
              (let a63 = map (\(T2 x0 _) -> x0) a62
               in
               fold1
                 (\x0 x1 -> x0 + x1)
                 (reshape
                    (let I2 x0 x1 = let I2 x0 x1 = shape a63 in I2 x1 x0 in I2 x0 x1)
                    (backpermute (let I2 x0 x1 = shape a63 in I2 x1 x0) (\(I2 x0 x1) -> I2 x1 x0) a63)))
              (map (\(T2 _ (T3 x0 x1 x2)) -> T3 x0 x1 x2) a41)
      a64 = zipWith
              (\x0 (T3 x1 x2 x3) -> x0 * x2)
              (map (\(T2 _ x0) -> x0) a62)
              (map (\(T2 _ (T3 x0 x1 x2)) -> T3 x0 x1 x2) a40)
      a65 = zipWith
              (\x0 (T3 x1 x2 x3) -> T2 (0.0 + x0) (x0 + 0.0))
              (zipWith
                 (\x0 (T2 x1 x2) -> x0 * x1 + x0 * x1)
                 (generate (shape a39) (\(I3 x0 x1 _) -> a64 ! (I2 x0 x1)))
                 (map (\(T2 _ (T2 x0 x1)) -> T2 x0 x1) a38))
              (map (\(T2 _ (T3 x0 x1 x2)) -> T3 x0 x1 x2) a37)
      a66 = zipWith
              (\x0 (T3 x1 x2 x3) -> T2 (0.0 + x0 * x2) (x0 * x1 + 0.0))
              (map (\(T2 x0 _) -> x0) a65)
              (map (\(T2 _ (T3 x0 x1 x2)) -> T3 x0 x1 x2) a36)
      a67 = map (\(T2 _ x0) -> x0) a65
      a68 = zipWith
              (\x0 (T3 x1 x2 x3) -> T2 (0.0 + x0 * x2) (x0 * x1 + 0.0))
              (generate (shape a35) (\(I4 x0 x1 x2 _) -> a67 ! (I3 x0 x1 x2)))
              (map (\(T2 _ (T3 x0 x1 x2)) -> T3 x0 x1 x2) a34)
      a69 = zipWith
              (\x0 (T3 x1 x2 x3) -> T2 (0.0 + x0) (-x0 + 0.0))
              (zipWith
                 (\x0 x1 -> x0 + x1)
                 (let a69 = map (\(T2 _ x0) -> x0) a68
                  in
                  fold1
                    (\x0 x1 -> x0 + x1)
                    (reshape
                       (let I4 x0 x1 x2 x3 = let I4 x0 x1 x2 x3 = shape a69 in I4 x0 x1 x3 x2 in I4 x0 x1 x2 x3)
                       (backpermute
                          (let I4 x0 x1 x2 x3 = shape a69 in I4 x0 x1 x3 x2)
                          (\(I4 x0 x1 x2 x3) -> I4 x0 x1 x3 x2)
                          a69)))
                 (map (\(T2 _ x0) -> x0) a66))
              (map (\(T2 _ (T3 x0 x1 x2)) -> T3 x0 x1 x2) a29)
      a70 = zipWith
              (\x0 (T3 x1 x2 x3) -> T2 (0.0 + x0) (x0 + 0.0))
              (zipWith
                 (\x0 (T5 x1 x2 x3 x4 x5) -> x0 * x3)
                 (map (\(T2 _ x0) -> x0) a54)
                 (map (\(T2 _ (T5 x0 x1 x2 x3 x4)) -> T5 x0 x1 x2 x3 x4) a28))
              (map (\(T2 _ (T3 x0 x1 x2)) -> T3 x0 x1 x2) a27)
      a71 = zipWith
              (\x0 (T2 x1 x2) -> x0 / x1)
              (map (\(T2 x0 _) -> x0) a70)
              (map (\(T2 _ (T2 x0 x1)) -> T2 x0 x1) a26)
      a72 = zipWith
              (\x0 (T3 x1 x2 x3) -> T2 (0.0 + x0) (-x0 + 0.0))
              (zipWith
                 (\x0 (T2 x1 x2) -> x0 * x2)
                 (generate (shape a25) (\(I1 _) -> a71 ! Z_))
                 (map (\(T2 _ (T2 x0 x1)) -> T2 x0 x1) a24))
              (map (\(T2 _ (T3 x0 x1 x2)) -> T3 x0 x1 x2) a23)
      a73 = scanl1 (\x0 x1 -> max x0 x1) a0
      a74 = backpermute (let I1 x0 = shape a73 in I1 (x0 - 1)) (\(I1 x0) -> I1 x0) a73
      a75 = zipWith
              (\x0 x1 -> x0 * x1)
              (let
                 a75 = zipWith
                         (\x0 x1 ->
                            let T2 _ x2 = let T2 x2 x3 = if x0 > x1 then T2 1.0 0.0 else T2 0.0 1.0
                                          in T2 (0.0 + x2 :: Exp Float) (x3 + 0.0)
                            in x2)
                         a74
                         (backpermute (let I1 x0 = shape a0 in I1 (x0 - 1)) (\(I1 x0) -> I1 (x0 + 1)) a0)
               in
               generate (let I1 x0 = shape a75 in I1 (x0 + 1)) (\(I1 x0) -> if x0 > 0 then a75 ! I1 (x0 - 1) else 1.0))
              (scanr
                 (\x0 x1 -> x0 * x1)
                 1.0
                 (zipWith
                    (\x0 x1 ->
                       let T2 x2 _ = let T2 x2 x3 = if x0 > x1 then T2 1.0 0.0 else T2 0.0 1.0
                                     in T2 (0.0 + x2) (x3 + 0.0 :: Exp Float)
                       in x2)
                    a74
                    (backpermute (let I1 x0 = shape a0 in I1 (x0 - 1)) (\(I1 x0) -> I1 (x0 + 1)) a0)))
      a76 = zipWith
              (\x0 (T3 x1 x2 x3) -> x0)
              (map (\(T2 _ x0) -> x0) a53)
              (map (\(T2 _ (T3 x0 x1 x2)) -> T3 x0 x1 x2) a21)
      a77 = zipWith
              (\x0 (T3 x1 x2 x3) -> T2 (0.0 + x0) (-x0 + 0.0))
              (generate (shape a20) (\(I1 _) -> a76 ! Z_))
              (map (\(T2 _ (T3 x0 x1 x2)) -> T3 x0 x1 x2) a19)
      a78 = zipWith
              (\x0 (T3 x1 x2 x3) -> T2 (0.0 + x0 * x2) (x0 * x1 + 0.0))
              (map (\(T2 x0 _) -> x0) a77)
              (map (\(T2 _ (T3 x0 x1 x2)) -> T3 x0 x1 x2) a18)
      a79 = zipWith
              (\x0 (T3 x1 x2 x3) -> T2 (0.0 + x0) (x0 + 0.0))
              (map (\(T2 x0 _) -> x0) a78)
              (map (\(T2 _ (T3 x0 x1 x2)) -> T3 x0 x1 x2) a17)
      a80 = map (\(T2 x0 _) -> x0) a79
      a81 = map (\(T2 _ x0) -> x0) a79
      a82 = zipWith
              (\x0 (T3 x1 x2 x3) -> T2 (0.0 + x0 * x2) (x0 * x1 + 0.0))
              (map (\(T2 _ x0) -> x0) a77)
              (map (\(T2 _ (T3 x0 x1 x2)) -> T3 x0 x1 x2) a9)
      a83 = zipWith (\x0 x1 -> x0 + x1) (map (\(T2 x0 _) -> x0) a82) (map (\(T2 _ x0) -> x0) a63)
    in
    T3 (zipWith
          (\x0 x1 -> x0 + x1)
          (zipWith
             (\x0 x1 -> x0 + x1)
             (zipWith
                (\x0 x1 -> x0 + x1)
                (zipWith
                   (\x0 x1 -> x0 + x1)
                   (zipWith
                      (\x0 x1 -> x0 + x1)
                      (generate (shape a0) (\_ -> 0.0))
                      (generate (shape a0) (\_ -> 0.0)))
                   (generate (shape a0) (\_ -> 0.0)))
                (generate (shape a0) (\_ -> 0.0)))
             (generate (shape a0) (\_ -> 0.0)))
          (zipWith
             (\x0 x1 -> x0 + x1)
             (zipWith
                (\x0 x1 -> x0 + x1)
                (zipWith
                   (\x0 x1 -> x0 + x1)
                   (zipWith
                      (\x0 x1 -> x0 + x1)
                      (generate (shape a0) (\_ -> 0.0))
                      (generate (shape a0) (\_ -> 0.0)))
                   (generate (shape a0) (\_ -> 0.0)))
                (zipWith
                   (\x0 x1 -> x0 + x1)
                   (zipWith
                      (\x0 x1 -> x0 + x1)
                      (zipWith
                         (\x0 x1 -> x0 + x1)
                         (generate (shape a0) (\_ -> 0.0))
                         (generate (shape a0) (\_ -> 0.0)))
                      (zipWith
                         (\x0 x1 -> x0 + x1)
                         (zipWith
                            (\x0 x1 -> x0 + x1)
                            (generate (shape a0) (\_ -> 0.0))
                            (zipWith
                               (\x0 x1 -> x0 + x1)
                               (zipWith
                                  (\x0 x1 -> x0 + x1)
                                  (zipWith
                                     (\x0 x1 -> x0 + x1)
                                     (zipWith
                                        (\x0 x1 -> x0 * x1)
                                        (replicate
                                           (let I1 x0 = shape a75 in I1 x0)
                                           (zipWith
                                              (\x0 x1 -> x0 + x1)
                                              (let a84 = map (\(T2 _ x0) -> x0) a72
                                               in
                                               fold1
                                                 (\x0 x1 -> x0 + x1)
                                                 (reshape
                                                    (let I1 x0 = let I1 x0 = shape a84 in I1 x0 in I1 x0)
                                                    (backpermute (let I1 x0 = shape a84 in I1 x0) (\(I1 x0) -> I1 x0) a84)))
                                              (map (\(T2 _ x0) -> x0) a70)))
                                        a75)
                                     (map (\(T2 x0 _) -> x0) a72))
                                  (map (\(T2 x0 _) -> x0) a63))
                               (generate (shape a0) (\_ -> 0.0))))
                         (generate (shape a0) (\_ -> 0.0))))
                   (generate (shape a0) (\_ -> 0.0))))
             (generate (shape a0) (\_ -> 0.0))))
    (zipWith
       (\x0 x1 -> x0 + x1)
       (zipWith
          (\x0 x1 -> x0 + x1)
          (zipWith
             (\x0 x1 -> x0 + x1)
             (zipWith
                (\x0 x1 -> x0 + x1)
                (zipWith
                   (\x0 x1 -> x0 + x1)
                   (generate (shape a1) (\_ -> 0.0))
                   (generate (shape a1) (\_ -> 0.0)))
                (generate (shape a1) (\_ -> 0.0)))
             (generate (shape a1) (\_ -> 0.0)))
          (zipWith
             (\x0 x1 -> x0 + x1)
             (zipWith
                (\x0 x1 -> x0 + x1)
                (zipWith
                   (\x0 x1 -> x0 + x1)
                   (zipWith
                      (\x0 x1 -> x0 + x1)
                      (generate (shape a1) (\_ -> 0.0))
                      (generate (shape a1) (\_ -> 0.0)))
                   (zipWith
                      (\x0 x1 -> x0 + x1)
                      (zipWith
                         (\x0 x1 -> x0 + x1)
                         (zipWith
                            (\x0 x1 -> x0 + x1)
                            (generate (shape a1) (\_ -> 0.0))
                            (zipWith
                               (\x0 x1 -> x0 + x1)
                               (zipWith
                                  (\x0 x1 -> x0 + x1)
                                  (zipWith
                                     (\x0 x1 -> x0 + x1)
                                     (generate (shape a1) (\_ -> 0.0))
                                     (let a84 = map (\(T2 _ x0) -> x0) a69
                                      in
                                      fold1
                                        (\x0 x1 -> x0 + x1)
                                        (reshape
                                           (let I3 x0 x1 x2 = let I3 x0 x1 x2 = shape a84 in I3 x1 x2 x0 in I3 x0 x1 x2)
                                           (backpermute
                                              (let I3 x0 x1 x2 = shape a84 in I3 x1 x2 x0)
                                              (\(I3 x0 x1 x2) -> I3 x2 x0 x1)
                                              a84))))
                                  (generate (shape a1) (\_ -> 0.0)))
                               (generate (shape a1) (\_ -> 0.0))))
                         (generate (shape a1) (\_ -> 0.0)))
                      (generate (shape a1) (\_ -> 0.0))))
                (generate (shape a1) (\_ -> 0.0)))
             (generate (shape a1) (\_ -> 0.0))))
       (generate (shape a1) (\_ -> 0.0)))
    (zipWith
       (\x0 x1 -> x0 + x1)
       (zipWith
          (\x0 x1 -> x0 + x1)
          (zipWith
             (\x0 x1 -> x0 + x1)
             (zipWith
                (\x0 x1 -> x0 + x1)
                (zipWith
                   (\x0 x1 -> x0 + x1)
                   (generate (shape a2) (\_ -> 0.0))
                   (generate (shape a2) (\_ -> 0.0)))
                (generate (shape a2) (\_ -> 0.0)))
             (zipWith
                (\x0 x1 -> x0 + x1)
                (zipWith
                   (\x0 x1 -> x0 + x1)
                   (zipWith
                      (\x0 x1 -> x0 + x1)
                      (zipWith
                         (\x0 x1 -> x0 + x1)
                         (generate (shape a2) (\_ -> 0.0))
                         (zipWith
                            (\x0 x1 -> x0 + x1)
                            (zipWith
                               (\x0 x1 -> x0 + x1)
                               (zipWith
                                  (\x0 x1 -> x0 + x1)
                                  (zipWith
                                     (\x0 x1 -> x0 + x1)
                                     (zipWith
                                        (\x0 x1 -> x0 + x1)
                                        (generate (shape a2) (\_ -> 0.0))
                                        (generate (shape a2) (\_ -> 0.0)))
                                     (zipWith
                                        (\x0 x1 -> x0 + x1)
                                        (zipWith
                                           (\x0 x1 -> x0 + x1)
                                           (permute
                                              (\x0 x1 -> x0 + x1)
                                              (generate (shape a2) (\_ -> 0.0))
                                              (\(I2 x0 x1) -> Just_ (I2 x0 x1))
                                              (zipWith
                                                 (\x0 x1 -> x0 + x1)
                                                 (generate (shape a7) (\(I2 x0 _) -> a83 ! I1 x0))
                                                 (zipWith
                                                    (\x0 (T2 x1 x2) -> x0 * x2)
                                                    (zipWith
                                                       (\x0 x1 -> x0 + x1)
                                                       (zipWith
                                                          (\x0 (T2 x1 x2) -> x0 * x1 + x0 * x1)
                                                          (generate (shape a16) (\(I2 x0 _) -> a80 ! I1 x0))
                                                          (map (\(T2 _ (T2 x0 x1)) -> T2 x0 x1) a15))
                                                       (let a84 = map (\(T2 x0 _) -> x0) a66
                                                        in
                                                        fold1
                                                          (\x0 x1 -> x0 + x1)
                                                          (reshape
                                                             (let I3 x0 x1 x2 = let I3 x0 x1 x2 = shape a84 in I3 x1 x2 x0
                                                              in
                                                              I3 x0 x1 x2)
                                                             (backpermute
                                                                (let I3 x0 x1 x2 = shape a84 in I3 x1 x2 x0)
                                                                (\(I3 x0 x1 x2) -> I3 x2 x0 x1)
                                                                a84))))
                                                    (map (\(T2 _ (T2 x0 x1)) -> T2 x0 x1) a13))))
                                           (permute
                                              (\x0 x1 -> x0 + x1)
                                              (generate (shape a2) (\_ -> 0.0))
                                              (\(I2 x0 x1) -> Just_ (I2 x0 (x1 + let I2 x2 x3 = shape a3 in x3)))
                                              (zipWith
                                                 (\x0 (T2 x1 x2) -> x0 * x1 + x0 * x1)
                                                 (generate (shape a12) (\(I2 x0 _) -> a81 ! I1 x0))
                                                 (map (\(T2 _ (T2 x0 x1)) -> T2 x0 x1) a11))))
                                        (permute
                                           (\x0 x1 -> x0 + x1)
                                           (generate (shape a2) (\_ -> 0.0))
                                           (\(I2 x0 x1) -> Just_ (I2 x0 (x1 + let I2 x2 x3 = shape a3 in x3 - 1)))
                                           (map
                                              (\(T2 _ x0) -> x0)
                                              (zipWith
                                                 (\x0 (T3 x1 x2 x3) -> T2 (0.0 + x0 * x2) (x0 * x1 + 0.0))
                                                 (permute
                                                    (\x0 x1 -> x0 + x1)
                                                    (generate (shape a33) (\_ -> 0.0))
                                                    (\(I4 x0 x1 x2 x3) ->
                                                       let
                                                         T2 x4 x5 = if x2 > x3
                                                                       then
                                                                         T2 x1
                                                                         (let I2 x4 x5 = shape a3
                                                                          in
                                                                          div (x5 * (x5 - 1)) 2
                                                                          - div ((x5 - 1 - x3) * (x5 - 1 - x3 + 1)) 2
                                                                          + x2
                                                                          - x3
                                                                          - 1
                                                                          + 1)
                                                                       else T2 x1 0
                                                       in
                                                       Just_ (I2 x4 x5))
                                                    (map (\(T2 x0 _) -> x0) a68))
                                                 (map (\(T2 _ (T3 x0 x1 x2)) -> T3 x0 x1 x2) a32))))))
                                  (generate (shape a2) (\_ -> 0.0)))
                               (generate (shape a2) (\_ -> 0.0)))
                            (generate (shape a2) (\_ -> 0.0))))
                      (generate (shape a2) (\_ -> 0.0)))
                   (generate (shape a2) (\_ -> 0.0)))
                (generate (shape a2) (\_ -> 0.0))))
          (generate (shape a2) (\_ -> 0.0)))
       (generate (shape a2) (\_ -> 0.0)))
