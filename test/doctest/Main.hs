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
{-# LANGUAGE RebindableSyntax #-}
{-# LANGUAGE LambdaCase #-}
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
iffy acc = if size acc == 1 then twoMaps acc else reshape (Z_ ::. 1) (unit 1)
twoMaps :: Acc (Vector Int) -> Acc (Vector Int)
twoMaps = map (+1) . map (*2)-- . use $ fromList (Z :. 10) [1..]

foo (a :: Acc (Vector Int)) = map (*2) $ if (a ! I1 0) == 2 then map (+1) a else a

-- Neither of the backpermutes is allowed to fuse with the map: otherwise the other backpermute cannot be computed.
-- Fusing both is possible, but only with work duplication (we still choose to never do that for now).
-- The backpermutes _are_ allowed to fuse with each other: This should however 1. not be rewarded 2. supported in codegen
difficult :: Acc (Array DIM1 Int) -> Acc (Array DIM1 Int, Array DIM1 Int)
difficult acc = T2 (backpermute sh (\(I1 x) -> I1 (x `div` 2)) x) (backpermute sh (\(I1 x) -> I1 (x - 1)) x)
  where
    x = map (+3) acc
    sh = I1 10

main :: P.IO ()
main = P.putStrLn (test @UniformScheduleFun @InterpretKernel $ difficult) 

