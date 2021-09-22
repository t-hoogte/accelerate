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
-- import Data.Foldable                            ( traverse_ )
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
module Main where

import qualified Data.Array.Accelerate as A
import qualified Data.Array.Accelerate.Interpreter as A

main :: IO ()
main = A.test @A.InterpretOp twoMaps `seq` return ()

dotp :: A.Acc (A.Vector Int) -> A.Acc (A.Vector Int) -> A.Acc (A.Scalar Int)
dotp a b = A.fold (+) 0 $ A.zipWith (*) (A.map (+1) a) (A.map (`div` 2) b)

twoMaps :: A.Acc (A.Vector Int) -> A.Acc (A.Vector Int)
twoMaps = A.map (+1) . A.map (*2)
