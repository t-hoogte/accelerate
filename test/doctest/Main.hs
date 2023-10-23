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

import Data.Array.Accelerate as A
import qualified Prelude as P

import Control.Applicative
import Control.Monad                                    
import Data.Binary                                      ( decodeFile, encodeFile )

import Data.Array.Accelerate.Interpreter

import Data.Word
import Data.Random.Normal
import System.Environment
import System.IO
import System.Directory
import System.Random

import Criterion.Main

main :: IO ()
main = print . runN @Interpreter $ difficult (use $ fromList (Z:.20) $ [1..])

dotp :: Acc (Vector Int) -> Acc (Vector Int) -> Acc (Scalar Int)
dotp a b = fold (+) 0 $ zipWith (*) (map (+1) a) (map (`div` 2) b)

diagonal :: (Shape sh, P.Num (Exp b), Elt b) 
         => Acc (Array sh b) -> Acc (Array sh b, Array sh b)
diagonal xs =
  let ys = map (+2) xs
      zs = map (+3) ys
  in T2 ys zs

-- Neither of the backpermutes is allowed to fuse with the map: otherwise the other backpermute cannot be computed.
-- Fusing both is possible, but only with work duplication (we still choose to never do that for now).
-- The backpermutes _are_ allowed to fuse with each other: This should however 1. not be rewarded 2. supported in codegen
difficult :: Acc (Array DIM1 Int) -> Acc (Array DIM1 (Int, Int))
difficult acc = zip 
  (backpermute sh (\(I1 y) -> I1 (y `div` 2)) x) 
  (backpermute sh (\(I1 y) -> I1 (y + 1)) x)
  where
    x = map (+3) acc
    sh = I1 10


complex xs =
  let as = map (+1) xs
      bs = map (+2) xs
      cs = gather bs as -- map (\a -> bs!a) as
      ds = gather as bs -- map (\b -> as!b) bs
  in (cs, ds)

npDifficult xs =
  let ys = map (+1) xs
  in complex ys

-- filter' = filter















-- awhile' :: Acc (Vector Int) -> Acc (Vector Int)
-- awhile' = awhile (\x -> unit ((x ! I1 0) == 0)) P.id

-- iffy :: Acc (Vector Int) -> Acc (Vector Int)
-- iffy acc = if size acc == 20 then twoMaps acc else reshape (Z_ ::. 1) (unit 1)
-- twoMaps :: Acc (Vector Int) -> Acc (Vector Int)
-- twoMaps = map (+1) . map (*2)

-- foo :: Acc (Vector Int) -> Acc (Vector Int)
-- foo a = map (*2) $ if (a ! I1 0) == 2 then map (+1) a else a



-- runningExample :: Acc (Array (Z :. Int) Int) -> Acc (Array (Z :. Int) Int, Array (Z :. Int) Int)
-- runningExample xs = let
--   as = map (`div` 2) xs
--   bs = map (`div` 3) xs
--   cs = map (\a -> bs ! I1 a) as
--   ds = map (\b -> as ! I1 b) bs
--   in T2 cs ds

-- main :: P.IO ()
-- main =
--   P.putStrLn $ test @UniformScheduleFun @InterpretKernel $ zipWith @DIM1 @Int (+)
  
--     -- this fails spectacularly: The problem is that we think we fuse, but we don't actually, because
--     -- the Cluster AST doesn't allow zip's style of SoA trickery yet.
--     -- probably need some SoA translations, e.g. in the `take`s in Make/Reqr and in ClusterIO.
--     -- Would then also need to fix cluster construction, which detects fusion
--   -- P.print $ runN @Interpreter (zipWith (+)) (fromList (Z :. 10) [1::Int ..]) (fromList (Z :. 10) [1..])
  
--     --dotp (fromList (Z :. 10) [1..]) (fromList (Z :. 10) [1..])
--   -- P.print $ run1 @Interpreter (permute (+) (use $ fromList (Z:.10) (P.repeat @P.Int 0)) (\(I1 x) -> Just_ (I1 (x `div` 2)))) $ fromList (Z :. 10) [1..]
--   -- P.putStrLn $ test @UniformScheduleFun @InterpretKernel $ permute (+) (use $ fromList (Z:.10) (P.repeat @P.Int 0)) (\(I1 x) -> Just_ (I1 (x `div` 2)))
--   -- doNTimes 10 P.print
-- -- import qualified Data.Array.Accelerate as A
-- -- import qualified Data.Array.Accelerate.Interpreter as A
-- -- main = do
-- --   putStrLn $ A.test @A.UniformScheduleFun @A.InterpretKernel program
-- --   print $ A.run1 @A.Interpreter program $ A.fromList (A.Z) [20 :: Int]
-- --   where
-- --     program = collatzIndex

-- -- step :: A.Acc (A.Scalar Int, A.Scalar Int) -> A.Acc (A.Scalar Int, A.Scalar Int)
-- -- step (A.T2 x' count') = A.T2 (A.ifThenElse (x `mod` 2 A.== 0) (A.unit $ x `div` 2) (A.unit $ x * 3 + 1)) (A.unit $ count + 1)
-- --   where
-- --     x = A.the x'
-- --     count = A.the count'

-- -- collatzIndex :: A.Acc (A.Scalar Int) -> A.Acc (A.Scalar Int)
-- -- collatzIndex input = A.asnd $ A.awhile (A.unit . (A./= 1) . A.the . A.afst) step (A.T2 input $ A.unit 0)









-- program :: Acc (Vector Float)
-- program = let xs = use $ fromList (Z :. 4) [1,2,3,4]
--               xs'' = A.map (+ 1) (use $ fromList (Z :. 3) [0,1,2])
--               ys = generate (I1 3) (const 2)
--               zs = scatter xs'' (fill (constant (Z :. 4)) 0) xs
--           in A.zipWith (+) ys zs


-- main = putStrLn $ test @UniformScheduleFun @InterpretKernel program








-- -- This implementation works on 2D points. In future, generalise this to some
-- -- arbitrary "feature vector".
-- --
-- type Point a = (a, a)

-- -- Clusters consist of the centroid location as well as its identifier
-- --
-- type Id = Word32
-- type Cluster a = (Id, (a, a))

-- idOfCluster :: Elt a => Exp (Cluster a) -> Exp Id
-- idOfCluster = A.fst

-- centroidOfCluster :: Elt a => Exp (Cluster a) -> Exp (Point a)
-- centroidOfCluster = A.snd

-- -- We'll use this as an intermediate structure; it contains the number of points
-- -- in the set as well as the sum of the x and y coordinates respectively.
-- --
-- type PointSum a = (Word32, (a, a))


-- -- Get the distance (squared) between two points. Since we only compare this
-- -- value, we elide the square root.
-- --
-- distance :: A.Num a => Exp (Point a) -> Exp (Point a) -> Exp a
-- distance u v =
--   let (x1,y1) = unlift u
--       (x2,y2) = unlift v
--   in
--   (x1-x2) P.^ (2::Int) + (y1-y2) P.^ (2::Int)


-- -- For each of the given points, return the cluster Id that that that point is
-- -- closest to.
-- --
-- findClosestCluster
--     :: forall a. (A.RealFloat a, P.RealFloat a)
--     => Acc (Vector (Cluster a))
--     -> Acc (Vector (Point a))
--     -> Acc (Vector Id)
-- findClosestCluster clusters points =
--   A.map (\p -> A.fst $ A.sfoldl (nearest p) z (constant Z) clusters) points
--   where
--     z = constant (-1, inf)

--     nearest :: Exp (Point a) -> Exp (Id, a) -> Exp (Cluster a) -> Exp (Id, a)
--     nearest p st c =
--       let d  = A.snd st
--           d' = distance p (centroidOfCluster c)
--       in
--       d' A.< d ? ( lift (idOfCluster c, d') , st )


-- -- Given a vector of points and a vector of clusters we, we first locate the
-- -- closest cluster to each point, assign that point to their closest cluster,
-- -- and compute the centroid of the cluster. This yields the new centroid
-- -- locations.
-- --
-- makeNewClusters
--     :: forall a. (A.RealFloat a, P.RealFloat a, A.FromIntegral Word32 a)
--     => Acc (Vector (Point a))
--     -> Acc (Vector (Cluster a))
--     -> Acc (Vector (Cluster a))
-- makeNewClusters points clusters
--   = pointSumToCluster
--   . makePointSum
--   . findClosestCluster clusters
--   $ points

-- -- TLM: This setup might be quicker, because it forces the result of
-- --      findClosestCluster to be evaluated, which overall reduces memory
-- --      traffic. However, this is hitting a sharing recovery bug in Accelerate
-- --      so can't be used right now ):
-- --
-- --      As per tip in issue #148, we can get around the bug by making the first
-- --      argument to pipe closed. It turns out that the first version is quicker!
-- --
-- --  = A.uncurry findClosestCluster >-> pointSumToCluster . makePointSum $ A.lift (clusters, points)
--   where
--     npts        = size points
--     nclusters   = size clusters

--     -- Turn the PointSum intermediate structure into the clusters, by averaging
--     -- the cumulative (x,y) positions.
--     --
--     pointSumToCluster :: Acc (Vector (PointSum a)) -> Acc (Vector (Cluster a))
--     pointSumToCluster ps =
--       A.generate (A.shape ps)
--                  (\ix -> lift (A.fromIntegral (unindex1 ix), average (ps A.! ix)))

--     average :: Exp (PointSum a) -> Exp (Point a)
--     average ps =
--       let (n, xy) = unlift ps   :: (Exp Word32, Exp (Point a))
--           (x, y)  = unlift xy
--       in
--       lift (x / A.fromIntegral n, y / A.fromIntegral n) -- TLM: what if there are no points in the cluster??

--     -- Reduce along the rows of 'pointSum' to get the cumulative (x,y) position
--     -- and number of points assigned to each centroid.
--     --
--     makePointSum :: Acc (Vector Id) -> Acc (Vector (PointSum a))
--     makePointSum = A.fold1 addPointSum . compute . pointSum

--     -- The point sum is an intermediate 2D array (it gets fused away, so does
--     -- not exist in memory). The points are laid out along the innermost
--     -- dimension (rows), and down the column is each of the clusters.
--     --
--     -- For each point, we put its (x,y) coordinates into the row corresponding
--     -- to whichever cluster it is closest to, and zeros in each of the other
--     -- rows.
--     --
--     pointSum :: Acc (Vector Id) -> Acc (A.Array DIM2 (PointSum a))
--     pointSum nearest =
--       A.generate (lift (Z:.nclusters:.npts))
--                  (\ix -> let Z:.i:.j = unlift ix    :: Z :. Exp Int :. Exp Int
--                              near    = nearest A.! index1 j

--                              yes     = lift (constant 1, points A.! index1 j)
--                              no      = constant (0, (0, 0))
--                          in
--                          near A.== A.fromIntegral i ? ( yes, no ))

--     addPointSum :: Exp (PointSum a) -> Exp (PointSum a) -> Exp (PointSum a)
--     addPointSum x y =
--       let (c1, u) = unlift x    :: (Exp Word32, Exp (Point a))
--           (c2, v) = unlift y    :: (Exp Word32, Exp (Point a))
--           (x1,y1) = unlift u    :: (Exp a, Exp a)
--           (x2,y2) = unlift v    :: (Exp a, Exp a)
--       in
--       lift (c1+c2, lift (x1+x2, y1+y2) :: Exp (Point a))

-- {--
--     -- Alternative to computing the PointSum structure.
--     --
--     -- This method uses a forward permutation with atomic instructions to create
--     -- the array directly (this method is closer to what one might write
--     -- sequentially). This avoids a parallel reduction, but has very high
--     -- contention. Overall performance much lower, as:
--     --
--     --   number of clusters << number of points
--     --
--     makePointSum :: Acc (Vector (PointSum a))
--     makePointSum = A.permute addPointSum zeros near input
--       where
--         zeros   = A.fill (constant (Z:.nclusters)) (constant (0,(0,0)))
--         input   = A.zip (A.fill (A.shape points) (constant 1)) points
--         near ix = index1 (A.fromIntegral (nearest ! ix))
-- --}


-- -- To complete the k-means algorithm, we loop repeatedly generating new clusters
-- -- positions, until the positions converge (or some maximum iteration limit is
-- -- reached?)
-- --
-- kmeans :: forall a. (A.RealFloat a, P.RealFloat a, A.FromIntegral Word32 a)
--        => Acc (Vector (Point a))        -- the points to cluster
--        -> Acc (Vector (Cluster a))      -- initial cluster positions (guess)
--        -> Acc (Vector (Cluster a))
-- kmeans points clusters
--   = A.asnd
--   $ A.awhile (A.uncurry keepGoing)
--              (\cs -> let (_, old) = unlift cs   :: (Acc (Vector (Cluster a)), Acc (Vector (Cluster a)))
--                          new      = makeNewClusters points old
--                      in
--                      lift (old,new))
--              (lift (clusters, makeNewClusters points clusters))
--   where
--     keepGoing :: Acc (Vector (Cluster a)) -> Acc (Vector (Cluster a)) -> Acc (Scalar Bool)
--     keepGoing xs ys
--       = A.or
--       $ A.zipWith (\c1 c2 -> let (x1,y1) = unlift (centroidOfCluster c1)
--                                  (x2,y2) = unlift (centroidOfCluster c2)
--                              in
--                              abs (x1-x2) A.> 0.01 A.|| abs (y1-y2) A.> 0.01) xs ys


-- -- The largest non-infinite floating point number
-- --
-- inf :: forall a. P.RealFloat a => a
-- inf = P.encodeFloat m n
--   where
--     a           = undefined :: a
--     b           = P.floatRadix a
--     e           = P.floatDigits a
--     (_, e')     = P.floatRange a
--     m           = b P.^ e - 1
--     n           = e' - e

-- main :: IO ()
-- main = do
--   putStrLn $ test @UniformScheduleFun @InterpretKernel $ A.map @DIM2 (*(2::Exp Int))
--   -- inputs                <- (P.&&) <$> doesFileExist "points.bin"
--   --                                 <*> doesFileExist "clusters"
--   -- unless inputs $ do
--   --   print "Running the GenSamples program first to generate random data"
--   --   main'

--   -- points'               <- decodeFile "points.bin"
--   -- initial'              <- read `fmap` readFile "clusters"

--   -- let nclusters   = P.length initial'
--   --     npoints     = P.length points'

--   --     solve       = run1 @Interpreter (kmeans (use points))

--   --     initial :: Vector (Cluster Float)
--   --     initial = A.fromList (Z:.nclusters) initial'

--   --     points :: Vector (Point Float)
--   --     points = A.fromList (Z:.npoints) points'

--   -- -- Warm up first by printing the expected results
--   -- --
--   -- putStrLn $ "number of points: " P.++ show npoints
--   -- putStrLn $ "final clusters:\n"  P.++
--   --   unlines (P.map show (A.toList (solve initial)))

--   -- print $ solve initial


-- type Point' = (Float, Float)

-- zeroPoint :: Point'
-- zeroPoint = (0,0)


-- -- Clusters
-- -----------

-- type Cluster' = (Word32, Point')

-- makeCluster :: Int -> [Point'] -> Cluster'
-- makeCluster clid points
--   = ( P.fromIntegral clid
--     , (a / P.fromIntegral count, b / P.fromIntegral count))
--   where
--     (a,b) = foldl' addPoint zeroPoint points
--     count = P.length points

--     addPoint :: Point' -> Point' -> Point'
--     addPoint (x,y) (u,v) = (x+u,y+v)


-- -- Generate random points
-- -- ----------------------

-- minX, maxX, minY, maxY, minSD, maxSD :: Float
-- minX = -10
-- maxX = 10
-- minY = -10
-- maxY = 10
-- minSD = 1.5
-- maxSD = 2.0

-- main' :: IO ()
-- main' = do
--     -- n: minp: maxp: rest <- fmap (fmap read) getArgs
--     let n = 5
--         minp = 5
--         maxp = 5
--         rest = []

--     case rest of
--         [seed] -> setStdGen (mkStdGen seed)
--         _      -> return ()

--     nps <- replicateM n (randomRIO (minp, maxp))
--     xs  <- replicateM n (randomRIO (minX, maxX))
--     ys  <- replicateM n (randomRIO (minY, maxY))
--     sds <- replicateM n (randomRIO (minSD, maxSD))

--     let params = Data.List.zip5 nps xs ys sds sds

--     -- first generate a set of points for each set of sample parameters
--     ss <- mapM (\(a,b,c,d,e) -> generate2DSamples a b c d e) params
--     let points = concat ss

--     -- dump all the points into the file "points"
--     hsamp <- openFile "points" WriteMode
--     mapM_ (printPoint hsamp) points
--     hClose hsamp

--     encodeFile "points.bin" points

--     -- generate the initial clusters by assigning each point to random
--     -- cluster.
--     gen <- newStdGen
--     let
--         rand_clusters = randomRs (0,n-1) gen :: [Int]
--         arr = accumArray (flip (:)) [] (0,n-1) $
--                 P.zip rand_clusters points
--         clusters = P.map (P.uncurry makeCluster) (assocs arr)
--     writeFile "clusters" (show clusters)

--     -- so we can tell what the answer should be:
--     writeFile "params" (show params)


-- printPoint :: Handle -> Point' -> IO ()
-- printPoint h (x,y) = do
--   hPutStr h (show x)
--   hPutChar h ' '
--   hPutStr h (show y)
--   hPutChar h '\n'

-- generate2DSamples
--     :: Int                      -- number of samples to generate
--     -> Float -> Float           -- X and Y of the mean
--     -> Float -> Float           -- X and Y standard deviations
--     -> IO [Point']
-- generate2DSamples n mx my sdx sdy = do
--   gen <- newStdGen
--   let (genx, geny) = split gen
--       xsamples = normals' (mx,sdx) genx
--       ysamples = normals' (my,sdy) geny
--   return (P.zipWith (,) (P.take n xsamples) ysamples)






