{-# LANGUAGE RankNTypes          #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE GADTs               #-}
module Data.Array.Accelerate.Analysis.ActionsCount(
    -- * functions that count the number of parallel actions that are present in the AST.
    Actions,
    countAcc, countOpenAcc, cntAcc, countAFun, 
    countDOpenA, countDAOpenFun,

    -- * Auxiliary functions, for determing parallel action when vectorizing
    reg, irreg, reg2, irreg2, countF, countFReg,
)
  where

import Data.Array.Accelerate.AST 
import Data.Array.Accelerate.Type
-- import Data.Array.Accelerate.Trafo.Base
import Data.Array.Accelerate.Array.Sugar
import Data.Array.Accelerate.Trafo
import qualified Data.Array.Accelerate.Smart as S

import Data.Array.Accelerate as A hiding ((++), Acc, max)



--The actions we count, currently only parallel and we use integers to count them
type Actions = ParallelActions
type ParallelActions = Int

type Counter acc = forall aenv t. acc aenv t -> Actions

addPar :: Int -> Actions -> Actions
addPar n par = par + n

maxA :: Actions -> Actions -> Actions
maxA = max

addPar1 :: Actions -> Actions
addPar1 = addPar 1

zeroA :: Actions
zeroA = 0

-- avrA :: Actions -> Actions -> ActionsAS
-- avrA x y = x +^ y /2

(+^) :: Actions -> Actions -> Actions
(+^) = (+)

cntAcc :: Arrays a => Acc a -> Actions
cntAcc = countOpenAcc

countDOpenA :: DelayedOpenAcc aenv a -> Actions
countDOpenA (Manifest b) = countAcc countDOpenA b 
--We consider the Delayed construct as a sort of generate, thus a parallel action
countDOpenA (Delayed _ _ _) = addPar1 zeroA

countDAOpenFun :: DelayedOpenAfun aenv a -> Actions
countDAOpenFun (Abody b) = countDOpenA b
countDAOpenFun (Alam f) = countDAOpenFun f

countAFun :: Afun a -> Actions
countAFun = countAOpenFun

countAOpenFun :: OpenAfun aenv a -> Actions
countAOpenFun (Abody b) = countOpenAcc b
countAOpenFun (Alam f) = countAOpenFun f

countOpenAcc :: OpenAcc aenv t -> Actions
countOpenAcc (OpenAcc pacc) = countAcc countOpenAcc pacc

countPreOpenAfun :: Counter acc -> PreOpenAfun acc aenv t -> Actions
countPreOpenAfun cA (Abody b) = cA b
countPreOpenAfun cA (Alam f)  = countPreOpenAfun cA f

cTup :: Counter acc -> Atuple (acc aenv) t' -> Actions
cTup _  NilAtup        = zeroA
cTup cA (SnocAtup t a) = cA a +^ cTup cA t

countAcc :: forall acc aenv t. Counter acc -> PreOpenAcc acc aenv t -> Actions
--independentShapeArray :: forall acc aenv t. Kit acc => PreOpenAcc acc aenv t -> (Bool, Bool)
countAcc cA acc =
  let
    cAF :: PreOpenAfun acc aenv' t' -> Actions
    cAF = countPreOpenAfun cA
  in
  case acc of
    -- We just assume that everything that is being made as a let binding, is used. Just a simple assumption
    Alet a b            -> cA a +^ cA b
    Avar _              -> zeroA
    Atuple tup          -> cTup cA tup
    Aprj _ a            -> cA a
    Apply f a           -> cAF f +^ cA a
    Aforeign _ f a      -> cAF f +^ cA a
    LiftedAFun f _ a    -> cAF f +^ cA a
    -- We don't know which branch we take. Thus we just take the one with the maximum parallel actions
    Acond _ t e         -> maxA (cA t) (cA e)
    Awhile p it i       -> cAF p +^ cAF it +^  cA i
    Use _               -> zeroA
    Unit _              -> zeroA
    Reshape _ a         -> cA a
    Generate _ _        -> addPar1 $ zeroA
    Transform _ _ _ a   -> addPar1 $ cA a
    Subarray _ _ _      -> zeroA
    Replicate _ _ a     -> addPar1 $ cA a
    Slice _ a _         -> addPar1 $ cA a
    Map _ a             -> addPar1 $ cA a
    ZipWith _ a1 a2     -> addPar1 $ cA a1 +^ cA a2
    Fold _ _ a          -> addPar1 $ cA a
    Fold1 _ a           -> addPar1 $ cA a
    FoldSeg _ _ _ a     -> addPar1 $ cA a
    Fold1Seg _ _ a      -> addPar1 $ cA a
    Scanl _ _ a         -> addPar1 $ cA a
    Scanl' _ _ a        -> addPar1 $ cA a
    Scanl1 _ a          -> addPar1 $ cA a
    Scanr _ _ a         -> addPar1 $ cA a
    Scanr' _ _ a        -> addPar1 $ cA a
    Scanr1 _ a          -> addPar1 $ cA a
    Permute _ a1 _ a2     -> addPar1 $ cA a1 +^ cA a2
    Backpermute _ _ a   -> addPar1 $ cA a
    Stencil _ _ a       -> addPar1 $ cA a
    Stencil2 _ _ a1 _ a2
                        -> addPar1 $ cA a1 +^ cA a2
    Collect _ _ _ seq   -> countSeq cA seq

countSeq :: forall index acc aenv t. Counter acc -> PreOpenSeq index acc aenv t -> Actions
countSeq cA seq = let
  countProd :: Producer index acc aenv a -> Actions
  countProd p = case p of
    Pull _ -> zeroA
    Subarrays _ _ -> zeroA
    FromSegs s _ a -> cA s +^ cA a
    Produce _ f -> countPreOpenAfun cA f
    ProduceAccum _ f a -> countPreOpenAfun cA f +^ cA a 

  countCons :: Consumer index acc aenv a -> Actions
  countCons c = case c of
    FoldBatch f s a -> countPreOpenAfun cA f +^ cA a +^ cA s
    Last a _ -> cA a
    Stuple tup -> cTup (countSeq cA) tup
    Elements a -> cA a
    Tabulate a -> cA a

  cS :: PreOpenSeq index acc aenv' t' -> Actions
  cS = countSeq cA

  in case seq of 
    Producer p seq -> countProd p +^ cS seq
    Consumer c     -> countCons c
    Reify _ a      -> cA a

-----------------------------------------------------------------------------------------
-- Some usefull functions, to get the difference between regular and irregular functions
-- streamIn(Reg) and fromSeq should introduce the least overhead compared to all the other functions when vectorizing.
-- Thus that's the reason I chose for this.
-- There does seem to be a bug in streamIn, thus when you actually run it, you get wrong resutls 
reg, irreg, reg2, irreg2 :: (Shape sh, Elt e, Prelude.Num e) => (S.Acc (Vector e) -> S.Acc (Array sh e)) -> S.Acc (Vector sh, Vector e)
reg f = collect . fromSeq . mapSeq f . streamInReg sh $ xs
  where
    xs = [fromList sh [0,1] | x <-[0,1] ]
    sh = Z :. 2
irreg f = collect . fromSeq . mapSeq f . streamIn $ xs
  where
    xs = [fromList (Z :. 2) [0,1] | x <-[0,1] ]

-- There seems to be a bug in streamIn and streamInReg, so for completeness I added another version, to actually run programs
reg2 f = collect . fromSeq . mapSeq f . subarrays (index1 2) $ xs
  where
    xs = fromList (Z :. 4) $ Prelude.map fromInteger [0..]
reg2 f = collect . fromSeq . mapSeq f . subarrays (index1 2) $ xs
  where
    xs = fromList (Z :. 4) $ Prelude.map fromInteger [0..]
irreg2 f = collect . fromSeq . mapSeq f . fromShapes shapes $ xs
  where
    shapes = use $ fromList (Z :. 2) [Z :. 2, Z :. 2]
    xs = use $ fromList (Z :. 4) $ Prelude.map fromInteger [0..]

countF :: forall e sh. (Shape sh, Elt e, Prelude.Num e) => (S.Acc (Vector e) -> S.Acc (Array sh e)) -> IO ()
countF f = let 
               myidd = id :: (S.Acc (Vector e) -> S.Acc (Vector e))
               n = countDAOpenFun . convertAfun $ f
               regbase = countDOpenA . convertAcc $ (reg myidd)
               nreg = (countDOpenA . convertAcc $ (reg f)) 
               irregbase = countDOpenA . convertAcc $ (irreg myidd)
               nirreg = (countDOpenA . convertAcc $ (irreg f))
  in do putStrLn ("Normal: " ++ show n)
        putStrLn ("Regular: " ++ show nreg)
        putStrLn ("Regular - base: " ++ show (nreg - regbase))
        putStrLn ("Irregular: " ++ show nirreg)
        putStrLn ("Irregular - base: " ++ show (nirreg - irregbase))

countFReg ::  forall e sh. (Shape sh, Elt e, Prelude.Num e) => (S.Acc (Vector e) -> S.Acc (Array sh e)) -> IO ()
countFReg f = let
                myidd = id :: (S.Acc (Vector e) -> S.Acc (Vector e))
                regbase = countDOpenA . convertAcc $ (reg myidd)
                nreg = (countDOpenA . convertAcc $ (reg f)) 
  in do putStrLn ("Regular: " ++ show nreg)
        putStrLn ("Regular - base: " ++ show (nreg - regbase))