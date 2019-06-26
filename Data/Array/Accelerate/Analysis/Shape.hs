{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE CPP                 #-}
{-# LANGUAGE GADTs               #-}
{-# LANGUAGE PatternGuards       #-}
{-# LANGUAGE RankNTypes          #-}
{-# LANGUAGE RecordWildCards     #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell     #-}
{-# LANGUAGE TypeOperators       #-}
{-# OPTIONS_HADDOCK hide #-}
-- |
-- Module      : Data.Array.Accelerate.Analysis.Shape
-- Copyright   : [2008..2014] Manuel M T Chakravarty, Gabriele Keller
--               [2009..2014] Trevor L. McDonell
-- License     : BSD3
--
-- Maintainer  : Manuel M T Chakravarty <chak@cse.unsw.edu.au>
-- Stability   : experimental
-- Portability : non-portable (GHC extensions)
--

module Data.Array.Accelerate.Analysis.Shape (

  -- * query AST dimensionality
  AccDim, accDim, delayedDim, preAccDim,
  expDim,
  -- * Analysis if array expression is only dependent on shape
  IndAcc, indOpenAcc,

) where

-- friends
import Data.Array.Accelerate.AST
import Data.Array.Accelerate.Type
import Data.Array.Accelerate.Trafo.Base
import Data.Array.Accelerate.Array.Sugar


type AccDim acc  = forall aenv sh e. acc aenv (Array sh e) -> Int

-- |Reify the dimensionality of the result type of an array computation
--
accDim :: AccDim OpenAcc
accDim (OpenAcc acc) = preAccDim accDim acc

delayedDim :: AccDim DelayedOpenAcc
delayedDim (Manifest acc)   = preAccDim delayedDim acc
delayedDim (Delayed sh _ _) = expDim sh


-- |Reify dimensionality of a computation parameterised over a recursive closure
--
preAccDim :: forall acc aenv sh e. AccDim acc -> PreOpenAcc acc aenv (Array sh e) -> Int
preAccDim k pacc =
  case pacc of
    Alet  _ acc          -> k acc
    Avar _               -> case arrays (undefined :: Array sh e) of
                              ArraysRarray -> ndim (eltType (undefined::sh))
#if __GLASGOW_HASKELL__ < 800
                              _            -> error "halt, fiend!"
#endif

    Apply _ _            -> case arrays (undefined :: Array sh e) of
                              ArraysRarray -> ndim (eltType (undefined::sh))
#if __GLASGOW_HASKELL__ < 800
                              _            -> error "umm, hello"
#endif

    Aforeign _ _ _      -> case arrays (undefined :: Array sh e) of
                              ArraysRarray -> ndim (eltType (undefined::sh))
#if __GLASGOW_HASKELL__ < 800
                              _            -> error "I don't even like snails!"
#endif

    Atuple _             -> case arrays (undefined :: Array sh e) of
                              ArraysRarray -> ndim (eltType (undefined::sh))
#if __GLASGOW_HASKELL__ < 800
                              _            -> error "can we keep him?"
#endif

    Aprj _ _             -> case arrays (undefined :: Array sh e) of
                              ArraysRarray -> ndim (eltType (undefined::sh))
#if __GLASGOW_HASKELL__ < 800
                              _            -> error "inconceivable!"
#endif

    Collect _ _ _ _      -> case arrays (undefined :: Array sh e) of
                              ArraysRarray -> ndim (eltType (undefined::sh))
#if __GLASGOW_HASKELL__ < 800
                              _            -> error "ppbbbbbt~"
#endif
--}

    Acond _ acc _        -> k acc
    Awhile _ _ acc       -> k acc
    Use Array{}          -> ndim (eltType (undefined::sh))
    Subarray _ _ _       -> ndim (eltType (undefined::sh))
    Unit _               -> 0
    Generate _ _         -> ndim (eltType (undefined::sh))
    Transform _ _ _ _    -> ndim (eltType (undefined::sh))
    Reshape _ _          -> ndim (eltType (undefined::sh))
    Replicate _ _ _      -> ndim (eltType (undefined::sh))
    Slice _ _ _          -> ndim (eltType (undefined::sh))
    Map _ acc            -> k acc
    ZipWith _ _ acc      -> k acc
    Fold _ _ acc         -> k acc - 1
    Fold1 _ acc          -> k acc - 1
    FoldSeg _ _ acc _    -> k acc
    Fold1Seg _ acc _     -> k acc
    Scanl _ _ acc        -> k acc
    Scanl1 _ acc         -> k acc
    Scanr _ _ acc        -> k acc
    Scanr1 _ acc         -> k acc
    Permute _ acc _ _    -> k acc
    Backpermute _ _ _    -> ndim (eltType (undefined::sh))
    Stencil _ _ acc      -> k acc
    Stencil2 _ _ acc _ _ -> k acc


-- |Reify dimensionality of a scalar expression yielding a shape
--
expDim :: forall acc env aenv sh. Elt sh => PreOpenExp acc env aenv sh -> Int
expDim _ = ndim (eltType (undefined :: sh))


-- Count the number of components to a tuple type
--
ndim :: TupleType a -> Int
ndim UnitTuple       = 0
ndim (SingleTuple _) = 1
ndim (PairTuple a b) = ndim a + ndim b

type IndAcc acc = forall aenv t. acc aenv t -> (Bool, Bool)

(&&&) :: (Bool, Bool) -> (Bool, Bool) -> (Bool, Bool)
(b1, b2) &&& (a1, a2) = (b1 && a1, b2 && a2)

(&|) :: (Bool, Bool) -> (Bool, Bool) -> (Bool, Bool)
(b1, b2) &| (a1, a2) = (b1 && a1, b2 || a2)

indOpenAcc :: OpenAcc aenv t -> (Bool, Bool)
indOpenAcc (OpenAcc pacc) = independentShapeArray indOpenAcc pacc

indPreOpenAfun :: IndAcc acc -> PreOpenAfun acc aenv t -> (Bool, Bool)
indPreOpenAfun indA (Abody b) = indA b
indPreOpenAfun indA (Alam f)  = indPreOpenAfun indA f

indPreOpenFun :: IndAcc acc -> PreOpenFun acc env aenv t -> (Bool, Bool)
indPreOpenFun indA (Body b) = independentShapeExp indA b
indPreOpenFun indA (Lam f)  = indPreOpenFun indA f

independentShapeArray :: forall acc aenv t. IndAcc acc -> PreOpenAcc acc aenv t -> (Bool, Bool)
--independentShapeArray :: forall acc aenv t. Kit acc => PreOpenAcc acc aenv t -> (Bool, Bool)
independentShapeArray indA acc =
  let
    indAF :: PreOpenAfun acc aenv' t' -> (Bool, Bool)
    indAF = indPreOpenAfun indA

    indF :: PreOpenFun acc env aenv' t' -> (Bool, Bool)
    indF = indPreOpenFun indA

    indE :: PreOpenExp acc env' aenv' e' -> (Bool, Bool)
    indE = independentShapeExp indA

    indTup :: Atuple (acc aenv') t' -> (Bool, Bool)
    indTup NilAtup        = notIndShape
    indTup (SnocAtup t a) = indA a &&& indTup t

    -- The shape of the array is independent of elements of the array
    indShape :: (Bool, Bool)
    indShape = (False, True)

    -- The shape of the array is (probably) dependent of elements of the array
    notIndShape :: (Bool, Bool)
    notIndShape = (False, False)
  in
  -- In general we do an analysis that is to strict. If we are not strict enough, we break stuff. 
  case acc of
    -- If the variable we introduce is dependent, we can't assume indepence anymore.
    -- TODO: Maybe we can look in the environment and place the value of the binding there
    Alet a b            -> case indA a of
                            (_, True)  -> indA b
                            (_, False) -> notIndShape
    Avar _              -> indShape
    Atuple tup          -> indTup tup
    Aprj _ a            -> indA a
    Apply f a           -> indAF f &&& indA a
    -- We cannot say if the foreign function changes the shape and if so if that was dependent on the elements of the array
    Aforeign _ _ _      -> notIndShape
    -- Only of the choice can be made independent of elements of arrays, we can be sure that shape stays independent
    Acond p t e         -> case indE p of
                            (True, _) -> indA t &&& indA e
                            _         -> notIndShape
    -- My guess is this. But it's hard to reason about.
    Awhile p it i       -> indAF p &&& indAF it &&& indA i
    Use _               -> indShape
    -- If the expresion is independent, we have an array that is independent
    Unit e              -> indE e
    -- If the new shape is independent, we force that. Otherwise it simply isn't
    Reshape e a         -> case indE e of
                            (True, _) -> (True, True) &| indA a
                            _         -> notIndShape
    -- If the new shape is independent, we force that. Otherwise it simply isn't
    Generate e f        -> case indE e of
                            (True, _) -> (True, True) &| indF f
                            _         -> notIndShape
    Transform sh f f' a -> case indE sh of
                            (True, _) -> (True, True) &| (indF f &&& indF f' &&& indA a)
                            _         -> notIndShape
    -- TODO: I think false?
    Subarray {}         -> notIndShape
    Replicate _ slix a  -> indE slix &&& indA a
    -- False, since you can slice out a Scalar
    Slice _ _ _         -> notIndShape
    -- Doesn't change the shape, if a input was indepent and so is function f, we end up totally independent.
    Map f a             -> indF f &&& indA a
    ZipWith f a1 a2     -> indF f &&& indA a1 &&& indA a2
    --The shape is independent, but the elements (of the scalar) aren't
    Fold _ _ _          -> indShape
    Fold1 _ _           -> indShape
    -- TODO: Not sure about the fold segs, probably if the segs aren't totaly independent, we have a dependent shape
    FoldSeg _ _ _ _     -> notIndShape
    Fold1Seg _ _ _      -> notIndShape
    Scanl f z a         -> indF f &&& indE z &&& indA a 
    Scanl' f z a        -> indF f &&& indE z &&& indA a 
    Scanl1 f a          -> indF f &&& indA a 
    Scanr f z a         -> indF f &&& indE z &&& indA a 
    Scanr' f z a        -> indF f &&& indE z &&& indA a 
    Scanr1 f a          -> indF f &&& indA a
    -- False, since you could permute everything to a scalar
    Permute _ _ _ _     -> notIndShape
    Backpermute _ _ _   -> notIndShape
    -- The shape will be indepedent, (not the elements), aslong as the input array's shape is independent.
    Stencil _ _ a       -> indShape &&& indA a
    Stencil2 _ _ a1 _ a2
                        -> indShape &&& indA a1 &&& indA a2
    --We only call this when sequencing, thus this means a sequence in a sequence, which isn't possible.
    Collect _ _ _ _     -> notIndShape

-- We check if the expression is based on constant numbers or the shape of an array (and the array itself hasn't changed it's shape in an unpreditable manner)
-- Most importantly, if array elements are accessed, it will never be independent.
independentShapeExp :: forall acc env aenv e. IndAcc acc -> PreOpenExp acc env aenv e -> (Bool, Bool)
independentShapeExp indA expr =
  let
    indE :: PreOpenExp acc env' aenv' e' -> (Bool, Bool)
    indE = independentShapeExp indA

    indTup :: Tuple (PreOpenExp acc env' aenv') t -> (Bool, Bool)
    indTup NilTup        = ind
    indTup (SnocTup t e) = indE e &&& indTup t

    indF :: PreOpenFun acc env' aenv' e' -> (Bool, Bool)
    indF = indPreOpenFun indA

    -- The expression is only dependent on shape or constants (independent of the elements of the array)
    ind :: (Bool, Bool)
    ind = (True, True)

    -- The expression is (probably) dependent on the elements of the array
    notInd :: (Bool, Bool)
    notInd = (False, True)

  in
  case expr of
    Let bnd body              -> indE bnd &&& indE body
    Var _                     -> ind
    -- We cannot guarantee that foreign isn't a random function or something
    Foreign _ _ _             -> notInd
    Const _                   -> ind
    Tuple t                   -> indTup t
    -- We cannot go to a specific tuple index for now, so check whole tuple
    -- Also it can be a variable, so no guarantee that we can acces the tuple.
    Prj _ e                   -> indE e
    IndexNil                  -> ind
    IndexCons sh sz           -> indE sh &&& indE sz
    IndexHead sh              -> indE sh
    IndexTail sh              -> indE sh
    IndexAny                  -> ind
    IndexSlice _ _ sh         -> indE sh
    IndexFull _ slix sl       -> indE slix &&& indE sl 
    ToIndex sh ix             -> indE sh &&& indE ix
    FromIndex sh ix           -> indE sh &&& indE ix
    IndexTrans sh             -> indE sh
    ToSlice _ slix i          -> indE slix &&& indE i
    Cond p e1 e2              -> indE p &&& indE e1 &&& indE e2
    While p f x               -> indF p &&& indF f &&& indE x
    PrimConst _               -> ind
    PrimApp _ x               -> indE x
    Index _ _                 -> notInd
    LinearIndex _ _           -> notInd
    Shape a                   -> case indA a of
                                  (_, True) -> ind
                                  (_, False) -> notInd
    ShapeSize sh              -> indE sh
    Intersect sh1 sh2         -> indE sh1 &&& indE sh2
    Union sh1 sh2             -> indE sh1 &&& indE sh2