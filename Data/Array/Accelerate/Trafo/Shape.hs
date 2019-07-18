{-# LANGUAGE GADTs                #-}
{-# LANGUAGE RankNTypes           #-}
{-# LANGUAGE ScopedTypeVariables  #-}
--{-# LANGUAGE StandaloneDeriving   #-}
{-# LANGUAGE FlexibleContexts     #-}
{-# LANGUAGE TypeFamilies         #-}
{-# LANGUAGE TypeOperators        #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE AllowAmbiguousTypes  #-}
--{-# LANGUAGE ExplicitForAll       #-}
--{-# LANGUAGE TemplateHaskell      #-}

-- |
-- Module      : Data.Array.Accelerate.Trafo.Shape
-- Copyright   : [2019] Lars van den Haak
-- License     : BSD3
--
-- Maintainer  : Lars van den Haak <l.b.vandenhaak@gmail.com>
-- Stability   : experimental
-- Portability : non-portable (GHC extensions)
--

module Data.Array.Accelerate.Trafo.Shape (
  -- * Analysis if array expression is only dependent on shape
  IndAcc, indOpenAcc,
  shAcc,

) where

-- friends
import           Data.Array.Accelerate.Array.Sugar
import           Data.Array.Accelerate.AST
import           Data.Array.Accelerate.Product

-----------------------------------------------------------------
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
                                  (_, True)  -> ind
                                  (_, False) -> notInd
    ShapeSize sh              -> indE sh
    Intersect sh1 sh2         -> indE sh1 &&& indE sh2
    Union sh1 sh2             -> indE sh1 &&& indE sh2

type family ShapeRepr a :: *
type instance ShapeRepr ()           = ()
type instance ShapeRepr (Array sh e) = sh
type instance ShapeRepr (a, b)       = (ShapeRepr a, ShapeRepr b)
type instance ShapeRepr (a, b, c)    = (ShapeRepr a, ShapeRepr b, ShapeRepr c)
type instance ShapeRepr (a, b, c, d) = (ShapeRepr a, ShapeRepr b, ShapeRepr c, ShapeRepr d)
type instance ShapeRepr (a, b, c, d, e) = (ShapeRepr a, ShapeRepr b, ShapeRepr c, ShapeRepr d, ShapeRepr e)
type instance ShapeRepr (a, b, c, d, e, f) = (ShapeRepr a, ShapeRepr b, ShapeRepr c, ShapeRepr d, ShapeRepr e, ShapeRepr f)
type instance ShapeRepr (a, b, c, d, e, f, g) = (ShapeRepr a, ShapeRepr b, ShapeRepr c, ShapeRepr d, ShapeRepr e, ShapeRepr f, ShapeRepr g)
type instance ShapeRepr (a, b, c, d, e, f, g, h) = (ShapeRepr a, ShapeRepr b, ShapeRepr c, ShapeRepr d, ShapeRepr e, ShapeRepr f, ShapeRepr g, ShapeRepr h)
type instance ShapeRepr (a, b, c, d, e, f, g, h, i) = (ShapeRepr a, ShapeRepr b, ShapeRepr c, ShapeRepr d, ShapeRepr e, ShapeRepr f, ShapeRepr g, ShapeRepr h, ShapeRepr i)
type instance ShapeRepr (a, b, c, d, e, f, g, h, i, j) = (ShapeRepr a, ShapeRepr b, ShapeRepr c, ShapeRepr d, ShapeRepr e, ShapeRepr f, ShapeRepr g, ShapeRepr h, ShapeRepr i, ShapeRepr j)
type instance ShapeRepr (a, b, c, d, e, f, g, h, i, j, k) = (ShapeRepr a, ShapeRepr b, ShapeRepr c, ShapeRepr d, ShapeRepr e, ShapeRepr f, ShapeRepr g, ShapeRepr h, ShapeRepr i, ShapeRepr j, ShapeRepr k)
type instance ShapeRepr (a, b, c, d, e, f, g, h, i, j, k, l) = (ShapeRepr a, ShapeRepr b, ShapeRepr c, ShapeRepr d, ShapeRepr e, ShapeRepr f, ShapeRepr g, ShapeRepr h, ShapeRepr i, ShapeRepr j, ShapeRepr k, ShapeRepr l)
type instance ShapeRepr (a, b, c, d, e, f, g, h, i, j, k, l, m) = (ShapeRepr a, ShapeRepr b, ShapeRepr c, ShapeRepr d, ShapeRepr e, ShapeRepr f, ShapeRepr g, ShapeRepr h, ShapeRepr i, ShapeRepr j, ShapeRepr k, ShapeRepr l, ShapeRepr m)
type instance ShapeRepr (a, b, c, d, e, f, g, h, i, j, k, l, m, n) = (ShapeRepr a, ShapeRepr b, ShapeRepr c, ShapeRepr d, ShapeRepr e, ShapeRepr f, ShapeRepr g, ShapeRepr h, ShapeRepr i, ShapeRepr j, ShapeRepr k, ShapeRepr l, ShapeRepr m, ShapeRepr n)
type instance ShapeRepr (a, b, c, d, e, f, g, h, i, j, k, l, m, n, o) = (ShapeRepr a, ShapeRepr b, ShapeRepr c, ShapeRepr d, ShapeRepr e, ShapeRepr f, ShapeRepr g, ShapeRepr h, ShapeRepr i, ShapeRepr j, ShapeRepr k, ShapeRepr l, ShapeRepr m, ShapeRepr n, ShapeRepr o)


data ShapeType acc aenv a where
  ShapeVar :: Arrays arrs => ShapeEnv acc aenv shenv -> Idx shenv arrs -> ShapeType acc aenv arrs
  ShapeExpr :: Shape sh => {-e proxy type ->-} ShapeEnv acc aenv shenv -> PreExp acc shenv sh -> ShapeType acc aenv (Array sh e)

  Scalar :: {-e proxy type -> -} ShapeType acc aenv (Array Z e)
  Folded :: Shape sh => ShapeType acc aenv (Array (sh :.Int) e) -> ShapeType acc aenv (Array sh e)
  Zipped :: {- e proxy type -> -} ShapeType acc aenv (Array sh e1) -> ShapeType acc aenv (Array sh e2) -> ShapeType acc aenv (Array sh e3)
  Scanned :: ShapeType acc aenv (Array sh e) -> ShapeType acc aenv (Array sh e)

  Replicated :: (Shape sh, Shape sl, Slice slix) => ShapeEnv acc aenv shenv
             -> PreExp acc shenv slix -> ShapeType acc aenv (Array sl e) -> ShapeType acc aenv (Array sh e)
  Sliced :: (Shape sh, Shape sl, Slice slix) => ShapeEnv acc aenv shenv
         -> PreExp acc shenv slix -> ShapeType acc aenv (Array sl e) -> ShapeType acc aenv (Array sh e)

  Tup :: ShapeTypeTup acc aenv (TupleRepr arrs) -> ShapeType acc aenv arrs
  TupIdx :: (Arrays arrs, IsAtuple arrs, Arrays a) =>
          TupleIdx (TupleRepr arrs) a -> ShapeType acc aenv arrs -> ShapeType acc aenv a

  Undecidable :: {- e -> proxy type -}ShapeType acc aenv a
  Retype :: ShapeType acc aenv (Array sh e) -> ShapeType acc aenv (Array sh e')

data ShapeTypeTup acc aenv sh where
  STTupNil :: ShapeTypeTup acc aenv ()
  STTupCons :: ShapeTypeTup acc aenv sht -> ShapeType acc aenv sh -> ShapeTypeTup acc aenv (sht, sh)

data ShapeEnv acc aenv shenv where
  SEEmpty :: ShapeEnv acc aenv aenv
  SEPush  :: ShapeEnv acc aenv shenv -> ShapeType acc aenv s -> ShapeEnv acc aenv (shenv, s)

lookUp :: Arrays arrs => Idx shenv arrs -> ShapeEnv acc aenv shenv -> Maybe (ShapeType acc aenv arrs)
lookUp _ SEEmpty                     = Nothing
lookUp ZeroIdx (SEPush _ t)          = Just t
lookUp (SuccIdx idx) (SEPush env' _) = lookUp idx env'

equalShape :: ShapeType acc aenv sh -> ShapeType acc aenv sh -> Bool
equalShape st1@(ShapeVar env1 idx1) st2@(ShapeVar env2 idx2) =
  case (lookUp idx1 env1, lookUp idx2 env2) of
    (Nothing, Nothing)   -> idxToInt idx1 == idxToInt idx2
    (Just st1, Just st2) -> equalShape st1 st2
    (Just st1, Nothing)  -> equalShape st1 st2
    (Nothing, Just st2)  -> equalShape st1 st2
equalShape (ShapeVar env1 idx1) st2 =
  case lookUp idx1 env1 of
    Nothing  -> False
    Just st1 -> equalShape st1 st2

  {-
  ShapeVar :: Arrays arrs => ShapeEnv acc aenv shenv -> Idx shenv arrs -> ShapeType acc aenv arrs
  ShapeExpr :: Shape sh => {-e proxy type ->-} ShapeEnv acc aenv shenv -> PreExp acc shenv sh -> ShapeType acc aenv (Array sh e)

  Scalar :: {-e proxy type -> -} ShapeType acc aenv (Array Z e)
  Folded :: Shape sh => ShapeType acc aenv (Array (sh :.Int) e) -> ShapeType acc aenv (Array sh e)
  Zipped :: {- e proxy type -> -} ShapeType acc aenv (Array sh a) -> ShapeType acc aenv (Array sh b) -> ShapeType acc aenv (Array sh e)

  Replicated :: (Shape sh, Shape sl, Slice slix) => ShapeEnv acc aenv shenv
             -> PreExp acc shenv slix -> ShapeType acc aenv (Array sl e) -> ShapeType acc aenv (Array sh e)
  Sliced :: (Shape sh, Shape sl, Slice slix) => ShapeEnv acc aenv shenv
         -> PreExp acc shenv slix -> ShapeType acc aenv (Array sl e) -> ShapeType acc aenv (Array sh e)

  Tup :: ShapeTypeTup acc aenv (TupleRepr arrs) -> ShapeType acc aenv arrs
  TupIdx :: (Arrays arrs, IsAtuple arrs, Arrays a) =>
          TupleIdx (TupleRepr arrs) a -> ShapeType acc aenv arrs -> ShapeType acc aenv a

  Undecidable :: {- e -> proxy type -}ShapeType acc aenv a
  -}
-------------------------------------------------------------
type ShAcc acc = forall aenv shenv t . ShapeEnv acc aenv shenv -> acc shenv t -> ShapeType acc aenv t

shAcc :: Arrays t => Acc t -> ShapeType OpenAcc () (t)
shAcc a = shOpenAcc SEEmpty a

shOpenAcc :: ShapeEnv OpenAcc aenv shenv -> OpenAcc shenv t -> ShapeType OpenAcc aenv (t)
shOpenAcc shenv (OpenAcc pacc) = shaperAcc shOpenAcc shenv pacc

-- Maybe change last argument, to be a shapetype or whatever.
shAF1 :: ShAcc acc -> ShapeEnv acc aenv shenv -> PreOpenAfun acc shenv (arrs1 -> arrs2) -> acc shenv arrs1 -> ShapeType acc aenv arrs2
shAF1 shA shenv (Alam (Abody f)) a = let newenv = SEPush shenv (shA shenv a) in shA newenv f
shAF1 _ _ _ _ = error "error when applying shAF1"

shaperAcc :: forall acc aenv shenv t. ShAcc acc -> ShapeEnv acc aenv shenv -> PreOpenAcc acc shenv t -> ShapeType acc aenv t
shaperAcc shA' shenv acc =
  let
    shA :: acc shenv t' -> ShapeType acc aenv t'
    shA = shA' shenv

    shE :: Shape sh => PreExp acc shenv sh -> ShapeType acc aenv (Array sh e)
    shE e = ShapeExpr shenv e

    shT :: forall t. Atuple (acc shenv) t -> ShapeTypeTup acc aenv t
    shT NilAtup        = STTupNil
    shT (SnocAtup t a) = STTupCons (shT t) (shA a)
    
    getTup :: ShapeTypeTup acc aenv tarrs -> TupleIdx tarrs a -> ShapeType acc aenv a
    getTup (STTupCons _ sha) ZeroTupIdx = sha
    getTup (STTupCons shtup _) (SuccTupIdx tup) = getTup shtup tup
    getTup STTupNil _ = error "Tupple index is to high for the tupple"

    scan' :: Shape sh => acc shenv (Array (sh :. Int) e) -> ShapeType acc aenv (Array (sh :. Int) e, Array sh e )
    scan' a = case shA a of
                  Undecidable -> Undecidable
                  sha         -> Tup $ STTupCons
                                  (STTupCons STTupNil sha)
                                  (Folded sha)

    {-
    notUn :: acc aenv' t' -> (ShapeType acc aenv t -> ShapeType acc aenv t) -> ShapeType acc aenv t
    notUn a f = case shA a of
                  Undecidable -> Undecidable
                  sha         -> f sha
-}
  in
  case acc of
    Alet a b            -> let newenv = SEPush shenv (shA a) in shA' newenv b
    Avar idx            -> ShapeVar shenv idx
    Atuple tup          -> Tup (shT tup)
    Aprj tidx a         | Tup t <- shA a
                        -> getTup t tidx
                        | otherwise -> TupIdx tidx (shA a)
    Apply f a           -> shAF1 shA' shenv f a
    --Aforeign thing can alter the shape really undecidable.
    Aforeign _ _ _      -> Undecidable
    --Have to think about this, if it eventually points to the same acond, it's still fine right?
    Acond _ t e         -> let sht = shA t
                               she = shA e
                           in if equalShape sht she then sht else Undecidable
    Awhile _ it i       -> let shi = shA i
                               --itEnv = SEPush shenv shi
                               shIt = shAF1 shA' shenv it i
                           in  if equalShape shi shIt then shi else Undecidable
    Unit _              -> Scalar
    Reshape e _         -> shE e
    Generate e _        -> shE e
    Transform sh _ _ _  -> shE sh
    Replicate _ slix a  -> case shA a of
                            Undecidable -> Undecidable
                            sha         -> Replicated shenv slix sha
    Slice _ a slix      -> case shA a of
                            Undecidable -> Undecidable
                            sha         -> Sliced shenv slix sha
    Map _ a             -> Retype $ shA a
    ZipWith _ a1 a2     -> Zipped (shA a1) (shA a2)
    Fold _ _ a          -> case shA a of
                            Undecidable -> Undecidable
                            sha         -> Folded sha
    Fold1 _ a           -> case shA a of
                            Undecidable -> Undecidable
                            sha         -> Folded sha
    FoldSeg _ _ _ _     -> Undecidable
    Fold1Seg _ _ _      -> Undecidable
    Scanl _ _ a         -> case shA a of
                            Undecidable -> Undecidable
                            sha         -> Scanned sha
    Scanl' _ _ a        -> scan' a
    Scanl1 _ a          -> shA a
    Scanr _ _ a         -> case shA a of
                            Undecidable -> Undecidable
                            sha         -> Scanned sha
    Scanr' _ _ a        -> scan' a
    Scanr1 _ a          -> shA a
    Permute _ a _ _     -> shA a
    Backpermute e _ _   -> shE e
    Stencil _ _ a       -> Retype $ shA a
    Stencil2 _ _ a _ b  -> Zipped (shA a) (shA b)
    
    --TODO:: Realy not sure about these yet
    Use _               -> Undecidable
    Subarray _ _ _      -> Undecidable
    Collect _ _ _ _     -> Undecidable

    --Collect _ _ _ _     -> undefined
    --_ -> undefined
    {-
    Avar idx            -> ShapeVar (idxToInt idx)
    Atuple tup          -> Tup (shTup tup)
    Aprj tidx a         | Tup t <- shA a
                        -> getTup t tidx
                        | otherwise -> TupIdx tidx (shA a)
    Aforeign _ _ _      -> Undecidable
    Acond _ t e         -> let sht = shA t
                               she = shA e
                           in if equalShape sht she then sht else Undecidable
    Awhile p it i       -> let shi = shA i
                               itEnv = addToEnv shenv shi
                               shIt = shPreOpenAfun shA' itEnv it
                           in  if equalShape shi shIt then shi else Undecidable

    Unit e              -> Scalar
    Reshape e a         -> shE e
    Generate e f        -> shE e
    Transform sh f f' a -> shE sh
    --Subarray {}         -> undefined
    Replicate _ slix a  -> case shA a of
                            Undecidable -> Undecidable
                            sha         -> Replicated slix sha
    Slice _ a slix      -> case shA a of
                            Undecidable -> Undecidable
                            sha         -> Sliced slix sha
    Map f a             -> shA a
    ZipWith f a1 a2     -> Zipped (shA a1) (shA a2)
    Fold _ _ a          -> case shA a of
                            Undecidable -> Undecidable
                            sha         -> Folded sha
    Fold1 _ a           -> case shA a of
                            Undecidable -> Undecidable
                            sha         -> Folded sha
    FoldSeg _ _ _ _     -> Undecidable
    Fold1Seg _ _ _      -> Undecidable
    Scanl f z a         -> case shA a of
                            Undecidable -> Undecidable
                            sha         -> Scanned sha
    Scanl' f z a        -> scan' a
    Scanl1 f a          -> shA a
    Scanr f z a         -> case shA a of
                            Undecidable -> Undecidable
                            sha         -> Scanned sha
    Scanr' f z a        -> scan' a
    Scanr1 f a          -> shA a
    Permute _ a _ _     -> shA a
    Backpermute e _ _   -> shE e
    Stencil _ _ a       -> shA a
    Stencil2 _ _ a1 _ a2
                        -> Zipped (shA a1) (shA a2)
    --Collect _ _ _ _     -> undefined
    _ -> error "Wrong construct in shape analysis (probably Collect or Subarray)."
    -}

{-
shaperExp :: forall acc env aenv e sh. ShAcc acc -> ShapeEnv -> PreOpenExp acc env aenv e -> ShapeType acc aenv sh
shaperExp shA shenv expr =
  let x = expr

  in case expr of
    Shape a -> shA shenv a
    _       -> ShapeExpr expr
    -}
