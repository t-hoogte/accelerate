{-# LANGUAGE GADTs                #-}
{-# LANGUAGE RankNTypes           #-}
{-# LANGUAGE ScopedTypeVariables  #-}
--{-# LANGUAGE StandaloneDeriving   #-}
{-# LANGUAGE AllowAmbiguousTypes  #-}
{-# LANGUAGE FlexibleContexts     #-}
{-# LANGUAGE TypeFamilies         #-}
{-# LANGUAGE TypeOperators        #-}
{-# LANGUAGE UndecidableInstances #-}
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
import           Control.Monad.State.Lazy
import           Data.Array.Accelerate.Array.Sugar
import           Data.Array.Accelerate.AST
import           Data.Array.Accelerate.Product
import           Data.Typeable
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
{-
type family ShapeRepr (a :: *)
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
-}

data ShapeType acc aenv a where
  ShapeVar :: Arrays arrs => ShapeEnv acc aenv shenv -> Idx shenv arrs -> ShapeType acc aenv arrs
  ShapeExpr :: Shape sh => ShapeEnv acc aenv shenv -> PreExp acc shenv sh -> ShapeType acc aenv (Array sh e)

  Scalar :: ShapeType acc aenv (Array Z e)
  Folded :: Shape sh => ShapeType acc aenv (Array (sh :.Int) e) -> ShapeType acc aenv (Array sh e)
  Zipped :: Shape sh => ShapeType acc aenv (Array sh e1) -> ShapeType acc aenv (Array sh e2) -> ShapeType acc aenv (Array sh e3)
  Scanned :: Shape sh => ShapeType acc aenv (Array (sh :.Int) e) -> ShapeType acc aenv (Array (sh :.Int) e)

  Replicated :: (Shape sh, Shape sl, Slice slix) => ShapeEnv acc aenv shenv
             -> PreExp acc shenv slix -> ShapeType acc aenv (Array sh e) -> ShapeType acc aenv (Array sl e)
  Sliced :: (Shape sh, Shape sl, Slice slix) => ShapeEnv acc aenv shenv
         -> PreExp acc shenv slix -> ShapeType acc aenv (Array sh e) -> ShapeType acc aenv (Array sl e)

  Tup :: (IsProduct Arrays arrs {-, ArrRepr arrs ~ (a,b)-}) => arrs {-proxy type-}
      -> ShapeTypeTup acc aenv (TupleRepr arrs) -> ShapeType acc aenv arrs
  TupIdx :: (Arrays arrs, IsAtuple arrs, Arrays a) => arrs {-proxy type-} ->
          TupleIdx (TupleRepr arrs) a -> ShapeType acc aenv arrs -> ShapeType acc aenv a

  UndecidableVar :: Int -> ShapeType acc aenv a
  Retype :: ShapeType acc aenv (Array sh e) -> ShapeType acc aenv (Array sh e')

data ShapeTypeTup acc aenv a where
  STTupNil :: ShapeTypeTup acc aenv ()
  STTupCons :: ShapeTypeTup acc aenv arrs -> ShapeType acc aenv (a) -> ShapeTypeTup acc aenv (arrs, a)

data ShapeEnv acc aenv shenv where
  SEEmpty :: ShapeEnv acc aenv aenv
  SEPush  :: ShapeEnv acc aenv shenv -> ShapeType acc aenv (s) -> ShapeEnv acc aenv (shenv, s)

lookUp :: Idx shenv a -> ShapeEnv acc aenv shenv -> Maybe (ShapeType acc aenv (a))
lookUp _ SEEmpty                     = Nothing
lookUp ZeroIdx (SEPush _ t)          = Just t
lookUp (SuccIdx idx) (SEPush env' _) = lookUp idx env'

equalShape :: forall a a' acc aenv . ShAcc acc -> ShapeType acc aenv a -> ShapeType acc aenv a' -> VSM Bool
equalShape shA st1 st2 -- | Just Refl <- eqT :: Maybe (sh :~: DIM0) = True
                   | otherwise =
  case (st1, st2) of
    (ShapeVar env1 idx1, ShapeVar env2 idx2) ->
      case (lookUp idx1 env1, lookUp idx2 env2) of
        (Nothing, Nothing)   -> return $ idxToInt idx1 == idxToInt idx2
        (Just st1, Just st2) -> equalShape shA st1 st2
        (Just st1, Nothing)  -> equalShape shA st1 st2
        (Nothing, Just st2)  -> equalShape shA st1 st2
    (ShapeExpr env1 e1, ShapeExpr env2 e2) -> equalE env1 e1 env2 e2

    (Scalar, Scalar) -> return True
    (Folded st1, Folded st2) -> equalShape' st1 st2
    (Zipped st1a st1b, Zipped st2a st2b) ->
      equalShape' st1a st2a &&^ equalShape' st1b st2b
      ||^ equalShape' st1a st2b &&^ equalShape' st1b st2a
    (Scanned st1, Scanned st2) -> equalShape' st1 st2

    (Replicated env1 slix1 st1, Replicated env2 slix2 st2) -> equalSlix env1 slix1 env2 slix2 &&^ equalShape' st1 st2
    (Sliced env1 slix1 st1, Sliced env2 slix2 st2) -> equalSlix env1 slix1 env2 slix2 &&^ equalShape' st1 st2
    (Tup _ sttup1, Tup _ sttup2) -> equalShapeT sttup1 sttup2
    (TupIdx _ tidx1 sta, TupIdx _ tidx2 stb) ->
      case (tryGetTup tidx1 sta, tryGetTup tidx2 stb) of
        (Just st1, Just st2) -> equalShape shA st1 st2
        (Just st1, Nothing)  -> equalShape shA st1 st2
        (Nothing, Just st2)  -> equalShape shA st1 st2
        (Nothing, Nothing)   -> equalShape shA sta stb &&^ return (tupleIdxToInt tidx1 == tupleIdxToInt tidx2)

    (UndecidableVar i1, UndecidableVar i2) -> return $ i1 == i2

    (Retype st1, _) -> equalShape shA st1 st2
    (_, Retype st2) -> equalShape shA st1 st2

    (ShapeVar env1 idx1, _) ->
      case lookUp idx1 env1 of
        Nothing  -> return False
        Just st1 -> equalShape shA st1 st2
    (_, ShapeVar env2 idx2) ->
      case lookUp idx2 env2 of
        Nothing  -> return False
        Just st2 -> equalShape shA st1 st2
    (TupIdx _ tidx1 sta, _) ->
      case tryGetTup tidx1 sta of
        Nothing  -> return False
        Just st1 -> equalShape shA st1 st2
    (_, TupIdx _ tidx2 stb) ->
      case tryGetTup tidx2 stb of
        Nothing  -> return False
        Just st2 -> equalShape shA st1 st2
    (ShapeExpr env1 e1, _) -> do 
      res <- tryGetExprShape shA env1 e1
      case res of
        Nothing -> return False
        Just st1 -> equalShape shA st1 st2
    (_, ShapeExpr env2 e2) -> do 
      res <- tryGetExprShape shA env2 e2
      case res of
        Nothing -> return False
        Just st2 -> equalShape shA st1 st2
    
    --Do all the scalar checks
    --We only check for scalar, folded, zipped, replicated and sliced, since these need to be arrays, so we have shape information
    (Scalar, Folded _) -> eqScalar st1 st2
    (Scalar, Zipped _ _) -> eqScalar st1 st2
    (Scalar, Replicated _ _ _) -> eqScalar st1 st2
    (Scalar, Sliced _ _ _) -> eqScalar st1 st2
    (Folded _,  Zipped _ _) -> eqScalar st1 st2
    (Folded _, Replicated _ _ _) -> eqScalar st1 st2
    (Folded _, Sliced _ _ _) -> eqScalar st1 st2
    --We flip the arguments, so it can check for previous ones in the list
    (Folded _, _) -> equalShape shA st2 st1
    (Zipped _ _, Replicated _ _ _) -> eqScalar st1 st2
    (Zipped _ _, Sliced _ _ _) -> eqScalar st1 st2
    (Zipped _ _, _) -> equalShape shA st2 st1
    (Replicated _ _ _, Sliced _ _ _) -> eqScalar st1 st2
    (Replicated _ _ _, _) -> equalShape shA st2 st1
    (Sliced _ _ _, _) -> equalShape shA st2 st1

    _ -> return False
    
    
  where
    eqScalar :: forall sh sh' e e' aenv. (Shape sh, Shape sh') => ShapeType acc aenv (Array sh e) -> ShapeType acc aenv (Array sh' e') -> VSM Bool
    eqScalar _ _ | Just Refl <- (eqT :: Maybe (sh :~: sh'))
                 , Just Refl <- (eqT :: Maybe (sh :~: DIM0)) = return True
                 | otherwise = return False


    equalE :: forall sh sh' shenv' shenv.  (Shape sh, Shape sh')
           => ShapeEnv acc aenv shenv' -> PreExp acc shenv' sh' -> ShapeEnv acc aenv shenv -> PreExp acc shenv sh -> VSM Bool
    equalE env1 e1 env2 e2 | Just Refl <- (eqT :: Maybe (sh :~: sh'))
                           , Just Refl <- (eqT :: Maybe (sh :~: DIM0)) = return True
                           | Just Refl <- (eqT :: Maybe (sh :~: sh')) = equalE' env1 e1 env2 e2
                           | otherwise = return False
    
    equalE' :: ShapeEnv acc aenv shenv' -> PreExp acc shenv' sh -> ShapeEnv acc aenv shenv -> PreExp acc shenv sh -> VSM Bool
    equalE' = undefined

    equalSlix :: forall shenv shenv' slix slix'. (Slice slix, Slice slix')
              => ShapeEnv acc aenv shenv' -> PreExp acc shenv' slix -> ShapeEnv acc aenv shenv -> PreExp acc shenv slix' -> VSM Bool
    equalSlix env1 slix1 env2 slix2 | Just Refl <- (eqT :: Maybe (slix :~: slix')) = equalE' env1 slix1 env2 slix2 
                                    | otherwise = return False

    equalShape' :: forall sh sh' e e' aenv. (Shape sh, Shape sh') => ShapeType acc aenv (Array sh e) -> ShapeType acc aenv (Array sh' e') -> VSM Bool
    equalShape' st1 st2 | Just Refl <- (eqT :: Maybe (sh :~: sh'))
                        , Just Refl <- (eqT :: Maybe (sh :~: DIM0)) = return True
                        | Just Refl <- (eqT :: Maybe (sh :~: sh')) = equalShape shA st1 st2
                        | otherwise = return False

    equalShapeT :: ShapeTypeTup acc aenv t -> ShapeTypeTup acc aenv t' -> VSM Bool
    equalShapeT STTupNil STTupNil = return True
    equalShapeT (STTupCons tup t) (STTupCons tup' t') = equalShapeT tup tup' &&^ equalShape shA t t'
    equalShapeT _ _ = return False

(&&^) :: VSM Bool -> VSM Bool -> VSM Bool
(&&^) = liftM2 (&&)

(||^) :: VSM Bool -> VSM Bool -> VSM Bool
(||^) = liftM2 (||)

tryGetTup :: TupleIdx (TupleRepr arrs) a -> ShapeType acc aenv arrs -> Maybe (ShapeType acc aenv a)
tryGetTup tidx st = case st of
    ShapeVar env idx  -> tryGetTup tidx =<< lookUp idx env
    Tup _ stup        -> Just $ getTup tidx stup
    TupIdx _ tidx' st -> tryGetTup tidx =<< tryGetTup tidx' st
    _                 -> Nothing
  where
    getTup :: TupleIdx tarrs a -> ShapeTypeTup acc aenv tarrs -> ShapeType acc aenv a
    getTup ZeroTupIdx       (STTupCons _ sha)   = sha
    getTup (SuccTupIdx tup) (STTupCons shtup _) = getTup tup shtup


tryGetExprShape :: ShAcc acc -> ShapeEnv acc aenv shenv -> PreOpenExp acc env shenv sh -> VSM (Maybe (ShapeType acc aenv (Array sh e)))
tryGetExprShape shA env exp = case exp of
  Shape a -> Just . Retype <$> shA env a
  IndexNil -> return $ Just Scalar
  _         -> return Nothing

equalOpenExp
    :: ShapeEnv OpenAcc aenv shenv
    -> ShapeEnv OpenAcc aenv shenv'
    -> OpenExp env shenv s
    -> OpenExp env shenv' s
    -> VSM Bool
equalOpenExp = equalPreOpenExp shOpenAcc

equalPreOpenExp
    :: forall acc env env' aenv shenv shenv' s t.
       ShAcc acc
    -> ShapeEnv acc aenv shenv
    -> ShapeEnv acc aenv shenv'
    -> PreOpenExp acc env shenv s
    -> PreOpenExp acc env' shenv' t
    -> VSM Bool
equalPreOpenExp shA shenv1 shenv2 e1 e2 = 
  let 
    shE :: forall env1 env2 a b. PreOpenExp acc env1 shenv a -> PreOpenExp acc env2 shenv' b -> VSM Bool
    shE = equalPreOpenExp shA shenv1 shenv2
    
    
  in case (e1, e2) of
    (Let x1 e1, Let x2 e2) -> shE x1 x2 &&^ shE e1 e2
    (Var ix1, Var ix2) -> return $ idxToInt ix1 == idxToInt ix2
    --Foreign functions can be randoms or something
    (Foreign _ _ _, Foreign _ _ _) -> return False 
    (Const c1, Const c2) -> return $ c1 == c2

-------------------------------------------------------------
type ShAcc acc = forall aenv shenv t . ShapeEnv acc aenv shenv -> acc shenv t -> VSM (ShapeType acc aenv t)

type VarState = Int
type VSM  = State VarState

getNext :: VSM Int
getNext = state (\st -> let st' = nextState st in (valFromState st,st') )
    where
      valFromState s = s
      nextState s = s + 1

shAcc :: Arrays t => Acc t -> ShapeType OpenAcc () t
shAcc a = evalState (shOpenAcc SEEmpty a) 0

shOpenAcc :: ShapeEnv OpenAcc aenv shenv -> OpenAcc shenv t -> VSM (ShapeType OpenAcc aenv (t))
shOpenAcc shenv (OpenAcc pacc) = shaperAcc shOpenAcc shenv pacc

-- Maybe change last argument, to be a shapetype or whatever.
shAF1 :: ShAcc acc -> ShapeEnv acc aenv shenv -> PreOpenAfun acc shenv (arrs1 -> arrs2) -> ShapeType acc aenv (arrs1) -> VSM (ShapeType acc aenv (arrs2))
shAF1 shA shenv (Alam (Abody f)) sha = do let newenv = SEPush shenv sha
                                          shA newenv f
shAF1 _ _ _ _ = error "error when applying shAF1"

shaperAcc :: forall acc aenv shenv t. ShAcc acc -> ShapeEnv acc aenv shenv -> PreOpenAcc acc shenv t -> VSM (ShapeType acc aenv (t))
shaperAcc shA' shenv acc =
  let
    shA :: acc shenv t' -> VSM (ShapeType acc aenv (t'))
    shA = shA' shenv

    shE :: Shape sh => PreExp acc shenv sh -> VSM (ShapeType acc aenv (Array sh e))
    shE e = do res <- tryGetExprShape shA' shenv e
               case res of
                  Just st -> return st
                  Nothing -> return $ ShapeExpr shenv e

    shT :: forall t. Atuple (acc shenv) t -> VSM (ShapeTypeTup acc aenv t)
    shT NilAtup        = return STTupNil
    shT (SnocAtup t a) = STTupCons <$> (shT t) <*> (shA a)

    proxy' :: acc shenv t' -> t'
    proxy' _ = undefined

    proxy :: t
    proxy = undefined

    scan' :: forall sh e. (Shape sh, Elt e) => acc shenv (Array (sh :. Int) e) -> VSM (ShapeType acc aenv (Array (sh :. Int) e, Array sh e))
    scan' a = do
      sha <- shA a
      return $ Tup (undefined :: (Array (sh :. Int) e, Array sh e)) $ STTupCons (STTupCons STTupNil sha) (Folded sha)

    nextUndecidable :: VSM (ShapeType acc aenv (t))
    nextUndecidable = UndecidableVar <$> getNext
  in
  case acc of
    Alet a b            -> do a' <- shA a
                              let newenv = SEPush shenv a'
                              shA' newenv b
    Avar idx            -> return $ ShapeVar shenv idx
    Atuple tup          -> Tup proxy <$> (shT tup)
    Aprj tidx a         -> TupIdx (proxy' a) tidx <$> shA a
    Apply f a           -> shAF1 shA' shenv f =<< shA a
    --Aforeign thing can alter the shape really undecidable.
    Aforeign _ _ _      -> nextUndecidable
    Acond _ t e         -> do
      sht <- shA t
      she <- shA e
      equals <- equalShape shA' sht she
      if equals then return sht else nextUndecidable
    Awhile _ it i       -> do
      shi <- shA i
      shIter <- shAF1 shA' shenv it shi
      equals <- equalShape shA' shi shIter
      if equals then return shi else nextUndecidable
    Use _               -> nextUndecidable
    Subarray _ _ _      -> nextUndecidable
    Unit _              -> return Scalar
    Reshape e _         -> shE e
    Generate e _        -> shE e
    Transform sh _ _ _  -> shE sh
    Replicate _ slix a  -> Replicated shenv slix <$> shA a
    Slice _ a slix      -> Sliced shenv slix <$> shA a
    Map _ a             -> Retype <$> shA a
    ZipWith _ a1 a2     -> Zipped <$> shA a1 <*> shA a2
    Fold _ _ a          -> Folded <$> shA a
    Fold1 _ a           -> Folded <$> shA a
    FoldSeg _ _ _ _     -> nextUndecidable
    Fold1Seg _ _ _      -> nextUndecidable
    Scanl _ _ a         -> Scanned <$> shA a
    Scanl' _ _ a        -> scan' a
    Scanl1 _ a          -> shA a
    Scanr _ _ a         -> Scanned <$> shA a
    Scanr' _ _ a        -> scan' a
    Scanr1 _ a          -> shA a
    Permute _ a _ _     -> shA a
    Backpermute e _ _   -> shE e
    Stencil _ _ a       -> Retype <$> shA a
    Stencil2 _ _ a _ b  -> Zipped <$> shA a <*> shA b
    Collect _ _ _ _     -> nextUndecidable
