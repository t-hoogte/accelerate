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
  IndAcc, indOpenAcc, indOpenAfun1, Independence(..), IndEnv(..), isInd,
  -- * Functions that get shape information out of an array term
  ShAcc, shAcc, shOpenAcc, shOpenAF1,
  -- * Functions that compare two shapes
  equalShape, equalShapedAcc, equalShapeOpen, equalShapedF1, equalShapedA, 
  ShapeEnv(..), 
) where

-- friends
import           Data.Array.Accelerate.Analysis.Match
import           Data.Array.Accelerate.Array.Representation (SliceIndex(..))
import           Data.Array.Accelerate.Array.Sugar
import           Data.Array.Accelerate.AST
import           Data.Array.Accelerate.Product

import           Control.Monad.State.Lazy
import           Data.Typeable
-----------------------------------------------------------------
data Independence =  NotInd | ShapeInd | TotalInd
  deriving (Eq, Ord, Show)

isInd :: Independence -> Bool
isInd TotalInd = True
isInd _        = False


data IndEnv aenv where
  BaseIE     :: IndEnv aenv
  PushIE     :: IndEnv aenv
  -- Added the proxy type, so we have extra type check safety if we add the right independence value to the environment
             -> t {- proxy -}
             -> Independence
             -> IndEnv (aenv, t)



type IndAcc acc = forall aenv t. IndEnv aenv -> acc aenv t -> Independence

(&&&) :: Independence -> Independence -> Independence
(&&&) = min

(|||) :: Independence -> Independence -> Independence
(|||) = max

-- Pass the right environment to this function.
-- Arrays that avoid vectorization, are totally independent.
-- Arrays that are regular, are shape independent.
-- Irregular Arrays, are totally dependent
-- Of only a base environment gets pushed, we have a problem.
-- Since it will recognize the base as an empty one.
indOpenAcc :: IndEnv aenv -> OpenAcc aenv t -> Independence
indOpenAcc env (OpenAcc pacc) = independentShapeArray indOpenAcc env pacc

indOpenAfun1 :: IndEnv (aenv, a) -> OpenAfun aenv (a -> b) -> Independence
indOpenAfun1 env (Alam (Abody a)) = indOpenAcc env a
indOpenAfun1 _ _ = error "Didn't provide correct function for indOpenAfun1"

indPreOpenAfun1 :: IndAcc acc -> IndEnv (aenv,a) -> PreOpenAfun acc aenv (a -> b) -> Independence
indPreOpenAfun1 indA env (Alam (Abody b)) = indA env b
indPreOpenAfun1 _ _ _ = error "Didn't provide correct function for indPreOpenAfun1"

indPreOpenFun1 :: IndAcc acc -> IndEnv aenv -> IndEnv (env,a) -> PreOpenFun acc env aenv (a -> b) -> Independence
indPreOpenFun1 indA aenv env (Lam (Body b)) = independentShapeExp indA aenv env b
indPreOpenFun1 _ _ _ _ = error "Didn't provide correct function for indPreOpenFun1"

indPreOpenFun2 :: IndAcc acc -> IndEnv aenv -> IndEnv ((env,a),b) -> PreOpenFun acc env aenv (a -> b -> c) -> Independence
indPreOpenFun2 indA aenv env (Lam (Lam (Body b))) = independentShapeExp indA aenv env b
indPreOpenFun2 _ _ _ _ = error "Didn't provide correct function for indPreOpenFun2"

indIx :: forall aenv t .
         IndEnv aenv
      -> Idx aenv t
      -> Independence
indIx BaseIE            _            = TotalInd
indIx (PushIE _ _ ind)  ZeroIdx      = ind
indIx (PushIE env _ _)  (SuccIdx ix) = indIx env ix

independentShapeArray :: forall acc aenv t. IndAcc acc -> IndEnv aenv -> PreOpenAcc acc aenv t -> Independence
--independentShapeArray :: forall acc aenv t. Kit acc => PreOpenAcc acc aenv t -> Independence
independentShapeArray indA' env acc =
  let
    indA :: acc aenv t' -> Independence
    indA = indA' env

    indAF1 :: IndEnv (aenv',a) -> PreOpenAfun acc aenv' (a -> b) -> Independence
    indAF1 = indPreOpenAfun1 indA'

    indF1 :: PreExp acc aenv a -> PreFun acc aenv (a -> b) -> Independence
    indF1 e = indPreOpenFun1 indA' env (pushE e)

    indF1AEl :: acc aenv (Array sh a) -> PreFun acc aenv (a -> b) -> Independence
    indF1AEl a = indPreOpenFun1 indA' env (pushAEl a)

    indF2AEl :: acc aenv (Array sh a) -> acc aenv (Array sh b) -> PreFun acc aenv (a -> b -> c) -> Independence
    indF2AEl a b = indPreOpenFun2 indA' env (pushAEl' (pushAEl a) b)

    indE' :: IndEnv env -> PreOpenExp acc env aenv e' -> Independence
    indE' env' = independentShapeExp indA' env env'

    indE :: PreExp acc aenv e' -> Independence
    indE = indE' BaseIE

    indTup :: Atuple (acc aenv) t' -> Independence
    indTup NilAtup        = TotalInd
    indTup (SnocAtup t a) = indA a &&& indTup t

    pushA' :: IndEnv aenv' -> acc aenv' a -> IndEnv (aenv', a)
    pushA' env' a = PushIE env' undefined (indA' env' a)

    pushE' :: IndEnv env' -> PreOpenExp acc env' aenv a -> IndEnv (env', a)
    pushE' env' a = PushIE env' undefined (indE' env' a)

    pushAEl' :: IndEnv env' -> acc aenv (Array sh a) -> IndEnv (env', a)
    pushAEl' env' a = PushIE env' undefined (indA a)

    pushA :: acc aenv a -> IndEnv (aenv, a)
    pushA = pushA' env

    pushE :: PreExp acc aenv a -> IndEnv ((), a)
    pushE = pushE' BaseIE

    pushAEl :: acc aenv (Array sh a) -> IndEnv (env', a)
    pushAEl = pushAEl' BaseIE

    -- The shape of the array is independent of elements of the array
    shapeInd :: Independence
    shapeInd = ShapeInd

    -- The shape of the array is (probably) dependent of elements of the array
    notInd :: Independence
    notInd = NotInd

    proxyA :: acc aenv a -> a 
    proxyA = undefined

    proxyEl :: acc aenv (Array sh e) -> e
    proxyEl = undefined

    proxySh :: acc aenv (Array sh e) -> sh
    proxySh = undefined
  in
  -- In general we do an analysis that is to strict. If we are not strict enough, we break stuff.
  case acc of
    -- We store the result of the independence test in our environment
    Alet a b            -> indA' (pushA a) b
    Avar ix             -> indIx env ix
    Atuple tup          -> indTup tup
    -- We just check the whole tupple
    Aprj _ a            -> indA a
    -- We store the applicant in the environment
    Apply f a           -> indAF1 (pushA a) f
    -- WARNING: When using a foreign function, we could assume it follows the rules of the fallback implementation.
    -- This could break stuff horribly, so we just are extra safe now.
    -- Aforeign _ f a      -> let env' = PushIE BaseIE (indA a)
    --                        in indAF1 env' f
    Aforeign _ _ _      -> notInd
    -- Only of the choice can be made independent of elements of arrays, we can be sure that shape stays independent
    Acond p t e         -> case indE p of
                             TotalInd -> indA t &&& indA e
                             _         -> notInd
    -- Only if the predicate is totally independent, we are sure to stop at exactly the same time.
    -- This must hold for intiatial thing, but also if it has passed through an arbitrary iteration
    Awhile p it i       -> let indi = indA i
                               env' = PushIE env (proxyA i) indi
                               indboth = indi &&& indAF1 env' it
                               env'' = PushIE env (proxyA i) indboth
                            in case indAF1 env'' p of
                                 TotalInd -> indboth
                                 _        -> notInd
    -- Not really sure about this one. If this occurs in a sequence, is it always the same?
    -- Must be right? Since it is not dependent on anything else.
    Use _               -> TotalInd
    -- The shape is indepedent, but maybe the expression is totally independent
    Unit e              -> indE e -- ||| shapeInd
    -- If the new shape is independent, we force that. Otherwise it simply isn't
    Reshape e a         -> case indE e of
                             TotalInd -> indA a ||| shapeInd 
                             _        -> notInd
    -- If the new shape is independent, we force that (automatically since it is expr func). Otherwise it simply isn't
    Generate e f        -> case indE e of
                             TotalInd -> indF1 e f -- ||| shapeInd
                             _        -> notInd
    Transform sh f f' a -> case indE sh of
                            TotalInd -> (indF1 sh f &&& indF1AEl a f') &&& indA a ||| shapeInd
                            _        -> notInd
    
    -- Shouldn't occur here
    Subarray {}         -> notInd
    -- If the slice is independent, just take over the independence of a
    Replicate _ slix a  -> case indE slix of
                             TotalInd -> indA a
                             _        -> notInd
    Slice _ a slix         -> case indE slix of
                                TotalInd -> indA a
                                _        -> notInd
    -- Doesn't change the shape, if an input was totally indepent and so is function f, we end up totally independent.
    -- It will not cover the case when a map will fill everthing with constant values
    Map f a             -> indA a &&& indF1AEl a f
    ZipWith f a1 a2     -> indA a1 &&& indA a2 &&& indF2AEl a1 a2 f 
    --The shape is independent, only if the input array was and the same for the resulting elements
    --Folding to a scalar, will always give an indepedent shape, we do not check for that now
    Fold f z a          -> indA a &&& indF2AEl a a f  &&& indE z
    Fold1 f a           -> indA a &&& indF2AEl a a f 
    -- If the segs aren't totaly independent, we have a dependent shape
    FoldSeg f z a segs  -> case indA segs of
                             TotalInd -> indA a &&& indF2AEl a a f  &&& indE z
                             _        -> notInd
    Fold1Seg f a segs   -> case indA segs of
                             TotalInd -> indA a &&& indF2AEl a a f
                             _        -> notInd
    Scanl f z a         -> indA a &&& indF2AEl a a f &&& indE z
    --Scanning to a scalar, will always give an indepedent shape, for the second index of the tupple.
    --We do not check for that
    Scanl' f z a        -> indA a &&& indF2AEl a a f &&& indE z
    Scanl1 f a          -> indA a &&& indF2AEl a a f
    Scanr f z a         -> indA a &&& indF2AEl a a f &&& indE z
    Scanr' f z a        -> indA a &&& indF2AEl a a f &&& indE z
    Scanr1 f a          -> indA a &&& indF2AEl a a f
    -- So this one is difficult. The default array and source array are both used in the
    -- combine function. So we combine the results. The shape function, can only really tell
    -- things if the source array was atleast shape independent. The case split is not neccesairy
    -- since we combine results anyway, but it is for clarity for myself
    -- 
    Permute f d p a     -> let indd = indA d
                               inda = indA a
                               indboth = indd &&& inda
                               env' = PushIE (PushIE BaseIE (proxyEl a) indboth) (proxyEl a) indboth
                               indf = indPreOpenFun2 indA' env env' f
                               indp = case inda of
                                        NotInd -> notInd
                                        _      -> indPreOpenFun1 indA' env (PushIE BaseIE (proxySh a) inda) p
                           in indboth &&& indf &&& indp
    Backpermute sh f a   -> case indE sh of
                              NotInd -> notInd
                              _      -> shapeInd ||| (indF1 sh f &&& indA a)
    -- The shape will be indepedent, (not the elements), aslong as the input array's shape is independent.
    -- This could be improved, if the elements are also independent, then only the combination function
    -- and boundary need to be checked on independence. We don't bother atm.
    Stencil _ _ a       -> shapeInd &&& indA a
    Stencil2 _ _ a1 _ a2
                        -> shapeInd &&& indA a1 &&& indA a2
    --We only call this when sequencing, thus this means a sequence in a sequence, which isn't possible.
    Collect _ _ _ _     -> notInd

-- We check if the expression is based on constant numbers or the shape of an array (and the array itself hasn't changed it's shape in an unpreditable manner)
-- Most importantly, if array elements are accessed, it will never be independent.
independentShapeExp :: forall acc env aenv e. IndAcc acc -> IndEnv aenv -> IndEnv env -> PreOpenExp acc env aenv e -> Independence
independentShapeExp indA' aenv env expr =
  let
    indA :: acc aenv a -> Independence
    indA = indA' aenv

    indE :: PreOpenExp acc env aenv e' -> Independence
    indE = indE' env

    indE' :: IndEnv env' -> PreOpenExp acc env' aenv e' -> Independence
    indE' env' = independentShapeExp indA' aenv env'

    indTup :: Tuple (PreOpenExp acc env aenv) t -> Independence
    indTup NilTup        = ind
    indTup (SnocTup t e) = indE e &&& indTup t

    indF1 :: PreOpenExp acc env aenv a -> PreOpenFun acc env aenv (a -> b) -> Independence
    indF1 e = indPreOpenFun1 indA' aenv (pushE e)

    pushE :: PreOpenExp acc env aenv a -> IndEnv (env, a)
    pushE = pushE' env

    pushE' :: IndEnv env' -> PreOpenExp acc env' aenv a -> IndEnv (env', a)
    pushE' env' a = PushIE env' undefined (indE' env' a)

    -- The expression is only dependent on shape or constants (independent of the elements of the array)
    ind :: Independence
    ind = TotalInd

    -- The expression is (probably) dependent on the elements of the array, but the shape is always shape independent
    shInd :: Independence
    shInd = ShapeInd

  in
  case expr of
    -- _ ->  shInd
    Let bnd body              -> indE' (pushE bnd) body
    Var ix                    -> indIx env ix ||| shInd
    -- We cannot guarantee that foreign isn't a random function or something
    Foreign _ _ _             -> shInd
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
    While p f x               -> indF1 x p &&& indF1 x f &&& indE x
    PrimConst _               -> ind
    PrimApp _ x               -> indE x
    -- We are indexing arrays. We will always stay shape independent. But maybe if the array is totally indepedent we can go to a totally dependent value
    Index a ix                -> (indA a &&& indE ix) ||| shInd
    LinearIndex a ix          -> (indA a &&& indE ix) ||| shInd
    --This step is very important. It means we can go from only a shape dependent array, to a totally dependent value.
    Shape a                   -> case indA a of
                                  NotInd -> shInd
                                  _  -> ind
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

instance Show (ShapeType acc aenv a) where
  show x = case x of
    ShapeVar env i -> case lookUp i env of
      Nothing -> "ShapeVar " ++ show (idxToInt i)
      Just st -> "ShapeVar -> (" ++ show st ++ ")"
    ShapeExpr _ _ -> "ShapeExpr"
    Scalar -> "Scalar"
    Folded st -> "Folded (" ++ show st ++ ")"
    Zipped st1 st2 -> "Zipped (" ++ show st1 ++ ", " ++ show st2 ++ ")"
    Scanned st -> "Scanned (" ++ show st ++ ")"
    Replicated _ _  st -> "Replicated (" ++ show st ++ ")"
    Sliced _ _ st -> "Sliced (" ++ show st ++ ")" 
    Tup _ stup -> "Tup " ++ show stup
    TupIdx _ idx st  -> "TupIdx " ++ show (tupleIdxToInt idx) ++ " (" ++ show st ++ ")" 
    UndecidableVar i -> "UndecidableVar " ++ show i
    Retype st -> "Retype (" ++ show st ++ ")"

instance Show (ShapeTypeTup acc aenv a) where
  show STTupNil = "()"
  show (STTupCons stup st) = "(" ++ show stup ++ ", " ++ show st ++ ")"

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

equalShapedAcc :: (Arrays t, Arrays s) => Acc t -> Acc s -> Bool
equalShapedAcc = equalShapedA shOpenAcc

equalShapeOpen :: ShapeType OpenAcc aenv a -> ShapeType OpenAcc aenv a' -> VSM Bool
equalShapeOpen = equalShape shOpenAcc

equalShapedF1 ::  ShAcc acc -> PreOpenAfun acc shenv (arrs1 -> arrs2) -> acc shenv arrs1 -> Bool
equalShapedF1 sha f a = 
  let res = do 
              sta <- sha SEEmpty a
              stfa <- shAF1 sha SEEmpty f sta
              equalShape sha sta stfa
  in runVSM res

equalShapedA :: ShAcc acc -> acc shenv t -> acc shenv s -> Bool
equalShapedA shA a1 a2 =
  let 
     res :: VSM Bool
     res = do 
              st1 <- shA SEEmpty a1
              st2 <- shA SEEmpty a2
              equalShape shA st1 st2
  in runVSM res

equalShape :: forall a a' acc aenv . ShAcc acc -> ShapeType acc aenv a -> ShapeType acc aenv a' -> VSM Bool
equalShape shA st1' st2' = do 
    st1 <- rewriteType st1'
    st2 <- rewriteType st2'
    equalShape' st1 st2
  where
    equalShape' :: ShapeType acc aenv a -> ShapeType acc aenv a' -> VSM Bool
    equalShape' st1 st2 = 
      case (st1, st2) of
        (ShapeVar env1 idx1, ShapeVar env2 idx2) ->
          case (lookUp idx1 env1, lookUp idx2 env2) of
            (Nothing, Nothing)   -> return $ idxToInt idx1 == idxToInt idx2
            (Just st1, Just st2) -> equalShape shA st1 st2
            (Just st1, Nothing)  -> equalShape shA st1 st2
            (Nothing, Just st2)  -> equalShape shA st1 st2
        (ShapeExpr env1 e1, ShapeExpr env2 e2) -> equalE env1 e1 env2 e2
    
        (Scalar, Scalar) -> return True
        (Folded st1, Folded st2) -> equalShape shA st1 st2
        (Zipped st1a st1b, Zipped st2a st2b) ->
          equalShape shA st1a st2a &&^ equalShape shA st1b st2b
          ||^ equalShape shA st1a st2b &&^ equalShape shA st1b st2a
        (Scanned st1, Scanned st2) -> equalShape shA st1 st2
    
        (Replicated env1 slix1 st1, Replicated env2 slix2 st2) -> equalSlix env1 slix1 env2 slix2 &&^ equalShape shA st1 st2
        (Sliced env1 slix1 st1, Sliced env2 slix2 st2) -> equalSlix env1 slix1 env2 slix2 &&^ equalShape shA st1 st2
        (Tup _ sttup1, Tup _ sttup2) -> equalShapeT sttup1 sttup2
        (TupIdx _ tidx1 sta, TupIdx _ tidx2 stb) ->
          case (tryGetTup tidx1 sta, tryGetTup tidx2 stb) of
            (Just st1, Just st2) -> equalShape shA st1 st2
            (Just st1, Nothing)  -> equalShape shA st1 st2
            (Nothing, Just st2)  -> equalShape shA st1 st2
            (Nothing, Nothing)   -> equalShape shA sta stb &&^ return (tupleIdxToInt tidx1 == tupleIdxToInt tidx2)
    
        (UndecidableVar i1, UndecidableVar i2) -> return $ i1 == i2

        -- The retype and zip rules must be applied here, since we cannot rewrite them with the same shape
        (Retype st1, _) -> equalShape shA st1 st2
        (_, Retype st2) -> equalShape shA st1 st2
        (Zipped st1a st1b, _) -> do 
          eq <- equalShape shA st1a st1b
          if eq then equalShape shA st1a st2
            else return False
        (_, Zipped st2a st2b) -> do 
          eq <- equalShape shA st2a st2b
          if eq then equalShape shA st1 st2a
            else return False

        _ -> return False

    rewriteType :: ShapeType acc aenv b -> VSM (ShapeType acc aenv b)
    rewriteType st = case st of
      ShapeVar env idx -> case lookUp idx env of
        Nothing -> return st
        Just st -> rewriteType st
      --Retype st -> rewriteType st
      TupIdx _ tidx stup -> case tryGetTup tidx stup of
        Nothing -> return st
        Just st -> rewriteType st
      ShapeExpr env1 e1 -> do 
          she <- tryGetExprShape shA env1 e1
          case she of
            Nothing -> return st
            Just st -> rewriteType st
      Folded _ -> rewriteScalar st
      Zipped _ _ -> rewriteScalar st
      Replicated _ _ _ -> rewriteScalar st
      Sliced _ _ _ -> rewriteScalar st
      
      _ -> return st
    
    rewriteScalar :: forall sh e . Shape sh => ShapeType acc aenv (Array sh e) -> VSM (ShapeType acc aenv (Array sh e))
    rewriteScalar st | Just Refl <- (eqT :: Maybe (sh :~: DIM0)) = return Scalar
                     | otherwise = return st

    equalE :: forall sh sh' shenv' shenv.  (Shape sh, Shape sh')
           => ShapeEnv acc aenv shenv' -> PreExp acc shenv' sh' -> ShapeEnv acc aenv shenv -> PreExp acc shenv sh -> VSM Bool
    equalE env1 e1 env2 e2 | Just Refl <- (eqT :: Maybe (sh :~: sh'))
                           , Just Refl <- (eqT :: Maybe (sh :~: DIM0)) = return True
                           | Just Refl <- (eqT :: Maybe (sh :~: sh')) = equalE' env1 env2 e1 e2
                           | otherwise = return False

    equalE' :: ShapeEnv acc aenv shenv -> ShapeEnv acc aenv shenv' -> PreExp acc shenv sh -> PreExp acc shenv' sh -> VSM Bool
    equalE' = equalPreOpenExp shA

    equalSlix :: forall shenv shenv' slix slix'. (Slice slix, Slice slix')
              => ShapeEnv acc aenv shenv' -> PreExp acc shenv' slix -> ShapeEnv acc aenv shenv -> PreExp acc shenv slix' -> VSM Bool
    equalSlix env1 slix1 env2 slix2 | Just Refl <- (eqT :: Maybe (slix :~: slix')) = equalE' env1 env2 slix1 slix2
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
  Shape a  -> Just . Retype <$> shA env a
  IndexNil -> return $ Just Scalar
  _        -> return Nothing

equalPreOpenExp
    :: forall acc env aenv shenv shenv' t .
       ShAcc acc
    -> ShapeEnv acc aenv shenv
    -> ShapeEnv acc aenv shenv'
    -> PreOpenExp acc env shenv t
    -> PreOpenExp acc env shenv' t
    -> VSM Bool
equalPreOpenExp shA shenv1 shenv2 e1 e2 =
  let
    eqE :: PreOpenExp acc env1 shenv s -> PreOpenExp acc env1 shenv' s -> VSM Bool
    eqE = equalPreOpenExp shA shenv1 shenv2

    eqE' :: forall e1 e2 env1 . (Elt e1, Elt e2) => PreOpenExp acc env1 shenv e1 -> PreOpenExp acc env1 shenv' e2 -> VSM Bool
    eqE' | Just Refl <- eqT :: Maybe (e1 :~: e2) = eqE
         | otherwise = \_ _ -> return False
    
    eqE'' :: forall e1 e2 env1 s . (Elt e1, Elt e2) => PreOpenExp acc (env1, e1) shenv s -> PreOpenExp acc (env1, e2) shenv' s -> VSM Bool
    eqE'' | Just Refl <- eqT :: Maybe (e1 :~: e2) = eqE
          | otherwise = \_ _ -> return False 

    eqTuple :: Tuple (PreOpenExp acc env1 shenv) s -> Tuple (PreOpenExp acc env1 shenv') s -> VSM Bool
    eqTuple NilTup          NilTup           = return True
    eqTuple (SnocTup t1 e1) (SnocTup t2 e2)  = eqTuple t1 t2 &&^ eqE e1 e2

    eqSlice :: SliceIndex slix s1 co sh1 -> SliceIndex slix' t2 co' sh2 -> Bool
    eqSlice SliceNil SliceNil                 = True
    eqSlice (SliceAll   sl1) (SliceAll   sl2) = eqSlice sl1 sl2
    eqSlice (SliceFixed sl1) (SliceFixed sl2) = eqSlice sl1 sl2
    eqSlice _ _                               = False

    eqF :: PreOpenFun acc env1 shenv s -> PreOpenFun acc env1 shenv' s -> VSM Bool
    eqF (Lam s) (Lam t)   = eqF s t
    eqF (Body s) (Body t) = eqE s t
    eqF _ _               = return False

  in case (e1, e2) of
    (Let x1 e1, Let x2 e2)           -> eqE' x1 x2 &&^ eqE'' e1 e2
    (Var ix1, Var ix2)               -> return $ idxToInt ix1 == idxToInt ix2
    --Foreign functions can be randoms or something
    (Foreign _ _ _, Foreign _ _ _)   -> return False
    (Const c1, Const c2)             -> return $ matchConst (eltType (undefined::t)) c1 c2
    (Tuple t1, Tuple t2)             -> eqTuple t1 t2
    (Prj tidx1 t1, Prj tidx2 t2)     -> eqE' t1 t2 &&^ return (tupleIdxToInt tidx1 == tupleIdxToInt tidx2)
    (IndexNil, IndexNil)             -> return True
    (IndexCons sl1 a1, IndexCons sl2 a2)
                                     -> eqE sl1 sl2 &&^ eqE a1 a2
    (IndexHead sl1, IndexHead sl2)   -> eqE' sl1 sl2
    (IndexTail sl1, IndexTail sl2)   -> eqE' sl1 sl2
    (IndexTrans sl1, IndexTrans sl2) -> eqE sl1 sl2
    (IndexAny, IndexAny)             -> return True
    (IndexSlice sliceIndex1 _ sh1, IndexSlice sliceIndex2 _ sh2)
                                     -> return (eqSlice sliceIndex1 sliceIndex2) &&^ eqE' sh1 sh2
    (IndexFull sliceIndex1 ix1 sl1, IndexFull sliceIndex2 ix2 sl2)
                                     -> return (eqSlice sliceIndex1 sliceIndex2) &&^ eqE' ix1 ix2 &&^ eqE' sl1 sl2
    (ToIndex sh1 i1, ToIndex sh2 i2) -> eqE' sh1 sh2 &&^ eqE' i1 i2
    (FromIndex sh1 i1, FromIndex sh2 i2)
                                     -> eqE sh1 sh2 &&^ eqE i1 i2
    (ToSlice _ sh1 i1, ToSlice _ sh2 i2)
                                     -> eqE sh1 sh2 &&^ eqE i1 i2
    (Cond p1 t1 e1, Cond p2 t2 e2)   -> eqE p1 p2 &&^ eqE t1 t2 &&^ eqE e1 e2
    (While p1 f1 x1, While p2 f2 x2) -> eqF p1 p2 &&^ eqF f1 f2 &&^ eqE x1 x2
    (PrimConst c1, PrimConst c2)     | Just Refl <- matchPrimConst c1 c2
                                     -> return True
    -- In the match library they reorder things, we don't here
    (PrimApp f1 x1, PrimApp f2 x2)   | Just Refl <- matchPrimFun' f1 f2
                                     -> eqE' x1 x2
    -- We cannot assume the same arrays, so we cannot know if indexing gives the same value
    (Index _ _, Index _ _)           ->  return False
    (LinearIndex _ _, LinearIndex _ _)
                                     -> return False
    -- This is the reason we are writing our own equality class, instead of using the match library allready in 
    -- place. The arrays do not need to be the same, but must have the same shape
    (Shape a1, Shape a2)             -> do
      sha1 <- shA shenv1 a1
      sha2 <- shA shenv2 a2
      equalShape shA sha1 sha2
    (ShapeSize sh1, ShapeSize sh2)   -> eqE' sh1 sh2
    (Intersect sha1 shb1, Intersect sha2 shb2)
                                     -> (eqE sha1 sha2 &&^ eqE shb1 shb2) ||^
                                        (eqE sha1 shb2 &&^ eqE shb1 sha2)
    (Union sha1 shb1, Union sha2 shb2)
                                     -> (eqE sha1 sha2 &&^ eqE shb1 shb2) ||^
                                        (eqE sha1 shb2 &&^ eqE shb1 sha2)
    _                                -> return False


-------------------------------------------------------------
type ShAcc acc = forall aenv shenv t . ShapeEnv acc aenv shenv -> acc shenv t -> VSM (ShapeType acc aenv t)

type VarState = Int
type VSM  = State VarState

getNext :: VSM Int
getNext = state (\st -> let st' = nextState st in (valFromState st,st') )
    where
      valFromState s = s
      nextState s = s + 1

runVSM :: VSM a -> a
runVSM x = evalState x 0
    
shAcc :: Arrays t => Acc t -> ShapeType OpenAcc () t
shAcc a = runVSM (shOpenAcc SEEmpty a)

shOpenAcc :: ShapeEnv OpenAcc aenv shenv -> OpenAcc shenv t -> VSM (ShapeType OpenAcc aenv t)
shOpenAcc shenv (OpenAcc pacc) = shaperAcc shOpenAcc shenv pacc

shOpenAF1 :: ShapeEnv OpenAcc aenv shenv -> OpenAfun shenv (arrs1 -> arrs2) -> ShapeType OpenAcc aenv arrs1 -> VSM (ShapeType OpenAcc aenv arrs2)
shOpenAF1 = shAF1 shOpenAcc

shAF1 :: ShAcc acc -> ShapeEnv acc aenv shenv -> PreOpenAfun acc shenv (arrs1 -> arrs2) -> ShapeType acc aenv arrs1 -> VSM (ShapeType acc aenv arrs2)
shAF1 shA shenv (Alam (Abody f)) sha = shA (SEPush shenv sha) f
shAF1 _ _ _ _ = error "error when applying shAF1"

shaperAcc :: forall acc aenv shenv t. ShAcc acc -> ShapeEnv acc aenv shenv -> PreOpenAcc acc shenv t -> VSM (ShapeType acc aenv t)
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

    nextUndecidable :: VSM (ShapeType acc aenv t)
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
