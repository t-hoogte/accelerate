{-# LANGUAGE GADTs                #-}
{-# LANGUAGE RankNTypes           #-}
{-# LANGUAGE ScopedTypeVariables  #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE TypeApplications     #-}
{-# LANGUAGE TypeFamilies         #-}
{-# LANGUAGE TypeOperators        #-}
-- |
-- Module      : Data.Array.Accelerate.Trafo.Desugar
-- Copyright   : [2012..2020] The Accelerate Team
-- License     : BSD3
--
-- Maintainer  : Trevor L. McDonell <trevor.mcdonell@gmail.com>
-- Stability   : experimental
-- Portability : non-portable (GHC extensions)
--

module Data.Array.Accelerate.Trafo.Desugar
  where

import qualified Data.Array.Accelerate.AST as Named
import Data.Array.Accelerate.AST.Environment          hiding ( Val )
import Data.Array.Accelerate.AST.Idx
import Data.Array.Accelerate.AST.Operation
import Data.Array.Accelerate.AST.LeftHandSide
import Data.Array.Accelerate.Analysis.Match           ((:~:)(..))
import Data.Array.Accelerate.Representation.Array
import Data.Array.Accelerate.Representation.Shape
import Data.Array.Accelerate.Representation.Slice
import Data.Array.Accelerate.Representation.Stencil
import Data.Array.Accelerate.Representation.Tag
import Data.Array.Accelerate.Representation.Type
import Data.Array.Accelerate.Representation.Vec
import Data.Array.Accelerate.Sugar.Foreign
import Data.Array.Accelerate.Trafo.Exp.Substitution
import Data.Array.Accelerate.Trafo.Operation.Substitution
import Data.Array.Accelerate.Trafo.Var
import Data.Array.Accelerate.Type
import Data.Array.Accelerate.Error
import Data.Primitive.Vec
import Data.Kind
import GHC.Stack

type a $ b = a b
infixr 0 $

-- | Vanilla boundary condition specification for stencil operations
-- Note that this data type is not used in the actual AST, it is just
-- used to pass to 'mkStencil' or 'mkStencil2'.
--
data Boundary env t where
  -- Clamp coordinates to the extent of the array
  Clamp     :: Boundary env t

  -- Mirror coordinates beyond the array extent
  Mirror    :: Boundary env t

  -- Wrap coordinates around on each dimension
  Wrap      :: Boundary env t

  -- Use a constant value for outlying coordinates
  Constant  :: e
            -> Boundary env (Array sh e)

  -- Apply the given function to outlying coordinates
  Function  :: Fun env (sh -> e)
            -> Boundary env (Array sh e)


class DesugarAcc (op :: Type -> Type) where
  mkMap         :: Arg env (Fun' (s -> t))
                -> Arg env (In sh s)
                -> Arg env (Out sh t)
                -> OperationAcc op env ()
  mkMap f input output = mkTransform (ArgFun $ identity $ shapeType shr) f input output
    where
      ArrayR shr _ = argArrayR input

  mkBackpermute :: Arg env (Fun' (sh' -> sh))
                -> Arg env (In sh t)
                -> Arg env (Out sh' t)
                -> OperationAcc op env ()
  mkBackpermute f input output = mkTransform f (ArgFun $ identity tp) input output
    where
      ArrayR _ tp = argArrayR input

  mkTransform   :: Arg env (Fun' (sh' -> sh))
                -> Arg env (Fun' (s -> t))
                -> Arg env (In sh s)
                -> Arg env (Out sh' t)
                -> OperationAcc op env ()
  mkTransform (ArgFun f) (ArgFun g) (ArgArray _ repr sh buffers) output = mkGenerate (ArgFun h) output
    where
      h = g `compose` indexFunction repr sh buffers `compose` f

  mkGenerate    :: Arg env (Fun' (sh -> t))
                -> Arg env (Out sh t)
                -> OperationAcc op env ()

  mkPermute     :: Arg env (Fun' (e -> e -> e))
                -> Arg env (Mut sh' e)
                -> Arg env (Fun' (sh -> sh'))
                -> Arg env (In sh e)
                -> OperationAcc op env ()

  mkStencil     :: StencilR sh e stencil
                -> Arg env (Fun' (stencil -> e'))
                -> Boundary env (Array sh e)
                -> Arg env (In sh e)
                -> Arg env (Out sh e')
                -> OperationAcc op env ()
  -- Default implementation for mkStencil uses 'generate'. It includes the conditional code for the boundary on all elements, making it less efficient
  -- than a specialized implementation.
  --
  mkStencil sr (ArgFun f) boundary input output@(ArgArray _ (ArrayR _ tp) _ _)
    = mkGenerate (ArgFun $ desugarStencilFun sr tp f (Just boundary) input) output

  mkStencil2    :: StencilR sh a stencil1
                -> StencilR sh b stencil2
                -> Arg env (Fun' (stencil1 -> stencil2 -> c))
                -> Boundary env (Array sh a)
                -> Arg env (In sh a)
                -> Boundary env (Array sh b)
                -> Arg env (In sh b)
                -> Arg env (Out sh c)
                -> OperationAcc op env ()
  -- Default implementation for mkStencil uses 'generate'. It includes the conditional code for the boundary on all elements, making it less efficient
  -- than a specialized implementation.
  -- XXX: Could we define this in terms of mkStencil and a zip? Maybe only if the sizes of the two input arrays are equal?
  --
  mkStencil2 sr1 sr2 (ArgFun f) boundary1 input1 boundary2 input2 output@(ArgArray _ (ArrayR _ tp) _ _)
    = mkGenerate (ArgFun $ desugarStencil2Fun sr1 sr2 tp f (Just boundary1) input1 (Just boundary2) input2) output

  mkFold        :: Arg env (Fun' (e -> e -> e))
                -> Arg env (Maybe (Exp' e))
                -> Arg env (In  (sh, Int) e)
                -> Arg env (Out sh        e)
                -> OperationAcc op env ()
  -- TODO: Default implementation in terms of generate & awhile, or a sequential one in terms of generate
  -- Altough it may not be that efficient, it will make it easier to implement new backends

  mkFoldSeg     :: IntegralType i
                -> Arg env (Fun' (e -> e -> e))
                -> Arg env (Maybe (Exp' e))
                -> Arg env (In  (sh, Int) e)
                -> Arg env (In  DIM1      i)
                -> Arg env (Out (sh, Int) e)
                -> OperationAcc op env ()

  mkScan        :: Arg env (Fun' (e -> e -> e))
                -> Arg env (Maybe (Exp' e))
                -> Arg env (In  (sh, Int) e)
                -> Arg env (Out (sh, Int) e)
                -> OperationAcc op env ()
  -- TODO: Default implementation with awhile & generate

  mkScan'       :: Arg env (Fun' (e -> e -> e))
                -> Arg env (Maybe (Exp' e))
                -> Arg env (In  (sh, Int) e)
                -> Arg env (Out (sh, Int) e)
                -> Arg env (Out sh        e)
                -> OperationAcc op env ()
  -- TODO: Default implementation with awhile & generate

  mkForeign     :: Foreign asm
                => ArraysR bs
                -> asm (as -> bs)
                -> GroundVars env (DesugaredArrays as)
                -> Maybe (OperationAcc op env (DesugaredArrays bs))
  mkForeign _ _ _ = Nothing

type family DesugaredArrays a where
  DesugaredArrays ()           = ()
  DesugaredArrays (a, b)       = (DesugaredArrays a, DesugaredArrays b)
  DesugaredArrays (Array sh e) = (sh, Buffers e)

type family DesugaredAfun a where
  DesugaredAfun (a -> b) = DesugaredArrays a -> DesugaredAfun b
  DesugaredAfun a        = DesugaredArrays a

desugar :: (HasCallStack, DesugarAcc op) => Named.Acc a -> OperationAcc op () (DesugaredArrays a)
desugar = desugarOpenAcc Empty

desugarAfun :: (HasCallStack, DesugarAcc op) => Named.Afun a -> OperationAfun op () (DesugaredAfun a)
desugarAfun = desugarOpenAfun Empty

data ArrayDescriptor env a where
  ArrayDescriptor :: GroundVars env sh
                  -> GroundVars env (Buffers e)
                  -> ArrayDescriptor env (Array sh e)

weakenArrayDescriptor :: (env :> env') -> ArrayDescriptor env a -> ArrayDescriptor env' a
weakenArrayDescriptor k (ArrayDescriptor sh buffers) = ArrayDescriptor (weakenVars k sh) (weakenVars k buffers)

type BEnv benv = Env (ArrayDescriptor benv)

desugarOpenAcc :: forall op benv aenv a.
                  (HasCallStack, DesugarAcc op)
               => BEnv benv aenv
               -> Named.OpenAcc aenv a
               -> OperationAcc op benv (DesugaredArrays a)
desugarOpenAcc env = travA
  where
    travA :: Named.OpenAcc aenv arr -> OperationAcc op benv (DesugaredArrays arr)
    travA (Named.OpenAcc acc) = case acc of
      Named.Alet lhs bnd a
        | DesugaredLHS env' lhs' <- desugarLHS env lhs -> alet lhs' (travA bnd) (desugarOpenAcc env' a)
      Named.Avar (Var _ ix)
        | ArrayDescriptor sh bf <- prj' ix env -> Return (TupRpair sh bf)
      Named.Apair a b -> pair (travA a) (travA b)
      Named.Anil       -> Return TupRunit
      Named.Apply repr f arg -> case f of
        Named.Alam lhs (Named.Abody a) -> travA $ Named.OpenAcc $ Named.Alet lhs arg a
        Named.Abody a                  -> arraysRFunctionImpossible $ Named.arraysR a
        Named.Alam _ Named.Alam{}      -> arraysRFunctionImpossible repr


desugarOpenAfun :: (HasCallStack, DesugarAcc op)
                => BEnv benv aenv
                -> Named.OpenAfun aenv a
                -> OperationAfun op benv (DesugaredAfun a)
desugarOpenAfun env (Named.Abody a) = case Named.arraysR a of
  -- We must pattern match on the arrays representation of the body
  -- to inform the type checker that 'a' is not a function, and thus
  -- that 'DesugaredAfun a' is equal to 'DesugaredArrays a'
  TupRsingle ArrayR{} -> Abody $ desugarOpenAcc env a
  TupRunit            -> Abody $ desugarOpenAcc env a
  TupRpair _ _        -> Abody $ desugarOpenAcc env a
desugarOpenAfun env (Named.Alam lhs f)
  | DesugaredLHS env' lhs' <- desugarLHS env lhs = Alam lhs' $ desugarOpenAfun env' f

data DesugaredLHS b aenv' benv where
  DesugaredLHS :: BEnv benv' aenv' -> GLeftHandSide b benv benv' -> DesugaredLHS b aenv' benv

desugarLHS :: BEnv benv aenv -> Named.ALeftHandSide a aenv aenv' -> DesugaredLHS (DesugaredArrays a) aenv' benv
desugarLHS env (LeftHandSideWildcard repr)      = DesugaredLHS env $ LeftHandSideWildcard $ desugarArraysR repr
desugarLHS env (LeftHandSidePair l1 l2)
  | DesugaredLHS env1 l1' <- desugarLHS env  l1
  , DesugaredLHS env2 l2' <- desugarLHS env1 l2 = DesugaredLHS env2 $ LeftHandSidePair l1' l2'
desugarLHS env (LeftHandSideSingle (ArrayR shr tp))
  | DeclareVars lhsSh kSh valueSh <- declareVars $ mapTupR GroundRscalar $ shapeType shr
  , DeclareVars lhsBf kBf valueBf <- declareVars $ buffersR tp
  = DesugaredLHS (mapEnv (weakenArrayDescriptor $ kBf .> kSh) env `Push` ArrayDescriptor (valueSh kBf) (valueBf weakenId)) $ LeftHandSidePair lhsSh lhsBf

desugarArraysR :: ArraysR arr -> GroundsR (DesugaredArrays arr)
desugarArraysR TupRunit          = TupRunit
desugarArraysR (TupRsingle repr) = desugarArrayR repr
desugarArraysR (TupRpair r1 r2)  = desugarArraysR r1 `TupRpair` desugarArraysR r2

desugarArrayR :: ArrayR arr -> GroundsR (DesugaredArrays arr)
desugarArrayR (ArrayR shr tp) = mapTupR GroundRscalar (shapeType shr) `TupRpair` buffersR tp

buffersR :: forall e. TypeR e -> GroundsR (Buffers e)
buffersR TupRunit           = TupRunit
buffersR (TupRsingle tp)
  | Refl <- reprIsSingle @ScalarType @e @Buffer tp = TupRsingle (GroundRbuffer tp)
buffersR (TupRpair t1 t2)   = buffersR t1 `TupRpair` buffersR t2


desugarExp :: HasCallStack
           => BEnv benv aenv
           -> Named.OpenExp env aenv e
           -> OpenExp env benv e
desugarExp env = rebuildArrayInstr (desugarArrayInstr env)

desugarFun :: HasCallStack
           => BEnv benv aenv
           -> Named.Fun aenv e
           -> Fun benv e
desugarFun env = rebuildArrayInstr (desugarArrayInstr env)

desugarArrayInstr :: BEnv benv aenv -> Named.ArrayInstr aenv (s -> t) -> OpenExp env benv s -> OpenExp env benv t
desugarArrayInstr env (Named.Shape (Var (ArrayR shr _) array)) _
  | ArrayDescriptor sh _ <- prj' array env = paramsIn (shapeType shr) sh
desugarArrayInstr env (Named.LinearIndex (Var (ArrayR _ tp) array)) ix
  = Let lhs ix $ linearIndex tp buffers $ Var int ZeroIdx
  where
    ArrayDescriptor _ buffers = prj' array env
    int = SingleScalarType $ NumSingleType $ IntegralNumType TypeInt
    lhs = LeftHandSideSingle int
desugarArrayInstr env (Named.Index (Var (ArrayR shr tp) array)) ix
  = Let lhs (ToIndex shr sh' ix) $ linearIndex tp buffers $ Var int ZeroIdx
  where
    ArrayDescriptor sh buffers = prj' array env
    sh' = paramsIn (shapeType shr) sh
    int = SingleScalarType $ NumSingleType $ IntegralNumType TypeInt
    lhs = LeftHandSideSingle int

weakenBEnv :: forall benv benv' aenv. benv :> benv' -> BEnv benv aenv -> BEnv benv' aenv
weakenBEnv k = mapEnv f
  where
    f :: ArrayDescriptor benv a -> ArrayDescriptor benv' a
    f (ArrayDescriptor sh buffers) = ArrayDescriptor (weakenVars k sh) (weakenVars k buffers)

-- Utilities
--

index :: ArrayR (Array sh e) -> GroundVars benv sh -> GroundVars benv (Buffers e) -> OpenExp env benv sh -> OpenExp env benv e
index (ArrayR shr tp) sh buffers ix = Let lhs (ToIndex shr (paramsIn (shapeType shr) sh) ix) $ linearIndex tp buffers $ Var int ZeroIdx
  where
    int = SingleScalarType $ NumSingleType $ IntegralNumType TypeInt
    lhs = LeftHandSideSingle int

indexFunction :: ArrayR (Array sh e) -> GroundVars benv sh -> GroundVars benv (Buffers e) -> OpenFun env benv (sh -> e)
indexFunction repr@(ArrayR shr _) sh buffers
  | DeclareVars lhs _ value <- declareVars $ shapeType shr
    = Lam lhs $ Body $ index repr sh buffers (expVars $ value weakenId)

linearIndex :: forall e benv env. HasCallStack => TypeR e -> GroundVars benv (Buffers e) -> ExpVar env Int -> OpenExp env benv e
linearIndex TupRunit         TupRunit         _   = Nil
linearIndex (TupRpair t1 t2) (TupRpair b1 b2) ix  = linearIndex t1 b1 ix `Pair` linearIndex t2 b2 ix
linearIndex (TupRsingle t)   (TupRsingle var@(Var (GroundRbuffer _) _)) ix
  | Refl <- reprIsSingle @ScalarType @e @Buffer t = ArrayInstr (Index var) (Evar ix)
linearIndex _                _                _   = internalError "Tuple mismatch"

desugarBoundaryToFunction :: forall benv sh e. Boundary benv (Array sh e) -> Arg benv (In sh e) -> Fun benv (sh -> e)
desugarBoundaryToFunction boundary (ArgArray _ repr@(ArrayR shr tp) sh buffers) = case boundary of
  Function f -> f
  Constant e -> Lam (LeftHandSideWildcard $ shapeType shr) $ Body $ mkConstant tp e
  Clamp      -> reindex clamp
  Mirror     -> reindex mirror
  Wrap       -> reindex wrap
  where

    -- Note: the expressions passed as argument may be duplicated in the resulting code.
    -- This doesn't explode the code size as they are always an Evar or a Parameter.
    --
    clamp, mirror, wrap :: OpenExp env benv Int -> OpenExp env benv Int -> OpenExp env benv Int
    -- clamp ix sz = max(0, min(ix, sz - 1))
    clamp ix sz = mkBinary (PrimMax singleType) (Const scalarTypeInt 0) $ mkBinary (PrimMin singleType) ix $ sub sz $ Const scalarTypeInt 0

    -- if ix < 0 then -ix
    mirror ix sz = Cond (mkBinary (PrimLt singleType) ix (Const scalarTypeInt 0)) (PrimApp (PrimNeg numType) ix)
                 -- else if ix >= sz then sz - ((ix - sz) + 2)
                 $ Cond (mkBinary (PrimGtEq singleType) ix sz) (sub sz (add (sub ix sz) $ Const scalarTypeInt 2))
                 -- else ix
                 $ ix

    -- if ix < 0 then sz + ix
    wrap ix sz = Cond (mkBinary (PrimLt singleType) ix (Const scalarTypeInt 0)) (add sz ix)
                 -- else if ix >= sz then ix - sz
                 $ Cond (mkBinary (PrimGtEq singleType) ix sz) (sub ix sz)
                 -- else ix
                 $ ix

    add = mkBinary (PrimAdd numType)
    sub = mkBinary (PrimSub numType)

    reindex :: (forall env'. OpenExp env' benv Int -> OpenExp env' benv Int -> OpenExp env' benv Int) -> Fun benv (sh -> e)
    reindex f
      | DeclareVars lhs _ value <- declareVars $ shapeType shr
        = Lam lhs $ Body $ index repr sh buffers $ getIndex f shr (value weakenId) sh

    getIndex :: (OpenExp env benv Int -> OpenExp env benv Int -> OpenExp env benv Int) -> ShapeR sh' -> ExpVars env sh' -> GroundVars benv sh' -> OpenExp env benv sh'
    getIndex _ ShapeRz           _                              _                              = Nil
    getIndex f (ShapeRsnoc shr') (TupRpair ixs (TupRsingle ix)) (TupRpair szs (TupRsingle sz)) = getIndex f shr' ixs szs `Pair` f (Evar ix) (paramIn scalarTypeInt sz)
    getIndex _ _                 _                              _                              = internalError "Illegal tuple for shape"

desugarStencilFun :: StencilR sh e stencil -> TypeR e' -> Fun benv (stencil -> e') -> Maybe (Boundary benv (Array sh e)) -> Arg benv (In sh e) -> Fun benv (sh -> e')
desugarStencilFun sr _ f boundary array = f `compose` stencilAccess sr boundary array

desugarStencil2Fun :: StencilR sh a stencil1 -> StencilR sh b stencil2 -> TypeR c -> Fun benv (stencil1 -> stencil2 -> c) -> Maybe (Boundary benv (Array sh a)) -> Arg benv (In sh a) -> Maybe (Boundary benv (Array sh b)) -> Arg benv (In sh b) -> Fun benv (sh -> c)
desugarStencil2Fun sr1 sr2 tp f boundary1 array1@(ArgArray _ (ArrayR shr _) _ _) boundary2 array2
  | DeclareVars lhs _ value <- declareVars $ shapeType shr
  , vars <- expVars $ value weakenId
    = Lam lhs $ Body $ apply2 tp f (apply1 (stencilR sr1) (stencilAccess sr1 boundary1 array1) vars)
                                   (apply1 (stencilR sr2) (stencilAccess sr2 boundary2 array2) vars)

stencilAccess :: forall sh e stencil benv. StencilR sh e stencil -> Maybe (Boundary benv (Array sh e)) -> Arg benv (In sh e) -> Fun benv (sh -> stencil)
stencilAccess sr boundary array@(ArgArray _ repr@(ArrayR shr tp) sh buffers)
  | DeclareVars lhs _ value <- declareVars $ shapeType shr = Lam lhs $ Body $ stencilAccess' shr sr readFunction (value weakenId)
  where
    readFunction :: env :> env' -> ExpVars env' sh -> OpenExp env' benv e
    readFunction _ = readFunction' . expVars

    readFunction' :: OpenExp env' benv sh -> OpenExp env' benv e
    readFunction' = apply1 tp $ case boundary of
      Just b  -> desugarBoundaryToFunction b array
      Nothing -> indexFunction repr sh buffers

stencilAccess' :: forall env benv sh e stencil. ShapeR sh -> StencilR sh e stencil -> (forall env'. env :> env' -> ExpVars env' sh -> OpenExp env' benv e) -> ExpVars env sh -> OpenExp env benv stencil
stencilAccess' shr sr rf ix = case sr of
  -- Base cases, nothing interesting to do here since we know the lower
  -- dimension is Z.
  --
  StencilRunit3 _ -> Nil `Pair` rf' (-1)
                         `Pair` center
                         `Pair` rf'   1
  StencilRunit5 _ -> Nil `Pair` rf' (-2)
                         `Pair` rf' (-1)
                         `Pair` center
                         `Pair` rf'   1
                         `Pair` rf'   2
  StencilRunit7 _ -> Nil `Pair` rf' (-3)
                         `Pair` rf' (-2)
                         `Pair` rf' (-1)
                         `Pair` center
                         `Pair` rf'   1
                         `Pair` rf'   2
                         `Pair` rf'   3
  StencilRunit9 _ -> Nil `Pair` rf' (-4)
                         `Pair` rf' (-3)
                         `Pair` rf' (-2)
                         `Pair` rf' (-1)
                         `Pair` center
                         `Pair` rf'   1
                         `Pair` rf'   2
                         `Pair` rf'   3
                         `Pair` rf'   4

  -- Recursive cases. Note that because the stencil pattern is defined with
  -- a cons ordering, whereas shapes (indices) are defined as a snoc list,
  -- when we recurse on the stencil structure we must manipulate the
  -- _left-most_ index component
  --
  StencilRtup3 s1 s2 s3 ->
    Nil `Pair` go s1 (-1) 
        `Pair` go s2 0
        `Pair` go s3 1

  StencilRtup5 s1 s2 s3 s4 s5 ->
    Nil `Pair` go s1 (-2) 
        `Pair` go s2 (-1)
        `Pair` go s3 0
        `Pair` go s4 1
        `Pair` go s5 2

  StencilRtup7 s1 s2 s3 s4 s5 s6 s7 ->
    Nil `Pair` go s1 (-3) 
        `Pair` go s2 (-2)
        `Pair` go s3 (-1)
        `Pair` go s4 0
        `Pair` go s5 1
        `Pair` go s6 2
        `Pair` go s7 3

  StencilRtup9 s1 s2 s3 s4 s5 s6 s7 s8 s9 ->
    Nil `Pair` go s1 (-4) 
        `Pair` go s2 (-3)
        `Pair` go s3 (-2)
        `Pair` go s4 (-1)
        `Pair` go s5 0
        `Pair` go s6 1
        `Pair` go s7 2
        `Pair` go s8 3
        `Pair` go s9 4
  where
    center :: sh ~ DIM1 => OpenExp env benv e
    center = rf weakenId ix

    -- read function for 1 dimensional cases
    rf' :: sh ~ DIM1 => Int -> OpenExp env benv e
    rf' d
      | TupRpair _ (TupRsingle i) <- ix = Let (LeftHandSideSingle scalarTypeInt) (mkBinary (PrimAdd numType) (Evar i) $ Const scalarTypeInt d)
                                        $ rf (weakenSucc weakenId) $ TupRpair TupRunit $ TupRsingle $ Var scalarTypeInt ZeroIdx
    rf' _ = internalError "Shape tuple mismatch"

    go :: forall sh' stencil'. sh ~ (sh', Int) => StencilR sh' e stencil' -> Int -> OpenExp env benv stencil'
    go sr' d = stencilAccess' shr' sr' rf'' ix'
      where
        ShapeRsnoc shr' = shr
        (i, ix') = uncons shr' ix

        rf'' :: (env :> env') -> ExpVars env' sh' -> OpenExp env' benv e
        rf'' k ds
          | d == 0 = rf k (cons shr' (weakenE k i) ds)
          | otherwise = Let (LeftHandSideSingle scalarTypeInt) (mkBinary (PrimAdd numType) (Evar $ weakenE k i) $ Const scalarTypeInt d)
                      $ rf (weakenSucc' k) $ cons shr' (Var scalarTypeInt ZeroIdx) $ weakenVars (weakenSucc weakenId) ds

-- Add a _left-most_ dimension to a shape
--
cons :: ShapeR sh -> ExpVar env Int -> ExpVars env sh -> ExpVars env (sh, Int)
cons ShapeRz          ix _                = TupRpair TupRunit $ TupRsingle ix
cons (ShapeRsnoc shr) ix (TupRpair sh sz) = TupRpair (cons shr ix sh) sz
cons _                _  _                = internalError "Illegal shape tuple"


-- Remove the _left-most_ index to a shape, and return the remainder
--
uncons :: ShapeR sh -> ExpVars env (sh, Int) -> (ExpVar env Int, ExpVars env sh)
uncons ShapeRz          (TupRpair _ (TupRsingle v2)) = (v2, TupRunit)
uncons (ShapeRsnoc shr) (TupRpair v1 v3)
  = let (i, v1') = uncons shr v1
    in  (i, TupRpair v1' v3)
uncons _ _ = internalError "Illegal shape tuple"
