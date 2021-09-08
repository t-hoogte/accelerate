{-# LANGUAGE BangPatterns        #-}
{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE GADTs               #-}
{-# LANGUAGE MagicHash           #-}
{-# LANGUAGE PatternGuards       #-}
{-# LANGUAGE RankNTypes          #-}
{-# LANGUAGE RecordWildCards     #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications    #-}
{-# LANGUAGE TypeFamilies        #-}
{-# LANGUAGE TypeOperators       #-}
{-# LANGUAGE ViewPatterns        #-}
{-# OPTIONS_GHC -fno-warn-name-shadowing #-}
{-# OPTIONS_HADDOCK prune #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE TupleSections #-}
-- |
-- Module      : Data.Array.Accelerate.Interpreter
-- Description : Reference backend (interpreted)
-- Copyright   : [2008..2020] The Accelerate Team
-- License     : BSD3
--
-- Maintainer  : Trevor L. McDonell <trevor.mcdonell@gmail.com>
-- Stability   : experimental
-- Portability : non-portable (GHC extensions)
--
-- This interpreter is meant to be a reference implementation of the
-- semantics of the embedded array language. The emphasis is on defining
-- the semantics clearly, not on performance.
--

module Data.Array.Accelerate.Interpreter


  where
import Prelude                                                      hiding ( (!!), sum )
import Data.Array.Accelerate.AST.Partitioned hiding (Empty)
import Data.Array.Accelerate.AST.Operation
import Data.Array.Accelerate.Trafo.Desugar
import qualified Data.Array.Accelerate.Debug.Internal as Debug
import Data.Array.Accelerate.Representation.Array
import Data.Array.Accelerate.Error
import Data.Array.Accelerate.Representation.Type
import Data.Array.Accelerate.Representation.Shape
import Data.Array.Accelerate.Representation.Slice
import Data.Array.Accelerate.AST.Environment hiding (Identity(..))
import Data.Array.Accelerate.Type
import Data.Primitive.Vec
import Data.Primitive.Types
import Data.Primitive.ByteArray
import Text.Printf (printf)
import Data.Array.Accelerate.Representation.Elt
import Data.Array.Accelerate.Representation.Vec
import Data.Array.Accelerate.Trafo.Exp.Substitution
import Unsafe.Coerce (unsafeCoerce)
import Control.Monad.ST
import Data.Bits
import Data.Array.Accelerate.Trafo.Partitioning.ILP.Graph (MakesILP (..), Information (Info), Var (BackendSpecific), (-?>), fused, infusibleEdges)
import Data.Array.Accelerate.Trafo.Partitioning.ILP.Labels
import qualified Data.Set as S
import Data.Array.Accelerate.Trafo.Partitioning.ILP.Solver
import Lens.Micro ((.~), (&))
import qualified Data.Array.Accelerate.Sugar.Array as Sugar
import qualified Data.Array.Accelerate.Smart as Smart
import System.IO.Unsafe (unsafePerformIO)
import Data.Array.Accelerate.Trafo (convertAcc)
import Control.DeepSeq (($!!))
import qualified Data.Array.Accelerate.AST.Environment as Env
import Data.Array.Accelerate.Array.Buffer
import Data.Array.Accelerate.AST.Var (varsType)
import Data.Type.Equality

-- Conceptually, this computes the body of the fused loop
-- It only deals with scalar values - wrap it in a loop!
-- transform :: Monad m  -- The interpreter will want to use this with `m ~ Identity`, but other backends might not (e.g. `m ~ CodeGen PTX`)
--           => (forall body. op body -> Args env body -> ToIn body -> m (ToOut body)) -- function to handle primitives, might end up in the typeclass of `op` 
--           -> ClusterAST op i o -- Tree of fused primitives
--           -> i                 -- input
--           -> m o               -- output
-- transform tbody None i = return i
-- transform tbody (Bind lhs op c) i = tbody op (getIn lhs i) >>= transform tbody c . genOut lhs i
evalCluster :: Monad m
            => (forall env body. op body -> FromIn env body -> Val env -> m (FromOut env body))
            -> ClusterIO args i o
            -> ClusterAST op i o
            -> Args env args
            -> Val env
            -> i
            -> m o
evalCluster k ci ca pa env i = _

data InterpretOp args where
  INoop        :: InterpretOp ()
  IMap         :: InterpretOp (Fun' (s -> t) -> In sh s -> Out sh t -> ())
  IBackpermute :: InterpretOp (Fun' (sh' -> sh) -> In sh t -> Out sh' t -> ())
  IGenerate    :: InterpretOp (Fun' (sh -> t) -> Out sh t -> ())
  IPermute     :: InterpretOp (Fun' (e -> e -> e)
                              -> Mut sh' e
                              -> Fun' (sh -> PrimMaybe sh')
                              -> In sh e
                              -> ())

instance DesugarAcc InterpretOp where
  mkMap         a b c   = Exec IMap         (a :>: b :>: c :>:       ArgsNil)
  mkBackpermute a b c   = Exec IBackpermute (a :>: b :>: c :>:       ArgsNil)
  mkGenerate    a b     = Exec IGenerate    (a :>: b :>:             ArgsNil)
  mkPermute     a b c d = Exec IPermute     (a :>: b :>: c :>: d :>: ArgsNil)
  -- etc, but the rest piggybacks off of Generate for now (see Desugar.hs)

-- -2 is left>right, -1 is right>left, n is 'according to computation n' (e.g. Backpermute) 
-- (Note that Labels are uniquely identified by an Int, the parent just gives extra information)
-- Use Output = -3 for 'cannot be fused with consumer', as that is more difficult to express (we don't know the consumer yet)
-- We restrict all the Inputs to (-2, PosInf).
data OrderV = OrderIn  Label
            | OrderOut Label
  deriving (Eq, Ord, Read, Show)

instance MakesILP InterpretOp where
  type BackendVar InterpretOp = OrderV
  -- TODO add folds/scans/stencils, and solve problems: in particular, iteration size needs to be uniform
  mkGraph INoop _ _ = mempty
  mkGraph IBackpermute (_ :>: ((L _ (_, S.toList -> ~[lIn])) :>: _)) l@(Label i _) =
    Info
      mempty
      (  inputDirectionConstraint l lIn
      <> var (OrderIn l) .==. int i) -- enforce that the backpermute follows its own rules
      (inOutBounds l)
  mkGraph IGenerate _ l = Info mempty mempty (lower (-2) (BackendSpecific $ OrderOut l))
  mkGraph IMap (f :>: L _ (_, S.toList -> ~[lIn]) :>: o :>: ArgsNil) l =
    Info
      mempty
      (  inputDirectionConstraint l lIn
      <> var (OrderIn l) .==. var (OrderOut l))
      (inOutBounds l)
  mkGraph IPermute (comb :>: L _ (_, S.toList -> ~[lTarget]) :>: f :>: L _ (_, S.toList -> ~[lIn]) :>: ArgsNil) l =
    Info
      (mempty & infusibleEdges .~ S.singleton (lTarget -?> l)) -- Cannot fuse with the producer of the target array
      (  inputDirectionConstraint l lIn
      <> var (OrderOut l) .==. int (-3)) -- convention meaning infusible
      (lower (-2) (BackendSpecific $ OrderIn l))


-- | If l and lIn are fused, the out-order of lIn and the in-order of l should match
inputDirectionConstraint :: Label -> Label -> Constraint InterpretOp
inputDirectionConstraint l lIn =
                timesN (fused lIn l) .>=. var (OrderIn l) .-. var (OrderOut lIn)
    <> (-1) .*. timesN (fused lIn l) .<=. var (OrderIn l) .-. var (OrderOut lIn)

inOutBounds :: Label -> Bounds InterpretOp
inOutBounds l = lower (-2) (BackendSpecific $ OrderIn l) <> lower (-2) (BackendSpecific $ OrderOut l)

var :: BackendVar InterpretOp -> Expression InterpretOp
var = c . BackendSpecific

instance NFData' InterpretOp where
  rnf' = error "todo"



fromArgs :: Int -> Env.Val env -> Args env args -> FromIn env args
fromArgs i _ ArgsNil = ()
fromArgs i env (ArgVar v :>: args) = (fromArgs i env args, v)
fromArgs i env (ArgExp e :>: args) = (fromArgs i env args, e)
fromArgs i env (ArgFun f :>: args) = (fromArgs i env args, f)
fromArgs i env (ArgArray Mut _ sh buf :>: args) = (fromArgs i env args, ArrayDescriptor sh buf)
fromArgs i env (ArgArray In _ _ buf :>: args) =
  let buf' = varsGetVal buf env
  in (fromArgs i env args, indexBuffers (bufferScalarType $ varsType buf) buf' i)
fromArgs i env (ArgArray Out ar sh buf :>: args) = (fromArgs i env args, varsGetVal sh env)


evalOp :: Int -> InterpretOp args -> Val env -> FromIn env args -> IO (FromOut env args)
evalOp _ INoop _ () = pure ()
evalOp _ IMap env ((_, x), f) = pure ((), evalFun f env x)
evalOp _ IBackpermute _ _ = error "Should be filtered out earlier? Or just treat as id here"
evalOp i IGenerate env (((), sh), f) = pure ((), evalFun f env $ _ i sh)
evalOp i IPermute env (((((), e), f), target), comb) =
  case evalFun f env (_ i) of
    (0, _) -> pure ((), target)
    (1, ((), sh)) -> case target of
      ArrayDescriptor _ (bufvars :: GroundVars env (Buffers e)) -> do
        let j = _ sh
        let buf = varsGetVal bufvars env
        let buf' = veryUnsafeUnfreezeBuffers @e (bufferScalarType $ varsType bufvars) buf
        x <- readBuffers @e (bufferScalarType $ varsType bufvars) buf' j
        let x' = evalFun comb env x e
        writeBuffers (bufferScalarType $ varsType bufvars) buf' j x'
        return ((), target)
    _ -> error "PrimMaybe's tag was non-zero and non-one"

-- TODO fix types, this is ridiculous. @Ivo how `should` such a function work? Is Distribute just an abstraction that hurts more than it helps?
bufferScalarType :: forall e. TupR GroundR (Buffers e) -> TypeR e
bufferScalarType TupRunit 
  | Refl :: e :~: () <- unsafeCoerce Refl 
  = TupRunit 
bufferScalarType (TupRpair tr' tr2) = unsafeCoerce $ TupRpair (bufferScalarType (unsafeCoerce tr')) (bufferScalarType (unsafeCoerce tr2))
bufferScalarType (TupRsingle (GroundRbuffer st)) = unsafeCoerce $ TupRsingle st
bufferScalarType (TupRsingle (GroundRscalar x)) = case x of {} -- all non-buffer

-- Program execution
-- -----------------

-- | Run a complete embedded array program using the reference interpreter.
--
run :: forall a. (HasCallStack, Sugar.Arrays a) => Smart.Acc a -> a
run a = unsafePerformIO execute
  where
    acc :: PartitionedAcc InterpretOp () (DesugaredArrays (Sugar.ArraysR a))
    !acc    = convertAcc a
    execute = do
      Debug.dumpGraph $!! acc
      Debug.dumpSimplStats
      res <- phase "execute" Debug.elapsed $ undefined
      return $ Sugar.toArr $ snd res

-- -- | This is 'runN' specialised to an array program of one argument.
-- --
-- run1 :: (HasCallStack, Sugar.Arrays a, Sugar.Arrays b) => (Smart.Acc a -> Smart.Acc b) -> a -> b
-- run1 = runN

-- -- | Prepare and execute an embedded array program.
-- --
-- runN :: forall f. (HasCallStack, Afunction f) => f -> AfunctionR f
-- runN f = go
--   where
--     !acc    = convertAfun f
--     !afun   = unsafePerformIO $ do
--                 Debug.dumpGraph $!! acc
--                 Debug.dumpSimplStats
--                 return acc
--     !go     = eval (afunctionRepr @f) afun Empty
--     --
--     eval :: AfunctionRepr g (AfunctionR g) (ArraysFunctionR g)
--          -> DelayedOpenAfun aenv (ArraysFunctionR g)
--          -> Val aenv
--          -> AfunctionR g
--     eval (AfunctionReprLam reprF) (Alam lhs f) aenv = \a -> eval reprF f $ aenv `push` (lhs, Sugar.fromArr a)
--     eval AfunctionReprBody        (Abody b)    aenv = unsafePerformIO $ phase "execute" Debug.elapsed (Sugar.toArr . snd <$> evaluate (evalOpenAcc b aenv))
--     eval _                        _aenv        _    = error "Two men say they're Jesus; one of them must be wrong"


-- Debugging
-- ---------

phase :: String -> (Double -> Double -> String) -> IO a -> IO a
phase n fmt = Debug.timed Debug.dump_phases (\wall cpu -> printf "phase %s: %s" n (fmt wall cpu))



-- Array expression evaluation
-- ---------------------------

type WithReprs acc = (ArraysR acc, acc)

fromFunction' :: ArrayR (Array sh e) -> sh -> (sh -> e) -> WithReprs (Array sh e)
fromFunction' repr sh f = (TupRsingle repr, fromFunction repr sh f)



-- Array primitives
-- ----------------

unitOp :: TypeR e -> e -> WithReprs (Scalar e)
unitOp tp e = fromFunction' (ArrayR ShapeRz tp) () (const e)


generateOp
    :: ArrayR (Array sh e)
    -> sh
    -> (sh -> e)
    -> WithReprs (Array sh e)
generateOp = fromFunction'


reshapeOp
    :: HasCallStack
    => ShapeR sh
    -> sh
    -> WithReprs (Array sh' e)
    -> WithReprs (Array sh  e)
reshapeOp newShapeR newShape (TupRsingle (ArrayR shr tp), Array sh adata)
  = boundsCheck "shape mismatch" (size newShapeR newShape == size shr sh)
    ( TupRsingle (ArrayR newShapeR tp)
    , Array newShape adata
    )


replicateOp
    :: SliceIndex slix sl co sh
    -> slix
    -> WithReprs (Array sl e)
    -> WithReprs (Array sh e)
replicateOp slice slix (TupRsingle repr@(ArrayR _ tp), arr)
  = fromFunction' repr' sh (\ix -> (repr, arr) ! pf ix)
  where
    repr' = ArrayR (sliceDomainR slice) tp
    (sh, pf) = extend slice slix (shape arr)

    extend :: SliceIndex slix sl co dim
           -> slix
           -> sl
           -> (dim, dim -> sl)
    extend SliceNil              ()        ()
      = ((), const ())
    extend (SliceAll sliceIdx)   (slx, ()) (sl, sz)
      = let (dim', f') = extend sliceIdx slx sl
        in  ((dim', sz), \(ix, i) -> (f' ix, i))
    extend (SliceFixed sliceIdx) (slx, sz) sl
      = let (dim', f') = extend sliceIdx slx sl
        in  ((dim', sz), \(ix, _) -> f' ix)


sliceOp
    :: SliceIndex slix sl co sh
    -> WithReprs (Array sh e)
    -> slix
    -> WithReprs (Array sl e)
sliceOp slice (TupRsingle repr@(ArrayR _ tp), arr) slix
  = fromFunction' repr' sh' (\ix -> (repr, arr) ! pf ix)
  where
    repr' = ArrayR (sliceShapeR slice) tp
    (sh', pf) = restrict slice slix (shape arr)

    restrict
        :: HasCallStack
        => SliceIndex slix sl co sh
        -> slix
        -> sh
        -> (sl, sl -> sh)
    restrict SliceNil              ()        ()
      = ((), const ())
    restrict (SliceAll sliceIdx)   (slx, ()) (sl, sz)
      = let (sl', f') = restrict sliceIdx slx sl
        in  ((sl', sz), \(ix, i) -> (f' ix, i))
    restrict (SliceFixed sliceIdx) (slx, i)  (sl, sz)
      = let (sl', f') = restrict sliceIdx slx sl
        in  indexCheck i sz $ (sl', \ix -> (f' ix, i))



-- Scalar expression evaluation
-- ----------------------------

-- Evaluate a closed scalar expression
--
evalExp :: HasCallStack => Exp aenv t -> Val aenv -> t
evalExp e aenv = evalOpenExp e Empty aenv

-- Evaluate a closed scalar function
--
evalFun :: HasCallStack => Fun aenv t -> Val aenv -> t
evalFun f aenv = evalOpenFun f Empty aenv

-- Evaluate an open scalar function
--
evalOpenFun :: HasCallStack => OpenFun env aenv t -> Val env -> Val aenv -> t
evalOpenFun (Body e)    env aenv = evalOpenExp e env aenv
evalOpenFun (Lam lhs f) env aenv =
  \x -> evalOpenFun f (env `push` (lhs, x)) aenv


-- Evaluate an open scalar expression
--
-- NB: The implementation of 'Index' and 'Shape' demonstrate clearly why
--     array expressions must be hoisted out of scalar expressions before code
--     execution. If these operations are in the body of a function that gets
--     mapped over an array, the array argument would be evaluated many times
--     leading to a large amount of wasteful recomputation.
--
evalOpenExp
    :: forall env aenv t. HasCallStack
    => OpenExp env aenv t
    -> Val env
    -> Val aenv
    -> t
evalOpenExp pexp env aenv =
  let
      evalE :: OpenExp env aenv t' -> t'
      evalE e = evalOpenExp e env aenv

      evalF :: OpenFun env aenv f' -> f'
      evalF f = evalOpenFun f env aenv

      -- evalA :: ArrayVar aenv a -> WithReprs a
      -- evalA (Var repr ix) = (TupRsingle repr, prj ix aenv)
  in
  case pexp of
    Let lhs exp1 exp2           -> let !v1  = evalE exp1
                                       env' = env `push` (lhs, v1)
                                   in  evalOpenExp exp2 env' aenv
    Evar (Var _ ix)             -> prj ix env
    Const _ c                   -> c
    Undef tp                    -> undefElt (TupRsingle tp)
    PrimConst c                 -> evalPrimConst c
    PrimApp f x                 -> evalPrim f (evalE x)
    Nil                         -> ()
    Pair e1 e2                  -> let !x1 = evalE e1
                                       !x2 = evalE e2
                                   in  (x1, x2)
    VecPack   vecR e            -> pack   vecR $! evalE e
    VecUnpack vecR e            -> unpack vecR $! evalE e
    IndexSlice slice slix sh    -> restrict slice (evalE slix)
                                                  (evalE sh)
      where
        restrict :: SliceIndex slix sl co sh -> slix -> sh -> sl
        restrict SliceNil              ()        ()         = ()
        restrict (SliceAll sliceIdx)   (slx, ()) (sl, sz)   =
          let sl' = restrict sliceIdx slx sl
          in  (sl', sz)
        restrict (SliceFixed sliceIdx) (slx, _i)  (sl, _sz) =
          restrict sliceIdx slx sl

    IndexFull slice slix sh     -> extend slice (evalE slix)
                                                (evalE sh)
      where
        extend :: SliceIndex slix sl co sh -> slix -> sl -> sh
        extend SliceNil              ()        ()       = ()
        extend (SliceAll sliceIdx)   (slx, ()) (sl, sz) =
          let sh' = extend sliceIdx slx sl
          in  (sh', sz)
        extend (SliceFixed sliceIdx) (slx, sz) sl       =
          let sh' = extend sliceIdx slx sl
          in  (sh', sz)

    ToIndex shr sh ix           -> toIndex shr (evalE sh) (evalE ix)
    FromIndex shr sh ix         -> fromIndex shr (evalE sh) (evalE ix)
    Case e rhs def              -> evalE (caseof (evalE e) rhs)
      where
        caseof :: TAG -> [(TAG, OpenExp env aenv t)] -> OpenExp env aenv t
        caseof tag = go
          where
            go ((t,c):cs)
              | tag == t  = c
              | otherwise = go cs
            go []
              | Just d <- def = d
              | otherwise     = internalError "unmatched case"

    Cond c t e
      | toBool (evalE c)        -> evalE t
      | otherwise               -> evalE e

    While cond body seed        -> go (evalE seed)
      where
        f       = evalF body
        p       = evalF cond
        go !x
          | toBool (p x) = go (f x)
          | otherwise    = x

    -- ArrayInstr (Index acc) ix   -> let (TupRsingle repr, a) = evalA acc
    --                                in (repr, a) ! evalE ix
    -- ArrayInstr (LinearIndex acc) i
    --                             -> let (TupRsingle repr, a) = evalA acc
    --                                    ix   = fromIndex (arrayRshape repr) (shape a) (evalE i)
    --                                in (repr, a) ! ix
    -- ArrayInstr (Shape acc) _    -> shape $ snd $ evalA acc
    ShapeSize shr sh            -> size shr (evalE sh)
    Foreign _ _ f e             -> evalOpenFun (rebuildNoArrayInstr f) Empty Empty $ evalE e
    Coerce t1 t2 e              -> evalCoerceScalar t1 t2 (evalE e)


-- Coercions
-- ---------

-- Coercion between two scalar types. We require that the size of the source and
-- destination values are equal (this is not checked at this point).
--
evalCoerceScalar :: ScalarType a -> ScalarType b -> a -> b
evalCoerceScalar SingleScalarType{}    SingleScalarType{} a = unsafeCoerce a
evalCoerceScalar VectorScalarType{}    VectorScalarType{} a = unsafeCoerce a  -- XXX: or just unpack/repack the (Vec ba#)
evalCoerceScalar (SingleScalarType ta) VectorScalarType{} a = vector ta a
  where
    vector :: SingleType a -> a -> Vec n b
    vector (NumSingleType t) = num t

    num :: NumType a -> a -> Vec n b
    num (IntegralNumType t) = integral t
    num (FloatingNumType t) = floating t

    integral :: IntegralType a -> a -> Vec n b
    integral TypeInt{}     = poke
    integral TypeInt8{}    = poke
    integral TypeInt16{}   = poke
    integral TypeInt32{}   = poke
    integral TypeInt64{}   = poke
    integral TypeWord{}    = poke
    integral TypeWord8{}   = poke
    integral TypeWord16{}  = poke
    integral TypeWord32{}  = poke
    integral TypeWord64{}  = poke

    floating :: FloatingType a -> a -> Vec n b
    floating TypeHalf{}    = poke
    floating TypeFloat{}   = poke
    floating TypeDouble{}  = poke

    {-# INLINE poke #-}
    poke :: forall a b n. Prim a => a -> Vec n b
    poke x = runST $ do
      mba <- newByteArray (sizeOf (undefined::a))
      writeByteArray mba 0 x
      ByteArray ba# <- unsafeFreezeByteArray mba
      return $ Vec ba#

evalCoerceScalar VectorScalarType{} (SingleScalarType tb) a = scalar tb a
  where
    scalar :: SingleType b -> Vec n a -> b
    scalar (NumSingleType t) = num t

    num :: NumType b -> Vec n a -> b
    num (IntegralNumType t) = integral t
    num (FloatingNumType t) = floating t

    integral :: IntegralType b -> Vec n a -> b
    integral TypeInt{}     = peek
    integral TypeInt8{}    = peek
    integral TypeInt16{}   = peek
    integral TypeInt32{}   = peek
    integral TypeInt64{}   = peek
    integral TypeWord{}    = peek
    integral TypeWord8{}   = peek
    integral TypeWord16{}  = peek
    integral TypeWord32{}  = peek
    integral TypeWord64{}  = peek

    floating :: FloatingType b -> Vec n a -> b
    floating TypeHalf{}    = peek
    floating TypeFloat{}   = peek
    floating TypeDouble{}  = peek

    {-# INLINE peek #-}
    peek :: Prim a => Vec n b -> a
    peek (Vec ba#) = indexByteArray (ByteArray ba#) 0


-- Scalar primitives
-- -----------------

evalPrimConst :: PrimConst a -> a
evalPrimConst (PrimMinBound ty) = evalMinBound ty
evalPrimConst (PrimMaxBound ty) = evalMaxBound ty
evalPrimConst (PrimPi       ty) = evalPi ty

evalPrim :: PrimFun (a -> r) -> (a -> r)
evalPrim (PrimAdd                ty) = evalAdd ty
evalPrim (PrimSub                ty) = evalSub ty
evalPrim (PrimMul                ty) = evalMul ty
evalPrim (PrimNeg                ty) = evalNeg ty
evalPrim (PrimAbs                ty) = evalAbs ty
evalPrim (PrimSig                ty) = evalSig ty
evalPrim (PrimQuot               ty) = evalQuot ty
evalPrim (PrimRem                ty) = evalRem ty
evalPrim (PrimQuotRem            ty) = evalQuotRem ty
evalPrim (PrimIDiv               ty) = evalIDiv ty
evalPrim (PrimMod                ty) = evalMod ty
evalPrim (PrimDivMod             ty) = evalDivMod ty
evalPrim (PrimBAnd               ty) = evalBAnd ty
evalPrim (PrimBOr                ty) = evalBOr ty
evalPrim (PrimBXor               ty) = evalBXor ty
evalPrim (PrimBNot               ty) = evalBNot ty
evalPrim (PrimBShiftL            ty) = evalBShiftL ty
evalPrim (PrimBShiftR            ty) = evalBShiftR ty
evalPrim (PrimBRotateL           ty) = evalBRotateL ty
evalPrim (PrimBRotateR           ty) = evalBRotateR ty
evalPrim (PrimPopCount           ty) = evalPopCount ty
evalPrim (PrimCountLeadingZeros  ty) = evalCountLeadingZeros ty
evalPrim (PrimCountTrailingZeros ty) = evalCountTrailingZeros ty
evalPrim (PrimFDiv               ty) = evalFDiv ty
evalPrim (PrimRecip              ty) = evalRecip ty
evalPrim (PrimSin                ty) = evalSin ty
evalPrim (PrimCos                ty) = evalCos ty
evalPrim (PrimTan                ty) = evalTan ty
evalPrim (PrimAsin               ty) = evalAsin ty
evalPrim (PrimAcos               ty) = evalAcos ty
evalPrim (PrimAtan               ty) = evalAtan ty
evalPrim (PrimSinh               ty) = evalSinh ty
evalPrim (PrimCosh               ty) = evalCosh ty
evalPrim (PrimTanh               ty) = evalTanh ty
evalPrim (PrimAsinh              ty) = evalAsinh ty
evalPrim (PrimAcosh              ty) = evalAcosh ty
evalPrim (PrimAtanh              ty) = evalAtanh ty
evalPrim (PrimExpFloating        ty) = evalExpFloating ty
evalPrim (PrimSqrt               ty) = evalSqrt ty
evalPrim (PrimLog                ty) = evalLog ty
evalPrim (PrimFPow               ty) = evalFPow ty
evalPrim (PrimLogBase            ty) = evalLogBase ty
evalPrim (PrimTruncate        ta tb) = evalTruncate ta tb
evalPrim (PrimRound           ta tb) = evalRound ta tb
evalPrim (PrimFloor           ta tb) = evalFloor ta tb
evalPrim (PrimCeiling         ta tb) = evalCeiling ta tb
evalPrim (PrimAtan2              ty) = evalAtan2 ty
evalPrim (PrimIsNaN              ty) = evalIsNaN ty
evalPrim (PrimIsInfinite         ty) = evalIsInfinite ty
evalPrim (PrimLt                 ty) = evalLt ty
evalPrim (PrimGt                 ty) = evalGt ty
evalPrim (PrimLtEq               ty) = evalLtEq ty
evalPrim (PrimGtEq               ty) = evalGtEq ty
evalPrim (PrimEq                 ty) = evalEq ty
evalPrim (PrimNEq                ty) = evalNEq ty
evalPrim (PrimMax                ty) = evalMax ty
evalPrim (PrimMin                ty) = evalMin ty
evalPrim PrimLAnd                    = evalLAnd
evalPrim PrimLOr                     = evalLOr
evalPrim PrimLNot                    = evalLNot
evalPrim (PrimFromIntegral ta tb)    = evalFromIntegral ta tb
evalPrim (PrimToFloating ta tb)      = evalToFloating ta tb


-- Implementation of scalar primitives
-- -----------------------------------

toBool :: PrimBool -> Bool
toBool 0 = False
toBool _ = True

fromBool :: Bool -> PrimBool
fromBool False = 0
fromBool True  = 1

evalLAnd :: (PrimBool, PrimBool) -> PrimBool
evalLAnd (x, y) = fromBool (toBool x && toBool y)

evalLOr  :: (PrimBool, PrimBool) -> PrimBool
evalLOr (x, y) = fromBool (toBool x || toBool y)

evalLNot :: PrimBool -> PrimBool
evalLNot = fromBool . not . toBool

evalFromIntegral :: IntegralType a -> NumType b -> a -> b
evalFromIntegral ta (IntegralNumType tb)
  | IntegralDict <- integralDict ta
  , IntegralDict <- integralDict tb
  = fromIntegral

evalFromIntegral ta (FloatingNumType tb)
  | IntegralDict <- integralDict ta
  , FloatingDict <- floatingDict tb
  = fromIntegral

evalToFloating :: NumType a -> FloatingType b -> a -> b
evalToFloating (IntegralNumType ta) tb
  | IntegralDict <- integralDict ta
  , FloatingDict <- floatingDict tb
  = realToFrac

evalToFloating (FloatingNumType ta) tb
  | FloatingDict <- floatingDict ta
  , FloatingDict <- floatingDict tb
  = realToFrac


-- Extract methods from reified dictionaries
--

-- Constant methods of Bounded
--

evalMinBound :: BoundedType a -> a
evalMinBound (IntegralBoundedType ty)
  | IntegralDict <- integralDict ty
  = minBound

evalMaxBound :: BoundedType a -> a
evalMaxBound (IntegralBoundedType ty)
  | IntegralDict <- integralDict ty
  = maxBound

-- Constant method of floating
--

evalPi :: FloatingType a -> a
evalPi ty | FloatingDict <- floatingDict ty = pi

evalSin :: FloatingType a -> (a -> a)
evalSin ty | FloatingDict <- floatingDict ty = sin

evalCos :: FloatingType a -> (a -> a)
evalCos ty | FloatingDict <- floatingDict ty = cos

evalTan :: FloatingType a -> (a -> a)
evalTan ty | FloatingDict <- floatingDict ty = tan

evalAsin :: FloatingType a -> (a -> a)
evalAsin ty | FloatingDict <- floatingDict ty = asin

evalAcos :: FloatingType a -> (a -> a)
evalAcos ty | FloatingDict <- floatingDict ty = acos

evalAtan :: FloatingType a -> (a -> a)
evalAtan ty | FloatingDict <- floatingDict ty = atan

evalSinh :: FloatingType a -> (a -> a)
evalSinh ty | FloatingDict <- floatingDict ty = sinh

evalCosh :: FloatingType a -> (a -> a)
evalCosh ty | FloatingDict <- floatingDict ty = cosh

evalTanh :: FloatingType a -> (a -> a)
evalTanh ty | FloatingDict <- floatingDict ty = tanh

evalAsinh :: FloatingType a -> (a -> a)
evalAsinh ty | FloatingDict <- floatingDict ty = asinh

evalAcosh :: FloatingType a -> (a -> a)
evalAcosh ty | FloatingDict <- floatingDict ty = acosh

evalAtanh :: FloatingType a -> (a -> a)
evalAtanh ty | FloatingDict <- floatingDict ty = atanh

evalExpFloating :: FloatingType a -> (a -> a)
evalExpFloating ty | FloatingDict <- floatingDict ty = exp

evalSqrt :: FloatingType a -> (a -> a)
evalSqrt ty | FloatingDict <- floatingDict ty = sqrt

evalLog :: FloatingType a -> (a -> a)
evalLog ty | FloatingDict <- floatingDict ty = log

evalFPow :: FloatingType a -> ((a, a) -> a)
evalFPow ty | FloatingDict <- floatingDict ty = uncurry (**)

evalLogBase :: FloatingType a -> ((a, a) -> a)
evalLogBase ty | FloatingDict <- floatingDict ty = uncurry logBase

evalTruncate :: FloatingType a -> IntegralType b -> (a -> b)
evalTruncate ta tb
  | FloatingDict <- floatingDict ta
  , IntegralDict <- integralDict tb
  = truncate

evalRound :: FloatingType a -> IntegralType b -> (a -> b)
evalRound ta tb
  | FloatingDict <- floatingDict ta
  , IntegralDict <- integralDict tb
  = round

evalFloor :: FloatingType a -> IntegralType b -> (a -> b)
evalFloor ta tb
  | FloatingDict <- floatingDict ta
  , IntegralDict <- integralDict tb
  = floor

evalCeiling :: FloatingType a -> IntegralType b -> (a -> b)
evalCeiling ta tb
  | FloatingDict <- floatingDict ta
  , IntegralDict <- integralDict tb
  = ceiling

evalAtan2 :: FloatingType a -> ((a, a) -> a)
evalAtan2 ty | FloatingDict <- floatingDict ty = uncurry atan2

evalIsNaN :: FloatingType a -> (a -> PrimBool)
evalIsNaN ty | FloatingDict <- floatingDict ty = fromBool . isNaN

evalIsInfinite :: FloatingType a -> (a -> PrimBool)
evalIsInfinite ty | FloatingDict <- floatingDict ty = fromBool . isInfinite


-- Methods of Num
--

evalAdd :: NumType a -> ((a, a) -> a)
evalAdd (IntegralNumType ty) | IntegralDict <- integralDict ty = uncurry (+)
evalAdd (FloatingNumType ty) | FloatingDict <- floatingDict ty = uncurry (+)

evalSub :: NumType a -> ((a, a) -> a)
evalSub (IntegralNumType ty) | IntegralDict <- integralDict ty = uncurry (-)
evalSub (FloatingNumType ty) | FloatingDict <- floatingDict ty = uncurry (-)

evalMul :: NumType a -> ((a, a) -> a)
evalMul (IntegralNumType ty) | IntegralDict <- integralDict ty = uncurry (*)
evalMul (FloatingNumType ty) | FloatingDict <- floatingDict ty = uncurry (*)

evalNeg :: NumType a -> (a -> a)
evalNeg (IntegralNumType ty) | IntegralDict <- integralDict ty = negate
evalNeg (FloatingNumType ty) | FloatingDict <- floatingDict ty = negate

evalAbs :: NumType a -> (a -> a)
evalAbs (IntegralNumType ty) | IntegralDict <- integralDict ty = abs
evalAbs (FloatingNumType ty) | FloatingDict <- floatingDict ty = abs

evalSig :: NumType a -> (a -> a)
evalSig (IntegralNumType ty) | IntegralDict <- integralDict ty = signum
evalSig (FloatingNumType ty) | FloatingDict <- floatingDict ty = signum

evalQuot :: IntegralType a -> ((a, a) -> a)
evalQuot ty | IntegralDict <- integralDict ty = uncurry quot

evalRem :: IntegralType a -> ((a, a) -> a)
evalRem ty | IntegralDict <- integralDict ty = uncurry rem

evalQuotRem :: IntegralType a -> ((a, a) -> (a, a))
evalQuotRem ty | IntegralDict <- integralDict ty = uncurry quotRem

evalIDiv :: IntegralType a -> ((a, a) -> a)
evalIDiv ty | IntegralDict <- integralDict ty = uncurry div

evalMod :: IntegralType a -> ((a, a) -> a)
evalMod ty | IntegralDict <- integralDict ty = uncurry mod

evalDivMod :: IntegralType a -> ((a, a) -> (a, a))
evalDivMod ty | IntegralDict <- integralDict ty = uncurry divMod

evalBAnd :: IntegralType a -> ((a, a) -> a)
evalBAnd ty | IntegralDict <- integralDict ty = uncurry (.&.)

evalBOr :: IntegralType a -> ((a, a) -> a)
evalBOr ty | IntegralDict <- integralDict ty = uncurry (.|.)

evalBXor :: IntegralType a -> ((a, a) -> a)
evalBXor ty | IntegralDict <- integralDict ty = uncurry xor

evalBNot :: IntegralType a -> (a -> a)
evalBNot ty | IntegralDict <- integralDict ty = complement

evalBShiftL :: IntegralType a -> ((a, Int) -> a)
evalBShiftL ty | IntegralDict <- integralDict ty = uncurry shiftL

evalBShiftR :: IntegralType a -> ((a, Int) -> a)
evalBShiftR ty | IntegralDict <- integralDict ty = uncurry shiftR

evalBRotateL :: IntegralType a -> ((a, Int) -> a)
evalBRotateL ty | IntegralDict <- integralDict ty = uncurry rotateL

evalBRotateR :: IntegralType a -> ((a, Int) -> a)
evalBRotateR ty | IntegralDict <- integralDict ty = uncurry rotateR

evalPopCount :: IntegralType a -> (a -> Int)
evalPopCount ty | IntegralDict <- integralDict ty = popCount

evalCountLeadingZeros :: IntegralType a -> (a -> Int)
evalCountLeadingZeros ty | IntegralDict <- integralDict ty = countLeadingZeros

evalCountTrailingZeros :: IntegralType a -> (a -> Int)
evalCountTrailingZeros ty | IntegralDict <- integralDict ty = countTrailingZeros

evalFDiv :: FloatingType a -> ((a, a) -> a)
evalFDiv ty | FloatingDict <- floatingDict ty = uncurry (/)

evalRecip :: FloatingType a -> (a -> a)
evalRecip ty | FloatingDict <- floatingDict ty = recip


evalLt :: SingleType a -> ((a, a) -> PrimBool)
evalLt (NumSingleType (IntegralNumType ty)) | IntegralDict <- integralDict ty = fromBool . uncurry (<)
evalLt (NumSingleType (FloatingNumType ty)) | FloatingDict <- floatingDict ty = fromBool . uncurry (<)

evalGt :: SingleType a -> ((a, a) -> PrimBool)
evalGt (NumSingleType (IntegralNumType ty)) | IntegralDict <- integralDict ty = fromBool . uncurry (>)
evalGt (NumSingleType (FloatingNumType ty)) | FloatingDict <- floatingDict ty = fromBool . uncurry (>)

evalLtEq :: SingleType a -> ((a, a) -> PrimBool)
evalLtEq (NumSingleType (IntegralNumType ty)) | IntegralDict <- integralDict ty = fromBool . uncurry (<=)
evalLtEq (NumSingleType (FloatingNumType ty)) | FloatingDict <- floatingDict ty = fromBool . uncurry (<=)

evalGtEq :: SingleType a -> ((a, a) -> PrimBool)
evalGtEq (NumSingleType (IntegralNumType ty)) | IntegralDict <- integralDict ty = fromBool . uncurry (>=)
evalGtEq (NumSingleType (FloatingNumType ty)) | FloatingDict <- floatingDict ty = fromBool . uncurry (>=)

evalEq :: SingleType a -> ((a, a) -> PrimBool)
evalEq (NumSingleType (IntegralNumType ty)) | IntegralDict <- integralDict ty = fromBool . uncurry (==)
evalEq (NumSingleType (FloatingNumType ty)) | FloatingDict <- floatingDict ty = fromBool . uncurry (==)

evalNEq :: SingleType a -> ((a, a) -> PrimBool)
evalNEq (NumSingleType (IntegralNumType ty)) | IntegralDict <- integralDict ty = fromBool . uncurry (/=)
evalNEq (NumSingleType (FloatingNumType ty)) | FloatingDict <- floatingDict ty = fromBool . uncurry (/=)

evalMax :: SingleType a -> ((a, a) -> a)
evalMax (NumSingleType (IntegralNumType ty)) | IntegralDict <- integralDict ty = uncurry max
evalMax (NumSingleType (FloatingNumType ty)) | FloatingDict <- floatingDict ty = uncurry max

evalMin :: SingleType a -> ((a, a) -> a)
evalMin (NumSingleType (IntegralNumType ty)) | IntegralDict <- integralDict ty = uncurry min
evalMin (NumSingleType (FloatingNumType ty)) | FloatingDict <- floatingDict ty = uncurry min

