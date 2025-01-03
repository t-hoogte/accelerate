{-# LANGUAGE AllowAmbiguousTypes    #-}
{-# LANGUAGE DerivingStrategies     #-}
{-# LANGUAGE EmptyCase              #-}
{-# LANGUAGE FlexibleContexts       #-}
{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE GADTs                  #-}
{-# LANGUAGE LambdaCase             #-}
{-# LANGUAGE MultiParamTypeClasses  #-}
{-# LANGUAGE OverloadedStrings      #-}
{-# LANGUAGE PatternSynonyms        #-}
{-# LANGUAGE QuantifiedConstraints  #-}
{-# LANGUAGE RankNTypes             #-}
{-# LANGUAGE ScopedTypeVariables    #-}
{-# LANGUAGE StandaloneDeriving     #-}
{-# LANGUAGE TypeApplications       #-}
{-# LANGUAGE TypeFamilyDependencies #-}
{-# LANGUAGE TypeOperators          #-}
{-# LANGUAGE UndecidableInstances   #-}
{-# LANGUAGE ViewPatterns           #-}
{-# OPTIONS_GHC -Wno-orphans        #-}
{-# OPTIONS_GHC -Wno-name-shadowing #-}

-- |
-- Module      : Data.Array.Accelerate.AST.Partitioned
-- Copyright   : [2008..2020] The Accelerate Team
-- License     : BSD3
--
-- Maintainer  : Trevor L. McDonell <trevor.mcdonell@gmail.com>
-- Stability   : experimental
-- Portability : non-portable (GHC extensions)
--
module Data.Array.Accelerate.AST.Partitioned (
  module Data.Array.Accelerate.AST.Operation,
  module Data.Array.Accelerate.AST.Partitioned,
  GroundR(..), NFData'(..), Arg(..),
  AccessGroundR(..),
  PreArgs(..), Modifier(..),
  Label(..),
) where


import Data.Array.Accelerate.AST.Operation hiding (OperationAcc, OperationAfun)

import Prelude hiding ( take )
import Data.Bifunctor
import Data.Maybe (fromMaybe)
import Data.Array.Accelerate.Trafo.Desugar (ArrayDescriptor(..))
import Data.Array.Accelerate.Trafo.Operation.Simplify (SimplifyOperation(..))
import Data.Array.Accelerate.Representation.Array (Array, Buffers, ArrayR (..))
import Data.Array.Accelerate.AST.LeftHandSide
import Data.Array.Accelerate.Representation.Shape (ShapeR (..), shapeType, typeShape)
import Data.Type.Equality
import Unsafe.Coerce (unsafeCoerce)
import Data.Array.Accelerate.Representation.Type
import Data.Array.Accelerate.Type
import Data.Array.Accelerate.AST.Idx
import Data.Array.Accelerate.AST.Environment
import Data.Array.Accelerate.Error

import Data.Array.Accelerate.Trafo.Var
import Data.Array.Accelerate.Trafo.Exp.Substitution
import Data.Array.Accelerate.Trafo.Substitution
import Data.Array.Accelerate.Trafo.Partitioning.ILP.Labels (Labels, LabelledArgs, LabelledArg (..), ALabel (..), ELabel (..), Label(..), ELabelTup)
import Data.List (sortOn, partition, groupBy, nubBy)
import qualified Data.Functor.Const as C
import Data.Array.Accelerate.Trafo.Partitioning.ILP.Graph (LabelledArgOp (..), BackendClusterArg, MakesILP (..), LabelledArgsOp, BackendCluster)
import Data.Array.Accelerate.Trafo.Operation.LiveVars
import Control.Applicative ((<|>))
import Data.Array.Accelerate.AST.Var (varsType)
import Data.Array.Accelerate.Analysis.Match



type PartitionedAcc  op = PreOpenAcc  (Clustered op)
type PartitionedAfun op = PreOpenAfun (Clustered op)


data Clustered op args = Clustered (Cluster op args) (BackendCluster op args)

data Cluster op args where
  SingleOp :: SingleOp op args -> Label -> Cluster op args
  Fused :: Fusion largs rargs args
        -> Cluster op largs
        -> Cluster op rargs
        -> Cluster op args

data SingleOp op args where
  Single :: op opArgs
         -> ClusterArgs (FunToEnv args) opArgs
         -> SingleOp op args

type ClusterArgs env = PreArgs (ClusterArg env)
data ClusterArg env t where
  -- Perhaps require that 't' is not 'In sh e' or 'Out sh e'
  ClusterArgSingle
    :: Idx env t
    -> ClusterArg env t

  ClusterArgArray
    -- Perhaps require that 'm' is 'In' or 'Out'
    :: Modifier m -- Not Mut
    -> ShapeR sh
    -> TypeR e
    -> ClusterArgBuffers env m sh e
    -> ClusterArg env (m sh e)

data ClusterArgBuffers env m sh t where
  ClusterArgBuffersPair
    :: ClusterArgBuffers env m sh l
    -> ClusterArgBuffers env m sh r
    -> ClusterArgBuffers env m sh (l, r)

  ClusterArgBuffersDead
    :: TypeR t -- TODO: Remove? This info is already stored in ClusterArgArray
    -> Idx env (Var' sh)
    -> ClusterArgBuffers env Out sh t

  ClusterArgBuffersLive
    :: TypeR t
    -> Idx env (m sh t)
    -> ClusterArgBuffers env m sh t

type family FunToEnv f = env | env -> f where
  FunToEnv () = ()
  FunToEnv (s -> t) = (FunToEnv t, s)

funToEnvPrj :: PreArgs a f' -> Idx (FunToEnv f') e -> a e
funToEnvPrj (a :>: _ ) ZeroIdx       = a
funToEnvPrj (_ :>: as) (SuccIdx idx) = funToEnvPrj as idx
funToEnvPrj _ _ = internalError "Empty environment"

-- These correspond to the inference rules in the paper
-- datatype describing how to combine the arguments of two fused clusters
data Fusion largs rargs args where
  EmptyF :: Fusion () () ()
  Vertical :: ArrayR (Array sh e)
           -> Fusion l r a
           -> Fusion (Out sh e -> l) (In sh e -> r) (Var' sh -> a)
  Horizontal :: Fusion l r a
             -> Fusion (In sh e -> l) (In sh e -> r) (In sh e -> a)
  Diagonal :: Fusion l r a
           -> Fusion (Out sh e -> l) (In sh e -> r) (Out sh e -> a)
  IntroI1 :: Fusion l r a
          -> Fusion (In sh e -> l) r (In sh e -> a)
  IntroI2 :: Fusion l r a
          -> Fusion l (In sh e -> r) (In sh e -> a)
  IntroO1 :: Fusion l r a
          -> Fusion (Out sh e -> l) r (Out sh e -> a)
  IntroO2 :: Fusion l r a
          -> Fusion l (Out sh e -> r) (Out sh e -> a)
  -- not in the paper; not meant for array args:
  -- Ivo: 'mut' arguments do go in here, right?
  IntroL :: Fusion l r a -> Fusion (x -> l) r (x -> a)
  IntroR :: Fusion l r a -> Fusion l (x -> r) (x -> a)
deriving instance Show (Fusion l r total)


combine :: Arg env (f l) -> Arg env (f r) -> Arg env (f (l,r))
combine (ArgArray m (ArrayR shr lr) sh l) (ArgArray _ (ArrayR _ rr) _ r) = ArgArray m (ArrayR shr (TupRpair lr rr)) sh (TupRpair l r)
combine _ _ = error "SOA'd non-arrays"

split :: Arg env (f (l,r)) -> (Arg env (f l), Arg env (f r))
split (ArgArray In  (ArrayR shr (TupRpair rl rr)) sh (TupRpair bufl bufr)) = (ArgArray In  (ArrayR shr rl) sh bufl, ArgArray In  (ArrayR shr rr) sh bufr)
split (ArgArray Out (ArrayR shr (TupRpair rl rr)) sh (TupRpair bufl bufr)) = (ArgArray Out (ArrayR shr rl) sh bufl, ArgArray Out (ArrayR shr rr) sh bufr)
split _ = error "non-array soa"

splitLabelledArgs :: LabelledArg env (f (l,r)) -> (LabelledArg env (f l), LabelledArg env (f r))
splitLabelledArgs (L _ (Arr (TupRsingle _), _)) = error "pair in single"
splitLabelledArgs (L arg (Arr (TupRpair labl labr), labs)) = bimap (`L` (Arr labl, labs)) (`L` (Arr labr, labs)) $ split arg
splitLabelledArgs (L _ (NotArr, _)) = error "SOA'd non-array arg"
splitLabelledArgsOp :: LabelledArgOp op env (f (l,r)) -> (LabelledArgOp op env (f l), LabelledArgOp op env (f r))
splitLabelledArgsOp (LOp _ (Arr (TupRsingle _), _) _) = error "pair in single"
splitLabelledArgsOp (LOp arg (Arr (TupRpair labl labr), labs) b) = bimap (flip (`LOp` (Arr labl, labs)) b) (flip (`LOp` (Arr labr, labs)) b) $ split arg
splitLabelledArgsOp (LOp _ (NotArr, _) _) = error "SOA'd non-array arg"


left :: Fusion largs rargs args -> Args env args -> Args env largs
left = left' (\repr (ArgVar sh) -> ArgArray Out repr (mapTupR (\(Var t ix)->Var (GroundRscalar t) ix) sh) er)
  where
    er = error "accessing fused away array"
left' :: (forall sh e. ArrayR (Array sh e) -> f (Var' sh) -> f (Out sh e)) -> Fusion largs rargs args -> PreArgs f args -> PreArgs f largs
left' _ EmptyF ArgsNil = ArgsNil
left' k (Vertical repr f) (arg :>: args) = k repr arg :>: left' k f args
left' k (Horizontal    f) (arg:>:args)   = arg :>: left' k f args
left' k (Diagonal      f) (arg:>:args)   = arg :>: left' k f args
left' k (IntroI1       f) (arg:>:args)   = arg :>: left' k f args
left' k (IntroI2       f) (_  :>:args)   =         left' k f args
left' k (IntroO1       f) (arg:>:args)   = arg :>: left' k f args
left' k (IntroO2       f) (_  :>:args)   =         left' k f args
left' k (IntroL        f) (arg:>:args)   = arg :>: left' k f args
left' k (IntroR        f) (_  :>:args)   =         left' k f args

right :: Fusion largs rargs args -> Args env args -> Args env rargs
right = right' varToIn outToIn
right' :: (forall sh e. ArrayR (Array sh e) -> f (Var' sh) -> f (In sh e)) -> (forall sh e. f (Out sh e) -> f (In sh e)) -> Fusion largs rargs args -> PreArgs f args -> PreArgs f rargs
right' _  _  EmptyF ArgsNil = ArgsNil
right' vi oi (Vertical arr f) (arg :>: args) = vi arr arg :>: right' vi oi f args
right' vi oi (Diagonal     f) (arg :>: args) = oi arg :>: right' vi oi f args
right' vi oi (Horizontal   f) (arg :>: args) = arg :>: right' vi oi f args
right' vi oi (IntroI1      f) (_   :>: args) =         right' vi oi f args
right' vi oi (IntroI2      f) (arg :>: args) = arg :>: right' vi oi f args
right' vi oi (IntroO1      f) (_   :>: args) =         right' vi oi f args
right' vi oi (IntroO2      f) (arg :>: args) = arg :>: right' vi oi f args
right' vi oi (IntroL       f) (_   :>: args) =         right' vi oi f args
right' vi oi (IntroR       f) (arg :>: args) = arg :>: right' vi oi f args

varToIn :: ArrayR (Array sh e) -> Arg env (Var' sh) -> Arg env (In sh e)
varToIn (ArrayR shr ty) (ArgVar sh)
  | Just Refl <- matchShapeR shr (varsToShapeR sh) = ArgArray In (ArrayR shr ty) (mapTupR (\(Var t ix)->Var (GroundRscalar t) ix) sh) er
  | otherwise = error "wrong shape?"
  where er = error "accessing fused away array"
outToIn :: Arg env (Out sh e) -> Arg env (In sh e)
outToIn (ArgArray Out x y z) = ArgArray In x y z
inToOut :: Arg env (In sh e) -> Arg env (Out sh e)
inToOut (ArgArray In x y z) = ArgArray Out x y z
varToOut :: ArrayR (Array sh e) -> Arg env (Var' sh) -> Arg env (Out sh e)
varToOut arr = inToOut . varToIn arr

both :: (forall sh e. f (Out sh e) -> f (In sh e) -> f (Var' sh)) -> Fusion largs rargs args -> PreArgs f largs -> PreArgs f rargs -> PreArgs f args
both _ EmptyF ArgsNil ArgsNil = ArgsNil
both k (Vertical _    f) (l:>:ls) (r:>:rs) = k l r :>: both k f ls rs
both k (Diagonal      f) (l:>:ls) (_:>:rs) = l     :>: both k f ls rs
both k (Horizontal    f) (l:>:ls) (_:>:rs) = l     :>: both k f ls rs
both k (IntroI1       f) (l:>:ls)      rs  = l     :>: both k f ls rs
both k (IntroI2       f)      ls  (r:>:rs) = r     :>: both k f ls rs
both k (IntroO1       f) (l:>:ls)      rs  = l     :>: both k f ls rs
both k (IntroO2       f)      ls  (r:>:rs) = r     :>: both k f ls rs
both k (IntroL        f) (l:>:ls)      rs  = l     :>: both k f ls rs
both k (IntroR        f)      ls  (r:>:rs) = r     :>: both k f ls rs



flattenClustered :: Clustered op args -> [Exists op]
flattenClustered (Clustered c _) = flattenCluster c

flattenCluster :: Cluster op args -> [Exists op]
flattenCluster = (`go` [])
  where
    go :: Cluster op args -> [Exists op] -> [Exists op]
    go (SingleOp (Single op _) _) accum = Exists op : accum
    go (Fused _ a b)              accum = go a $ go b accum

varsToShapeR :: Vars ScalarType g sh -> ShapeR sh
varsToShapeR = typeRtoshapeR . varsType

typeRtoshapeR :: TypeR sh -> ShapeR sh
typeRtoshapeR TupRunit = ShapeRz
typeRtoshapeR (TupRpair sh (TupRsingle (SingleScalarType (NumSingleType (IntegralNumType TypeInt))))) = ShapeRsnoc (typeRtoshapeR sh)
typeRtoshapeR _ = error "not a shape"

type family InArg a = b | b -> a where
  InArg (In sh e ) = Value sh e
  InArg (Mut sh e) = Mut sh e
  InArg (Exp'   e) = Exp' e
  InArg (Fun'   e) = Fun' e
  InArg (Var'   e) = Var' e
  InArg (Out sh e) = Sh sh e
type family InArgs a = b | b -> a where
  InArgs  ()       = ()
  InArgs  (a -> x) = (InArgs x, InArg a)
type family InArgsOf a where
  InArgsOf () = ()
  InArgsOf (a -> x) = InArg a -> InArgsOf x

type family InArg' a where
  InArg' (Value sh e) = In sh e
  InArg' (Mut sh e  ) = Mut sh e
  InArg' (Exp' e    ) = Exp'   e
  InArg' (Fun' e    ) = Fun'   e
  InArg' (Var' e    ) = Var'   e
  InArg' (Sh sh e   ) = Out sh e
type family InArgs' a where
  InArgs'  ()       = ()
  InArgs'  (x, a) = InArg' a -> InArgs' x

inargslemma :: InArgs' (InArgs a) :~: a
inargslemma = unsafeCoerce Refl
inarglemma :: InArg (InArg' a) :~: a
inarglemma = unsafeCoerce Refl

type family OutArgs a where
  OutArgs ()              = ()
  OutArgs (Out sh e -> x) = (OutArgs x, Value sh e)
  OutArgs (_  -> x)       =  OutArgs x
type family OutArgsOf a where
  OutArgsOf () = ()
  OutArgsOf (Out sh e -> x) = Out sh e -> OutArgsOf x
  OutArgsOf (_ -> x) = OutArgsOf x

type family FromArg env a where
  FromArg env (Exp'     e) = Exp     env e
  FromArg env (Var'     e) = ExpVars env e
  FromArg env (Fun'     e) = Fun     env e
  FromArg env (Mut   sh e) = (ArrayDescriptor env (Array sh e), TypeR e)
  FromArg env x = x

type family FromArgs env a where
  FromArgs env ()            = ()
  FromArgs env (a, x) = (FromArgs env a, FromArg env x)

type FromIn  env args = FromArgs env ( InArgs args)
type FromOut env args = FromArgs env (OutArgs args)


data Value sh e = Value e (Sh sh e)
data Sh sh e    = Shape (ShapeR sh) sh

class TupRmonoid f where
  pair' :: f a -> f b -> f (a,b)
  unpair' :: f (a,b) -> (f a, f b)

fromTupR :: TupRmonoid f => f () -> TupR f a -> f a
fromTupR u TupRunit = u
fromTupR _ (TupRsingle s) = s
fromTupR u (TupRpair l r) = pair' (fromTupR u l) (fromTupR u r)


varsGet' :: Vars s env t -> Env f env -> TupR f t
varsGet' t env = mapTupR (\(Var _ idx) -> prj' idx env) t

instance TupRmonoid (TupR f) where
  pair' = TupRpair
  unpair' (TupRpair l r) = (l, r)
  unpair' _ = error "nope"
  -- injL t p = TupRpair t (proofToR p)
  -- injR t p = TupRpair (proofToR p) t



unOpLabels' :: LabelledArgsOp op env args -> LabelledArgs env args
unOpLabels' = mapArgs unOpLabel

unOpLabel :: LabelledArgOp op env args -> LabelledArg env args
unOpLabel (LOp arg l _) = L arg l

data Both f g a = Both (f a) (g a) deriving (Show, Eq)
fst' :: Both f g a -> f a
fst' (Both x _) = x
snd' :: Both f g a -> g a
snd' (Both _ y) = y

instance (TupRmonoid f, TupRmonoid g) => TupRmonoid (Both f g) where
  pair' (Both a b) (Both c d) = Both (pair' a c) (pair' b d)
  unpair' (Both (unpair' -> (a, c)) (unpair' -> (b, d))) = (Both a b, Both c d)


zipArgs :: PreArgs f a -> PreArgs g a -> PreArgs (Both f g) a
zipArgs ArgsNil ArgsNil = ArgsNil
zipArgs (f:>:fs) (g:>:gs) = Both f g :>: zipArgs fs gs

onZipped :: (f a -> f b -> f c) -> (g a -> g b -> g c) -> (Both f g a -> Both f g b -> Both f g c)
onZipped f g (Both fa ga) (Both fb gb) = Both (f fa fb) (g ga gb)

-- assumes that the arguments are already sorted!
fuse :: MakesILP op
     => LabelledArgsOp op env l -> LabelledArgsOp op env r -> PreArgs f l -> PreArgs f r -> Clustered op l -> Clustered op r
     -> (forall sh e. f (Out sh e) -> f (In sh e) -> f (Var' sh))
     -> (forall args. PreArgs f args -> Clustered op args -> result)
     -> result
fuse labl labr largs rargs (Clustered cl bl) (Clustered cr br) c k = fuse' labl labr (zipArgs largs bl) (zipArgs rargs br) cl cr (onZipped c combineBackendClusterArg)
  $ \args c' -> k (mapArgs fst' args) (Clustered c' $ mapArgs snd' args)

-- assumes that the arguments are already sorted!
fuse' :: MakesILP op => LabelledArgsOp op env l -> LabelledArgsOp op env r -> PreArgs f l -> PreArgs f r -> Cluster op l -> Cluster op r
      -> (forall sh e. f (Out sh e) -> f (In sh e) -> f (Var' sh))
      -> (forall args. PreArgs f args -> Cluster op args -> result)
      -> result
fuse' labl labr largs rargs l r c k =
  mkFused labl labr $ \f -> k (both c f largs rargs) (Fused f l r)

mkFused :: MakesILP op => LabelledArgsOp op env l -> LabelledArgsOp op env r -> (forall args. Fusion l r args -> result) -> result
mkFused ArgsNil ArgsNil k = k EmptyF
mkFused ArgsNil (LOp r _ _ :>: rs) k = mkFused ArgsNil rs $ \f -> k (addright r f)
mkFused (LOp l _ _ :>: ls) ArgsNil k = mkFused ls ArgsNil $ \f -> k (addleft l f)
mkFused ((LOp l (NotArr,_) _) :>: ls) rs k = mkFused ls rs $ \f -> k (addleft l f)
mkFused ls ((LOp r (NotArr,_)_ ) :>: rs) k = mkFused ls rs $ \f -> k (addright r f)
mkFused ((LOp l (Arr TupRunit,_)_ ) :>: ls) rs k = mkFused ls rs $ \f -> k (addleft l f)
mkFused ls ((LOp r (Arr TupRunit,_)_) :>: rs) k = mkFused ls rs $ \f -> k (addright r f)
mkFused (l'@(LOp l _ bl) :>: ls) (r'@(LOp r _ br) :>: rs) k
  | Just le <- getElabelForSort $ unOpLabel l'
  , Just re <- getElabelForSort $ unOpLabel r'
    = case compare le re of
      LT -> mkFused ls (r':>:rs) $ \f -> k (addleft l f)
      GT -> mkFused (l':>:ls) rs $ \f -> k (addright r f)
      EQ -> mkFused ls rs $ \f -> if bl == br then addboth l r f k else k (addleft l (addright r f))
mkFused ((LOp l@(ArgArray Mut _ _ _) _ _) :>: ls) rs k = mkFused ls rs $ \f -> k (addleft l f)
mkFused ls ((LOp r@(ArgArray Mut _ _ _) _ _) :>: rs) k = mkFused ls rs $ \f -> k (addright r f)
mkFused ((LOp _ (Arr TupRpair{}, _)_) :>: _) _ _ = error "not soa'd array"
mkFused _ ((LOp _ (Arr TupRpair{}, _)_) :>: _) _ = error "not soa'd array"
mkFused _ _ _ = error "exhaustive"

addleft :: Arg env arg -> Fusion left right args -> Fusion (arg->left) right (arg->args)
addleft (ArgVar _          ) f = IntroL  f
addleft (ArgExp _          ) f = IntroL  f
addleft (ArgFun _          ) f = IntroL  f
addleft (ArgArray Mut _ _ _) f = IntroL  f
addleft (ArgArray In  _ _ _) f = IntroI1 f
addleft (ArgArray Out _ _ _) f = IntroO1 f

addright :: Arg env arg -> Fusion left right args -> Fusion left (arg->right) (arg->args)
addright (ArgVar _          ) f = IntroR  f
addright (ArgExp _          ) f = IntroR  f
addright (ArgFun _          ) f = IntroR  f
addright (ArgArray Mut _ _ _) f = IntroR  f
addright (ArgArray In  _ _ _) f = IntroI2 f
addright (ArgArray Out _ _ _) f = IntroO2 f

addboth :: Arg env l -> Arg env r -> Fusion left right args -> (forall arg. Fusion (l->left) (r->right) (arg -> args) -> result) -> result
addboth (ArgArray In  r1 _ _) (ArgArray In  r2 _ _) f k
  | Just Refl <- matchArrayR r1 r2 = k $ Horizontal f
  | otherwise = error "types of horizontally fused arrays are different"
addboth (ArgArray Out r1 _ _) (ArgArray In  r2 _ _) f k
  | Just Refl <- matchArrayR r1 r2 = k $ Diagonal f
  | otherwise = error "types of diagonally fused arrays are different"
addboth (ArgArray Out _ _ _) (ArgArray Out _ _ _) _ _ = error "two producers of the same array"
addboth (ArgArray In  _ _ _) (ArgArray Out _ _ _) _ _ = error "reverse vertical/diagonal"
addboth _ _ _ _ = error "fusing non-arrays"

getElabelForSort :: LabelledArg env a -> Maybe ELabel
getElabelForSort (L (ArgArray m (ArrayR _ TupRsingle{}) _ _) (Arr (TupRsingle (C.Const e)),_))
  | In  <- m = Just e
  | Out <- m = Just e
getElabelForSort _ = Nothing

singleton
  :: MakesILP op
  => Label
  -> LabelledArgsOp op env args
  -> op args
  -> (forall args'. Clustered op args' -> LabelledArgsOp op env args' -> r)
  -> r
singleton l largs op k
  | Exists sorted <- sortAndExpandArgs largs
  , opArgs <- createClusterArgs sorted largs
  = k
    (Clustered
      (SingleOp (Single op opArgs) l)
      (mapArgs getClusterArg sorted))
    sorted

createClusterArgs
  :: forall op env sorted args.
     LabelledArgsOp op env sorted
  -> LabelledArgsOp op env args
  -> ClusterArgs (FunToEnv sorted) args
createClusterArgs sorted = go 0
  where
    go
      :: Int -- Number of ClusterArgSingle that we've already handled
      -> LabelledArgsOp op env args'
      -> ClusterArgs (FunToEnv sorted) args'
    go _ ArgsNil = ArgsNil
    go n (a :>: as) = a' :>: go n' as
      where
        a' = createClusterArg n sorted a
        n' = case a' of
          ClusterArgSingle _ -> n + 1
          _ -> n

-- We ensure that environment starts with all non-in-or-out-array arguments,
-- then all array arguments. That simplifies the search for non-array arguments in 'sorted'.
createClusterArg
  :: forall op env sorted arg.
     Int -- Number of ClusterArgSingle that we've already handled
  -> LabelledArgsOp op env sorted
  -> LabelledArgOp op env arg
  -> ClusterArg (FunToEnv sorted) arg
createClusterArg _ sorted (LOp (ArgArray (m :: Modifier m) (ArrayR (shr :: ShapeR sh) tp) sh _) (Arr labels, _) _)
  | inOrOut m = ClusterArgArray m shr tp $ go tp labels
  where
    inOrOut :: Modifier m -> Bool
    inOrOut In  = True
    inOrOut Out = True
    inOrOut _   = False

    go :: TypeR t -> ELabelTup t -> ClusterArgBuffers (FunToEnv sorted) m sh t
    go TupRunit TupRunit
      = ClusterArgBuffersLive TupRunit $ findUnit sorted
    go (TupRsingle t) (TupRsingle (C.Const label))
      = ClusterArgBuffersLive (TupRsingle t) $ findLabel (TupRsingle t) label sorted
    go (TupRpair t1 t2) (TupRpair l1 l2)
      = go t1 l1 `ClusterArgBuffersPair` go t2 l2
    go _ _ = internalError "Tuple mismatch"

    findUnit
      :: LabelledArgsOp op env sorted'
      -> Idx (FunToEnv sorted') (m sh ())
    findUnit = \case
      LOp (ArgArray m' (ArrayR _ TupRunit) sh' _) _ _ :>: _
        | Just Refl <- matchModifier m m'
        , Just Refl <- matchVars sh sh'
        -> ZeroIdx
      _ :>: sorted' -> SuccIdx $ findUnit sorted'
      ArgsNil -> internalError "Unit array not found in sorted arguments"

    findLabel
      :: TupR ScalarType t
      -> ELabel
      -> LabelledArgsOp op env sorted'
      -> Idx (FunToEnv sorted') (m sh t)
    findLabel tp label = \case
      LOp (ArgArray m' (ArrayR _ tp') sh' _) (Arr (TupRsingle (C.Const label')), _) _ :>: _
        | label == label'
        , Refl <- expectOr "Modifier didn't match" $ matchModifier m m'
        , Refl <- expectOr "Shapes didn't match" $ matchVars sh sh'
        , Refl <- expectOr "Array types didn't match" $ matchTypeR tp tp'
        -> ZeroIdx
      _ :>: sorted' -> SuccIdx $ findLabel tp label sorted'
      ArgsNil -> internalError "Label not found in sorted arguments"

    expectOr _ (Just x) = x
    expectOr err _ = internalError err

-- ClusterArgSingles are not shuffled, they are kept in the original order.
-- To find the ith ClusterArgSingle, we thus search for the ith ClusterArgSingle in 'sorted'.
-- Function 'go' does this search, and skips over any In or Out arguments.
createClusterArg count sorted (LOp arg _ _) = ClusterArgSingle $ go count sorted
  where
    go :: Int -> LabelledArgsOp op env sorted' -> Idx (FunToEnv sorted') arg
    go n (LOp (ArgArray In  _ _ _) _ _ :>: args) = SuccIdx $ go n args
    go n (LOp (ArgArray Out _ _ _) _ _ :>: args) = SuccIdx $ go n args
    go 0 (LOp arg' _ _ :>: _)
      -- We only validate the type of the argument.
      -- We assume the ClusterArgSingles are not shuffled. We only do this
      -- to inform GHC that this is sound, and to catch situations where things
      -- are really broken.
      | Just Refl <- matchArgType arg arg' = ZeroIdx
      | otherwise = internalError "ClusterArgSingles are not in the right order"
    go n (_ :>: args) = SuccIdx $ go (n - 1) args
    go _ ArgsNil = internalError "ClusterArgSingle not found"

-- Checks whether two types are equal, to a certain extent.
-- If this function returns Just, the types of the two arguments are equal.
-- However, the inverse is not always true.
-- Use this function if you know that the arguments are equal, but want
-- type-level proof that the types match.
matchArgType :: Arg env s -> Arg env t -> Maybe (s :~: t)
matchArgType (ArgVar v1) (ArgVar v2)
  | Just Refl <- matchVars v1 v2 = Just Refl
matchArgType (ArgExp e1) (ArgExp e2)
  | Just Refl <- matchTypeR (expType e1) (expType e2) = Just Refl
matchArgType (ArgFun fun1) (ArgFun fun2)
  | Just Refl <- go fun1 fun2 = Just Refl
  where
    go :: OpenFun env1 env t1 -> OpenFun env2 env t2 -> Maybe (t1 :~: t2)
    go (Lam lhs1 f1) (Lam lhs2 f2)
      | Just Refl <- matchTypeR (lhsToTupR lhs1) (lhsToTupR lhs2)
      , Just Refl <- go f1 f2
      = Just Refl
    go (Body e1) (Body e2) = matchTypeR (expType e1) (expType e2)
    go _ _ = Nothing
matchArgType (ArgArray m1 repr1 _ _) (ArgArray m2 repr2 _ _)
  | Just Refl <- matchModifier m1 m2
  , Just Refl <- matchArrayR repr1 repr2 = Just Refl
matchArgType _ _ = Nothing

-- Checks whether the two Args are the same.
-- Assumes that the Args are both arrays and that
-- the arrays both consist of a single array, or a unit array
-- This is used in createClusterArg to both find the corresponding argument,
-- and to inform the type checker that the array has the correct type.
matchArgArraySingle :: Arg env a -> Arg env b -> Maybe (a :~: b)
matchArgArraySingle (ArgArray m1 (ArrayR _ (TupRsingle t1)) sh1 (TupRsingle buffer1)) (ArgArray m2 (ArrayR _ (TupRsingle t2)) sh2 (TupRsingle buffer2))
  | Just Refl <- matchModifier m1 m2
  , Just Refl <- matchVar buffer1 buffer2
  , Just Refl <- matchVars sh1 sh2
  , Just Refl <- matchScalarType t1 t2 = Just Refl
matchArgArraySingle (ArgArray m1 (ArrayR _ TupRunit) sh1 _) (ArgArray m2 (ArrayR _ TupRunit) sh2 _)
  | Just Refl <- matchModifier m1 m2
  , Just Refl <- matchVars sh1 sh2 = Just Refl
matchArgArraySingle _ _ = Nothing

matchModifier :: Modifier m1 -> Modifier m2 -> Maybe (m1 :~: m2)
matchModifier In In = Just Refl
matchModifier Out Out = Just Refl
matchModifier Mut Mut = Just Refl
matchModifier _ _ = Nothing

sortAndExpandArgs :: LabelledArgsOp op env args -> Exists (LabelledArgsOp op env)
sortAndExpandArgs args = argsFromList $ singles ++ unitArraysDedup ++ dedup
  where
    (arrays, singles) = partition isNonUnitInOut $ argsToList args
    expanded = arrays >>= \(Exists arg) -> expandArg arg
    sorted = sortOn fst expanded
    dedup = map (snd . head) $ groupBy (\a b -> fst a == fst b) sorted
    unitArraysDedup = nubBy compareUnitArrays (arrays >>= \(Exists arg) -> expandUnitArg arg)

    isNonUnitInOut :: Exists (LabelledArgOp op env) -> Bool
    isNonUnitInOut (Exists (LOp (ArgArray _ (ArrayR _ TupRunit) _ _) _ _)) = False
    isNonUnitInOut (Exists (LOp (ArgArray m _ _ _) _ _)) = case m of
      In -> True
      Out -> True
      _ -> False
    isNonUnitInOut _ = False

    compareUnitArrays :: Exists (LabelledArgOp op env) -> Exists (LabelledArgOp op env) -> Bool
    compareUnitArrays (Exists (LOp (ArgArray m _ sh _) _ _)) (Exists (LOp (ArgArray m' _ sh' _) _ _))
      | Just _ <- matchModifier m m'
      , Just _ <- matchVars sh sh'
      = True
    compareUnitArrays _ _ = False

expandUnitArg :: LabelledArgOp op env t -> [(Exists (LabelledArgOp op env))]
expandUnitArg (LOp (ArgArray m (ArrayR shr (TupRpair t1 t2)) sh (TupRpair b1 b2)) (Arr (TupRpair l1 l2), set) ba)
  =  expandUnitArg (LOp (ArgArray m (ArrayR shr t1) sh b1) (Arr l1, set) ba)
  ++ expandUnitArg (LOp (ArgArray m (ArrayR shr t2) sh b2) (Arr l2, set) ba)
expandUnitArg arg@(LOp _ (Arr TupRunit, _) _) = [Exists arg]
expandUnitArg _ = []

expandArg :: LabelledArgOp op env t -> [(ELabel, Exists (LabelledArgOp op env))]
expandArg (LOp (ArgArray m (ArrayR shr (TupRpair t1 t2)) sh (TupRpair b1 b2)) (Arr (TupRpair l1 l2), set) ba)
  =  expandArg (LOp (ArgArray m (ArrayR shr t1) sh b1) (Arr l1, set) ba)
  ++ expandArg (LOp (ArgArray m (ArrayR shr t2) sh b2) (Arr l2, set) ba)
expandArg arg@(LOp _ (Arr (TupRsingle (C.Const l)), _) _)
  = [(l, Exists arg)]
expandArg (LOp _ (Arr TupRunit, _) _) = []
expandArg _ = internalError "Tuple mismatch with labels"

instance ShrinkArg (BackendClusterArg op) => SLVOperation (Clustered op) where
  slvOperation (Clustered cluster b) = Just $ ShrinkOperation $ \ff' a' a ->
    case slvCluster cluster ff' a' a of
      ShrunkOperation' cluster' args ->
        ShrunkOperation (Clustered cluster' $ shrinkArgs ff' b) args

instance SimplifyOperation (Clustered op)
  -- Default implementation, where detectCopy always returns []
  -- Any copies should already have been detected before the program was fused.

slvClusterArg :: forall f f' t. SubArgs f f' -> ClusterArg (FunToEnv f) t -> ClusterArg (FunToEnv f') t
slvClusterArg subArgs (ClusterArgSingle idx) = case reindexSlv subArgs idx of
  ReindexSlvKeep idx' -> ClusterArgSingle idx'
  _ -> internalError "Expected a preserved variable, as this is not an Out argument"
slvClusterArg subArgs (ClusterArgArray m shr tp buffers) = ClusterArgArray m shr tp $ go buffers
  where
    go :: ClusterArgBuffers (FunToEnv f) m sh e -> ClusterArgBuffers (FunToEnv f') m sh e
    go (ClusterArgBuffersPair a1 a2) = go a1 `ClusterArgBuffersPair` go a2
    go (ClusterArgBuffersDead tp idx) = case reindexSlv subArgs idx of
      ReindexSlvKeep idx' -> ClusterArgBuffersDead tp idx'
    go (ClusterArgBuffersLive tp idx) = case reindexSlv subArgs idx of
      ReindexSlvKeep idx' -> ClusterArgBuffersLive tp idx'
      ReindexSlvDead idx' -> ClusterArgBuffersDead tp idx'

reindexSlv :: SubArgs f f' -> Idx (FunToEnv f) t -> ReindexSlv f' t
reindexSlv (SubArgsDead _) ZeroIdx = ReindexSlvDead ZeroIdx
reindexSlv (SubArgsLive arg _) ZeroIdx = case arg of
  SubArgKeep -> ReindexSlvKeep ZeroIdx
  SubArgOut SubTupRkeep -> ReindexSlvKeep ZeroIdx
  _ -> internalError "Expected preserved value"
reindexSlv (SubArgsDead s) (SuccIdx idx) = case reindexSlv s idx of
  ReindexSlvKeep idx -> ReindexSlvKeep $ SuccIdx idx
  ReindexSlvDead idx -> ReindexSlvDead $ SuccIdx idx
reindexSlv (SubArgsLive _ s) (SuccIdx idx) = case reindexSlv s idx of
  ReindexSlvKeep idx -> ReindexSlvKeep $ SuccIdx idx
  ReindexSlvDead idx -> ReindexSlvDead $ SuccIdx idx
reindexSlv SubArgsNil idx = case idx of {}

data ReindexSlv f t where
  ReindexSlvKeep :: Idx (FunToEnv f) t -> ReindexSlv f t
  ReindexSlvDead :: Idx (FunToEnv f) (Var' sh) -> ReindexSlv f (Out sh e)

slvCluster :: Cluster op f -> SubArgs f f' -> Args env' f' -> Args env f -> ShrunkOperation' (Cluster op) env' f'
slvCluster (SingleOp (Single op args) label) sub args' _
  = ShrunkOperation' (SingleOp (Single op $ mapArgs (slvClusterArg sub) args) label) args'

slvCluster (Fused fusion left right) sub args1' args1 = splitslvstuff fusion sub args1' args1 $
  \f' lsub largs' largs rsub rargs' rargs -> case (slvCluster left lsub largs' largs, slvCluster right rsub rargs' rargs) of
    (ShrunkOperation' lop largs'', ShrunkOperation' rop rargs'') ->
      ShrunkOperation' (Fused f' lop rop) (both (\x _ -> outvar x) f' largs'' rargs'')
  where
    splitslvstuff :: Fusion l r a
      -> SubArgs a a'
      -> Args env' a'
      -> Args env a
      -> (forall l' r'. Fusion l' r' a' -> SubArgs l l' -> Args env' l' -> Args env l -> SubArgs r r' -> Args env' r' -> Args env r -> result)
      -> result
    splitslvstuff EmptyF SubArgsNil ArgsNil ArgsNil k = k EmptyF SubArgsNil ArgsNil ArgsNil SubArgsNil ArgsNil ArgsNil
    splitslvstuff _ (SubArgsLive (SubArgOut SubTupRskip) _) _ _ _ = error "completely removed out arg using subtupr" --splitslvstuff f (SubArgsDead subs) args' args k
    splitslvstuff f (SubArgsLive (SubArgOut SubTupRkeep) subs) args' args k = splitslvstuff f (SubArgsLive SubArgKeep subs) args' args k
    splitslvstuff _ (SubArgsLive (SubArgOut SubTupRpair{}) _) (_:>:_) (_:>:_) _ = error "not SOA'd array"
    splitslvstuff (Diagonal   f) (SubArgsDead subs) args' (ArgArray _ r sh _:>:args) k = splitslvstuff (Vertical r f) (SubArgsLive SubArgKeep subs) args' (ArgVar (groundToExpVar (shapeType $ arrayRshape r) sh) :>:args) k
    splitslvstuff (IntroO1    f) (SubArgsDead subs) (arg':>:args') (arg:>:args) k = splitslvstuff f subs args' args $ \f lsubs largs' largs rsubs rargs' rargs -> k (IntroL   f) (SubArgsDead lsubs) (arg':>:largs') (arg:>:largs)              rsubs          rargs'         rargs
    splitslvstuff (IntroO2    f) (SubArgsDead subs) (arg':>:args') (arg:>:args) k = splitslvstuff f subs args' args $ \f lsubs largs' largs rsubs rargs' rargs -> k (IntroR   f)              lsubs          largs'         largs  (SubArgsDead rsubs) (arg':>:rargs') (arg:>:rargs)
    splitslvstuff (IntroL     _) (SubArgsDead _) (_:>:_) (_:>:_) _ = error "out in IntroL/R"
    splitslvstuff (IntroR     _) (SubArgsDead _) (_:>:_) (_:>:_) _ = error "out in IntroL/R"
    splitslvstuff (Vertical r  f) (SubArgsLive SubArgKeep subs) (ArgVar arg':>:args') (ArgVar arg:>:args) k = splitslvstuff f subs args' args $ \f lsubs largs' largs rsubs rargs' rargs -> k (Vertical r f) (SubArgsLive SubArgKeep lsubs) (ArgArray Out r sh' buf :>:largs') (ArgArray Out r sh buf :>:largs) (SubArgsLive SubArgKeep rsubs) (ArgArray In r sh' buf :>:rargs') (ArgArray In r sh buf :>:rargs)
      where
        buf = error "fused away buffer"
        sh = expToGroundVar arg
        sh' = expToGroundVar arg'
    splitslvstuff (Diagonal   f) (SubArgsLive SubArgKeep subs) (arg'@(ArgArray Out r' sh' buf'):>:args') (arg@(ArgArray Out r sh buf):>:args) k = splitslvstuff f subs args' args $ \f lsubs largs' largs rsubs rargs' rargs -> k (Diagonal   f) (SubArgsLive SubArgKeep lsubs) (arg':>:largs') (arg:>:largs) (SubArgsLive SubArgKeep rsubs) (ArgArray In r' sh' buf':>:rargs') (ArgArray In r sh buf:>:rargs)
    splitslvstuff (Horizontal f) (SubArgsLive SubArgKeep subs) (arg':>:args') (arg:>:args) k = splitslvstuff f subs args' args $ \f lsubs largs' largs rsubs rargs' rargs -> k (Horizontal f) (SubArgsLive SubArgKeep lsubs) (       arg':>:largs') (       arg:>:largs) (SubArgsLive SubArgKeep rsubs) (      arg':>:rargs') (      arg:>:rargs)
    splitslvstuff (IntroI1    f) (SubArgsLive SubArgKeep subs) (arg':>:args') (arg:>:args) k = splitslvstuff f subs args' args $ \f lsubs largs' largs rsubs rargs' rargs -> k (IntroI1    f) (SubArgsLive SubArgKeep lsubs) (       arg':>:largs') (       arg:>:largs)                         rsubs                rargs'               rargs
    splitslvstuff (IntroI2    f) (SubArgsLive SubArgKeep subs) (arg':>:args') (arg:>:args) k = splitslvstuff f subs args' args $ \f lsubs largs' largs rsubs rargs' rargs -> k (IntroI2    f)                         lsubs                 largs'                largs  (SubArgsLive SubArgKeep rsubs) (      arg':>:rargs') (      arg:>:rargs)
    splitslvstuff (IntroO1    f) (SubArgsLive SubArgKeep subs) (arg':>:args') (arg:>:args) k = splitslvstuff f subs args' args $ \f lsubs largs' largs rsubs rargs' rargs -> k (IntroO1    f) (SubArgsLive SubArgKeep lsubs) (       arg':>:largs') (       arg:>:largs)                         rsubs                rargs'               rargs
    splitslvstuff (IntroO2    f) (SubArgsLive SubArgKeep subs) (arg':>:args') (arg:>:args) k = splitslvstuff f subs args' args $ \f lsubs largs' largs rsubs rargs' rargs -> k (IntroO2    f)                         lsubs                 largs'                largs  (SubArgsLive SubArgKeep rsubs) (      arg':>:rargs') (      arg:>:rargs)
    splitslvstuff (IntroL     f) (SubArgsLive SubArgKeep subs) (arg':>:args') (arg:>:args) k = splitslvstuff f subs args' args $ \f lsubs largs' largs rsubs rargs' rargs -> k (IntroL     f) (SubArgsLive SubArgKeep lsubs) (       arg':>:largs') (       arg:>:largs)                         rsubs                rargs'               rargs
    splitslvstuff (IntroR     f) (SubArgsLive SubArgKeep subs) (arg':>:args') (arg:>:args) k = splitslvstuff f subs args' args $ \f lsubs largs' largs rsubs rargs' rargs -> k (IntroR     f)                         lsubs                 largs'                largs  (SubArgsLive SubArgKeep rsubs) (      arg':>:rargs') (      arg:>:rargs)

-- Variant of ShrunkOperation where f is not an existential
data ShrunkOperation' op env f where
  ShrunkOperation' :: op f -> Args env f -> ShrunkOperation' op env f

outvar :: Arg env (Out sh e) -> Arg env (Var' sh)
outvar (ArgArray Out (ArrayR shr _) sh _) = ArgVar $ groundToExpVar (shapeType shr) sh

prjClusterArgs :: Args env args -> ClusterArgs (FunToEnv args) s -> Args env s
prjClusterArgs args = mapArgs (prjClusterArg args)

prjClusterArg :: forall env args s. Args env args -> ClusterArg (FunToEnv args) s -> Arg env s
prjClusterArg args (ClusterArgSingle idx) = funToEnvPrj args idx
prjClusterArg args (ClusterArgArray (m :: Modifier m) (shr :: ShapeR sh) tp buffers') = case go buffers' of
  (Just sh, buffers) -> ArgArray m (ArrayR shr tp) sh buffers
  _ -> internalError "Arrays only consisting of units are not supported in fusion"
  where
    go :: ClusterArgBuffers (FunToEnv args) m sh e -> (Maybe (GroundVars env sh), GroundVars env (Buffers e))
    go (ClusterArgBuffersPair c1 c2)
      | (sh1, buffers1) <- go c1
      , (sh2, buffers2) <- go c2
      = (sh1 <|> sh2, TupRpair buffers1 buffers2)
    go (ClusterArgBuffersLive _ idx)
      | ArgArray _ _ sh buffers <- funToEnvPrj args idx
      = (Just sh, buffers)
    go (ClusterArgBuffersDead _ idx)
      | ArgVar sh <- funToEnvPrj args idx
      = (Just $ mapTupR f sh, TupRsingle $ internalError "Cannot access array removed by strongly-live-variable analysis")

    f :: ExpVar env t -> GroundVar env t
    f (Var tp idx) = Var (GroundRscalar tp) idx

showSorted :: LabelledArgsOp op env args -> String
showSorted ArgsNil = ""
showSorted (a :>: args) = case a of
  LOp (ArgArray m _ _ _) (_,ls) _ -> show m <> "{" <> show ls <> "}" <> showSorted args
  _ -> showSorted args

data FlatCluster op f where
  FlatCluster
    :: LeftHandSide OutR t (FunToEnv f) env
    -> OutShapes (FunToEnv f) t
    -> [FlatOp op env]
    -> FlatCluster op f

data FlatOp op env where
  FlatOp
    :: op opArgs
    -> FlatArgs env opArgs
    -> FlatOp op env

type FlatArgs env = PreArgs (FlatArg env)
data FlatArg env t where
  -- Perhaps require that 't' is not 'In sh e' or 'Out sh e'
  FlatArgSingle
    :: Idx env t
    -> FlatArg env t

  FlatArgArray
    -- Perhaps require that 'm' is 'In' or 'Out'
    :: Modifier m -- Not Mut
    -> ShapeR sh
    -> TypeR e
    -> FlatArgBuffers env m sh e
    -> FlatArg env (m sh e)

data FlatArgBuffers env m sh t where
  FlatArgBuffersPair
    :: FlatArgBuffers env m sh l
    -> FlatArgBuffers env m sh r
    -> FlatArgBuffers env m sh (l, r)

  FlatArgBuffersLive
    :: TypeR t
    -> Idx env (m sh t)
    -> FlatArgBuffers env m sh t

  FlatArgBuffersFused
    :: TypeR t
    -> Idx env (Out sh t)
    -> FlatArgBuffers env In sh t

data OutR a where
  OutR :: ArrayR (Array sh e) -> OutR (Out sh e)

type OutShapes env = TupR (OutShape env)
data OutShape env a where
  OutShape :: Idx env (Var' sh) -> OutShape env (Out sh e)

instance Sink' (FlatOp op) where
  weaken' k (FlatOp op args) = FlatOp op $ mapArgs (weaken k) args

instance Sink FlatArg where
  weaken k (FlatArgSingle i) = FlatArgSingle $ weaken k i
  weaken k (FlatArgArray m shr tp bs) = FlatArgArray m shr tp $ weakenFlatArgBuffers k bs

weakenFlatArgBuffers :: env :> env' -> FlatArgBuffers env m sh t -> FlatArgBuffers env' m sh t
weakenFlatArgBuffers k (FlatArgBuffersPair b1 b2)
  = weakenFlatArgBuffers k b1 `FlatArgBuffersPair` weakenFlatArgBuffers k b2
weakenFlatArgBuffers k (FlatArgBuffersLive tp idx)
  = FlatArgBuffersLive tp $ weaken k idx
weakenFlatArgBuffers k (FlatArgBuffersFused tp idx)
  = FlatArgBuffersFused tp $ weaken k idx

data ToFlatCluster op env where
  ToFlatCluster
    :: TupR OutR a -- Fused away and dead output arrays
    -- The OutR Vars should not be needed for the OutShapes, but we include them
    -- anyway to use the same index transformation for the OutShapes and the FlatOps.
    -> (forall env'. FlattenEnv env env' -> Vars OutR env' a -> OutShapes env' a)
    -> (forall env'. FlattenEnv env env' -> Vars OutR env' a -> [FlatOp op env'])
    -> ToFlatCluster op env

data ToFlatArgs env t where
  ToFlatArgs
    :: TupR OutR a -- Fused away and dead output arrays
    -> (forall env'. FlattenEnv env env' -> OutShapes env' a)
    -> (forall env'. FlattenEnv env env' -> Vars OutR env' a -> FlatArgs env' t)
    -> ToFlatArgs env t

data ToFlatArg env t where
  ToFlatArg
    :: TupR OutR a -- Fused away and dead output arrays
    -> (forall env'. FlattenEnv env env' -> OutShapes env' a)
    -> (forall env'. FlattenEnv env env' -> Vars OutR env' a -> FlatArg env' t)
    -> ToFlatArg env t

data ToFlatArgBuffers env m sh t where
  ToFlatArgBuffers
    :: TupR OutR a -- Fused away and dead output arrays
    -> (forall env'. FlattenEnv env env' -> OutShapes env' a)
    -> (forall env'. FlattenEnv env env' -> Vars OutR env' a -> FlatArgBuffers env' m sh t)
    -> ToFlatArgBuffers env m sh t

data ToFlatFusion env envL envR where
  ToFlatFusion
    :: TupR OutR a -- Fused away and dead output arrays
    -> (forall env'. FlattenEnv env env' -> OutShapes env' a)
    -> (forall env'. FlattenEnv env env' -> Vars OutR env' a -> FlattenEnv envL env')
    -> (forall env'. FlattenEnv env env' -> Vars OutR env' a -> FlattenEnv envR env')
    -> ToFlatFusion env envL envR

data ToFlatIdx env t where
  ToFlatIdxEqual :: Idx env t -> ToFlatIdx env t
  ToFlatIdxFused :: Idx env (Out sh e) -> ToFlatIdx env (In sh e)

type FlattenEnv env env' = forall t. Idx env t -> ToFlatIdx env' t

toFlatClustered :: Clustered op f -> FlatCluster op f
toFlatClustered (Clustered cluster _) = toFlatCluster cluster

toFlatCluster :: Cluster op f -> FlatCluster op f
toFlatCluster cluster
  | ToFlatCluster tp outs ops <- toFlatCluster' cluster
  , DeclareVars lhs k values <- declareVars tp
  , values' <- values weakenId
  = FlatCluster lhs
    (mapTupR
      (\(OutShape idx) -> OutShape $ fromMaybe (internalError "Out impossible") $ strengthenWithLHS lhs idx)
      $ outs (ToFlatIdxEqual . weaken k) values'
    )
    $ ops (ToFlatIdxEqual . weaken k) values'
toFlatCluster' :: Cluster op f -> ToFlatCluster op (FunToEnv f)
toFlatCluster' (Fused fusion l r)
  | ToFlatCluster tp1 o1 l' <- toFlatCluster' l
  , ToFlatFusion  tp2 o2 kLeft kRight <- travFusion fusion
  , ToFlatCluster tp3 o3 r' <- toFlatCluster' r
  = case (tp1, tp2, tp3) of
      (_, TupRunit, TupRunit) ->
        ToFlatCluster tp1
          (\k value -> o1 (kLeft k TupRunit) value)
          $ \k value ->
            l' (kLeft k TupRunit) value ++ r' (kRight k TupRunit) TupRunit
      (TupRunit, _, TupRunit) ->
        ToFlatCluster tp2
          (\k _ -> o2 k)
          $ \k value ->
            l' (kLeft k value) TupRunit ++ r' (kRight k value) TupRunit
      (TupRunit, TupRunit, _) ->
        ToFlatCluster tp3
          (\k value -> o3 (kRight k TupRunit) value)
          $ \k value ->
            l' (kLeft k TupRunit) TupRunit ++ r' (kRight k TupRunit) value
      -- This last case is the generic case. Only having this case would be
      -- sufficient, but the prior cases just prevent that we put many many
      -- TupRunits in the type.
      _ ->
        ToFlatCluster
          (tp1 `TupRpair` tp2 `TupRpair` tp3)
          (\k value -> case value of
            v1 `TupRpair` v2 `TupRpair` v3 ->
              o1 (kLeft k v2) v1 `TupRpair` o2 k `TupRpair` o3 (kRight k v2) v3
            _ -> internalError "Pair impossible"
          )
          $ \k value -> case value of
            v1 `TupRpair` v2 `TupRpair` v3 ->
              l' (kLeft k v2) v1 ++ r' (kRight k v2) v3
            _ -> internalError "Pair impossible"
  where
    travFusion :: Fusion largs rargs args -> ToFlatFusion (FunToEnv args) (FunToEnv largs) (FunToEnv rargs)
    travFusion EmptyF = ToFlatFusion TupRunit (const TupRunit) (\_ _ -> \case {}) (\_ _ -> \case {})
    travFusion (IntroI1 f) = travFusion (IntroL f)
    travFusion (IntroI2 f) = travFusion (IntroR f)
    travFusion (IntroO1 f) = travFusion (IntroL f)
    travFusion (IntroO2 f) = travFusion (IntroR f)
    travFusion (IntroL f)
      | ToFlatFusion tp outs l r <- travFusion f
      = ToFlatFusion tp (\k -> outs (succ k))
        (\k value -> \case
          ZeroIdx -> k ZeroIdx
          SuccIdx idx -> l (succ k) value idx
        )
        (\k value -> r (succ k) value)
    travFusion (IntroR f)
      | ToFlatFusion tp outs l r <- travFusion f
      = ToFlatFusion tp (\k -> outs (succ k))
        (\k value -> l (succ k) value)
        (\k value -> \case
          ZeroIdx -> k ZeroIdx
          SuccIdx idx -> r ( succ k) value idx
        )
    travFusion (Horizontal f)
      | ToFlatFusion tp outs l r <- travFusion f
      = ToFlatFusion tp (\k -> outs (succ k))
        (\k value -> \case
          ZeroIdx -> k ZeroIdx
          SuccIdx idx -> l (succ k) value idx
        )
        (\k value -> \case
          ZeroIdx -> k ZeroIdx
          SuccIdx idx -> r (succ k) value idx
        )
    travFusion (Diagonal f)
      | ToFlatFusion tp outs l r <- travFusion f
      = ToFlatFusion tp (\k -> outs (succ k))
        (\k value -> \case
          ZeroIdx -> k ZeroIdx
          SuccIdx idx -> l (succ k) value idx
        )
        (\k value -> \case
          ZeroIdx -> markFused $ k ZeroIdx
          SuccIdx idx -> r (succ k) value idx
        )
    travFusion (Vertical repr f)
      | ToFlatFusion tp outs l r <- travFusion f
      = ToFlatFusion
        (TupRpair tp $ TupRsingle $ OutR repr)
        (\k -> TupRpair (outs $ succ k) $ TupRsingle $ OutShape $ case k ZeroIdx of
          ToFlatIdxEqual idx' -> idx'
        )
        (\k value -> case value of
          TupRpair v1 (TupRsingle v2) -> \case
            ZeroIdx -> ToFlatIdxEqual $ varIdx v2
            SuccIdx idx -> l (succ k) v1 idx
          _ -> internalError "Pair impossible"
        )
        (\k value -> case value of
          TupRpair v1 (TupRsingle v2) -> \case
            ZeroIdx -> ToFlatIdxFused $ varIdx v2
            SuccIdx idx -> r (succ k) v1 idx
          _ -> internalError "Pair impossible"
        )

    succ :: FlattenEnv (env, t) env' -> FlattenEnv env env'
    succ f = f . SuccIdx

    markFused :: ToFlatIdx env (Out sh e) -> ToFlatIdx env (In sh e)
    markFused (ToFlatIdxEqual idx) = ToFlatIdxFused idx
toFlatCluster' (SingleOp (Single op args) _)
  | ToFlatArgs tp outs args' <- travArgs args
  = ToFlatCluster tp (\k _ -> outs k) $ \k values -> [FlatOp op $ args' k values]
  where
    travArgs :: ClusterArgs env f -> ToFlatArgs env f
    travArgs ArgsNil = ToFlatArgs TupRunit (const TupRunit) $ \_ _ -> ArgsNil
    travArgs (a :>: as) = case (travArg a, travArgs as) of
      (ToFlatArg TupRunit _ a', ToFlatArgs tp outs as') ->
        ToFlatArgs tp outs $ \k values -> a' k TupRunit :>: as' k values
      (ToFlatArg tp outs a', ToFlatArgs TupRunit _ as') ->
        ToFlatArgs tp outs $ \k values -> a' k values :>: as' k TupRunit
      (ToFlatArg t1 o1 a', ToFlatArgs t2 o2 as') ->
        ToFlatArgs (TupRpair t1 t2) (\k -> o1 k `TupRpair` o2 k)
          $ \k values -> case values of
            TupRpair v1 v2 -> a' k v1 :>: as' k v2
            TupRsingle _ -> internalError "Pair impossible"

    travArg :: ClusterArg env t -> ToFlatArg env t
    travArg (ClusterArgSingle idx) = ToFlatArg TupRunit (const TupRunit)
      $ \k _ -> case k idx of
        ToFlatIdxEqual idx' -> FlatArgSingle idx'
        ToFlatIdxFused _ -> internalError "In argument not allowed in ClusterArgSingle"
    travArg (ClusterArgArray m shr tp bs)
      | ToFlatArgBuffers fusedR outs f <- travBuffers shr bs
      = ToFlatArg fusedR outs $ \k values -> FlatArgArray m shr tp $ f k values

    travBuffers :: ShapeR sh -> ClusterArgBuffers env m sh t -> ToFlatArgBuffers env m sh t
    travBuffers shr (ClusterArgBuffersPair b1 b2) = case (travBuffers shr b1, travBuffers shr b2) of
      (ToFlatArgBuffers TupRunit _ f1, ToFlatArgBuffers tp outs f2) ->
        ToFlatArgBuffers tp outs $ \k values -> f1 k TupRunit `FlatArgBuffersPair` f2 k values
      (ToFlatArgBuffers tp outs f1, ToFlatArgBuffers TupRunit _ f2) ->
        ToFlatArgBuffers tp outs $ \k values -> f1 k values `FlatArgBuffersPair` f2 k TupRunit
      (ToFlatArgBuffers t1 o1 f1, ToFlatArgBuffers t2 o2 f2) ->
        ToFlatArgBuffers (TupRpair t1 t2) (\k -> o1 k `TupRpair` o2 k) $ \k values -> case values of
          TupRpair v1 v2 -> f1 k v1 `FlatArgBuffersPair` f2 k v2
          TupRsingle _ -> internalError "Pair impossible"
    travBuffers _   (ClusterArgBuffersLive tp idx) =
      ToFlatArgBuffers TupRunit (const TupRunit) $ \k _ -> case k idx of
        ToFlatIdxEqual idx' -> FlatArgBuffersLive tp idx'
        ToFlatIdxFused idx' -> FlatArgBuffersFused tp idx'
    travBuffers shr (ClusterArgBuffersDead tp idx) =
      ToFlatArgBuffers
        (TupRsingle $ OutR $ ArrayR shr tp)
        (\k -> TupRsingle $ OutShape $ case k idx of
          ToFlatIdxEqual idx' -> idx'
        )
        $ \_ value -> case value of
          TupRsingle var -> FlatArgBuffersLive tp $ varIdx var
