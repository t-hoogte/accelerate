{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilyDependencies#-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ViewPatterns #-}
{-# OPTIONS_GHC -Wno-orphans #-}
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
import Data.Array.Accelerate.Trafo.Desugar (ArrayDescriptor(..))
import Data.Array.Accelerate.Trafo.Operation.Simplify (SimplifyOperation(..))
import Data.Array.Accelerate.Representation.Array (Array, Buffers, ArrayR (..))
import Data.Array.Accelerate.AST.LeftHandSide
import Data.Array.Accelerate.Representation.Shape (ShapeR (..), shapeType, typeShape)
import Data.Type.Equality
import Unsafe.Coerce (unsafeCoerce)
import Data.Array.Accelerate.Representation.Type (TypeR, TupR (..), mapTupR)
import Data.Array.Accelerate.Type (ScalarType (..), SingleType (..), NumType (..), IntegralType (..))
import Data.Array.Accelerate.AST.Environment (Env (..), prj')


import Data.Array.Accelerate.Trafo.Partitioning.ILP.Labels (Labels, LabelledArgs, LabelledArg (..), ALabel (..), ELabel (..), Label(..))
import Data.List (sortOn)
import qualified Data.Functor.Const as C
import Data.Array.Accelerate.Trafo.Partitioning.ILP.Graph (LabelledArgOp (..), BackendClusterArg, MakesILP (..), LabelledArgsOp, BackendCluster)
import Data.Array.Accelerate.Trafo.Operation.LiveVars
import Data.Maybe (fromJust)
import Data.Array.Accelerate.AST.Var (varsType)
import Data.Array.Accelerate.Analysis.Match (matchShapeR)



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
  Single :: op args
         -> SOAs args expanded
         -> SortedArgs expanded sorted
         -> SubArgs sorted live
         -> SingleOp op live

-- this pattern synonym translates between the 'new' ast (above) and the 'old' ast (below):
-- the first constructor of `Cluster` used to be called `Op` and contain an `SLVOp`.
-- todo: slowly change all use sites from the old to the new, and eventually retire the old and this pattern synonym.
{-# COMPLETE Op, Fused #-}
pattern Op :: SLVOp op args -> Label -> Cluster op args
pattern Op slv l <- SingleOp (toOld -> slv) l where
  Op (SLV (SOp (SOAOp op soas) sortedargs) subargs) l = SingleOp (Single op soas sortedargs subargs) l
toOld :: SingleOp op args -> SLVOp op args
toOld (Single op soas sortedargs subargs) = SLV (SOp (SOAOp op soas) sortedargs) subargs

data SLVOp op args where
  SLV :: SortedOp op big
      -> SubArgs big small
      -> SLVOp op small

data SortedOp op args where
  SOp :: SOAOp op args
      -> SortedArgs args sorted
      -> SortedOp op sorted

data SortedArgs args sorted where
  SA :: (forall f. PreArgs f args -> PreArgs f sorted)
     -> (forall f. PreArgs f sorted -> PreArgs f args)
     -> SortedArgs args sorted

data SOAOp op args where
  SOAOp :: op args
        -> SOAs args expanded
        -> SOAOp op expanded

data SOAs args expanded where
  SOArgsNil :: SOAs () ()
  SOArgsCons :: SOAs args expanded -> SOA arg expanded both -> SOAs (arg -> args) both

data SOA arg appendto result where
  SOArgSingle :: SOA arg args (arg -> args)
  SOArgTup :: SOA (f right) args args' -> SOA (f left) args' args'' -> SOA (f (left,right)) args args''



-- These correspond to the inference rules in the paper
-- datatype describing how to combine the arguments of two fused clusters
data Fusion largs rars args where
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
  IntroL :: Fusion l r a -> Fusion (x -> l) r (x -> a)
  IntroR :: Fusion l r a -> Fusion l (x -> r) (x -> a)
deriving instance Show (Fusion l r total)


soaShrink :: forall args expanded f
           .
          --  (forall a. Show (f a))
          -- => 
          (forall l r g. f (g l) -> f (g r) -> f (g (l,r)))
          -> SOAs args expanded -> PreArgs f expanded -> PreArgs f args
soaShrink _ SOArgsNil ArgsNil = ArgsNil
soaShrink f (SOArgsCons soas soa) args = case go soa args of (arg :>: args') -> arg :>: soaShrink f soas args'
  where
    go :: SOA arg appendto result -> PreArgs f result -> PreArgs f (arg -> appendto)
    go SOArgSingle args' = args'
    go (SOArgTup soar soal) args' = case go soal args' of
      argl :>: args'' -> case go soar args'' of
        argr :>: args''' -> f argl argr :>: args'''

soaExpand :: forall args expanded f. (forall l r g. f (g (l,r)) -> (f (g l), f (g r))) -> SOAs args expanded -> PreArgs f args -> PreArgs f expanded
soaExpand _ SOArgsNil ArgsNil = ArgsNil
soaExpand f (SOArgsCons soas soa) (arg :>: args) = go soa arg $ soaExpand f soas args
  where
    go :: SOA arg appendto result -> f arg -> PreArgs f appendto -> PreArgs f result
    go SOArgSingle arg appendto = arg :>: appendto
    go (SOArgTup soar soal) arg appendto = let (l,r) = f arg
                                               appendtor = go soar r appendto
                                           in go soal l appendtor


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

soaOut :: forall env args expanded f. (forall sh l r. f (Value sh (l,r)) -> (f (Value sh l),f (Value sh r))) -> Args env args -> SOAs args expanded -> Env f (OutArgs args) -> Env f (OutArgs expanded)
soaOut _ ArgsNil SOArgsNil Empty = Empty
soaOut k (ArgArray Out _ _ _:>:args) (SOArgsCons soas soa) (Push env arg) = go soa arg $ soaOut k args soas env
  where
    go :: SOA (Out sh e) appendto both -> f (Value sh e) -> Env f (OutArgs appendto) -> Env f (OutArgs both)
    go SOArgSingle v appendto = Push appendto v
    go (SOArgTup soar soal) v appendto = go soal (fst $ k v) $ go soar (snd $ k v) appendto
soaOut k (_ :>: args) (SOArgsCons soas soa) env -- we match on 'ArgArray Out' above, so the unsafe calls are fine, because the arg is not an output
  | Refl <- unsafeOutargslemma @args
  , Refl <- unsafeSOAlemma soa = soaOut k args soas env
-- only use if the arg is not Out!
unsafeOutargslemma :: (args' ~ (a -> args)) => OutArgs args' :~: OutArgs args
unsafeOutargslemma = unsafeCoerce Refl
-- only use if the arg is not Out!
unsafeSOAlemma :: SOA arg appendto result -> OutArgs appendto :~: OutArgs result
unsafeSOAlemma = unsafeCoerce Refl

soaIn :: forall f env args expanded. (forall aarrgg l r. Arg env (aarrgg (l,r)) -> f (InArg (aarrgg l)) -> f (InArg (aarrgg r)) -> f (InArg (aarrgg (l,r)))) -> Args env expanded -> SOAs args expanded -> Env f (InArgs expanded) -> Env f (InArgs args)
soaIn _ ArgsNil SOArgsNil Empty = Empty
soaIn k args (SOArgsCons soas soa) expanded = case go args soa expanded of
  (_, v, rest, args') -> Push (soaIn k args' soas rest) v
  where
    go :: Args env result -> SOA arg appendto result -> Env f (InArgs result) -> (Arg env arg, f (InArg arg), Env f (InArgs appendto), Args env appendto)
    go (a:>:args) SOArgSingle (Push env v) = (a, v, env, args)
    go args (SOArgTup soar soal) env = case go args soal env of
      (la, l, env', args') -> case go args' soar env' of
        (ra, r, env'', args'') -> (combine la ra, k (combine la ra) l r, env'', args'')

emptySoaImpossible :: SOA a b () -> anything
emptySoaImpossible (SOArgTup _ soa) = emptySoaImpossible soa




justOut :: Args env args -> PreArgs f args -> PreArgs f (OutArgsOf args)
justOut ArgsNil ArgsNil = ArgsNil
justOut (ArgArray Out _ _ _ :>: args) (arg :>: fs) = arg :>: justOut args fs
justOut (ArgVar _           :>: args) (_   :>: fs) = justOut args fs
justOut (ArgExp _           :>: args) (_   :>: fs) = justOut args fs
justOut (ArgFun _           :>: args) (_   :>: fs) = justOut args fs
justOut (ArgArray In  _ _ _ :>: args) (_   :>: fs) = justOut args fs
justOut (ArgArray Mut _ _ _ :>: args) (_   :>: fs) = justOut args fs



left :: Fusion largs rargs args -> Args env args -> Args env largs
left = left' (\repr (ArgVar sh) -> ArgArray Out repr (mapTupR (\(Var t ix)->Var (GroundRscalar t) ix) sh) er2)
  where
    er1 = error "accessing fused away array1"
    er2 = error "accessing fused away array2"
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
    go (Op s _)      accum = extract s : accum
    go (Fused _ a b) accum = go a $ go b accum

    extract :: SLVOp op args -> Exists op
    extract (SLV (SOp (SOAOp op _) _) _) = Exists op

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

data ToArg env a where
  ArrArg :: ArrayR (Array sh e)
         -> GroundVars env sh
         -> GroundVars env (Buffers e)
         -> ToArg env (Value sh e)
  OutArg :: ArrayR (Array sh e)
         -> GroundVars env sh
         -> GroundVars env (Buffers e)
         -> ToArg env (Sh sh e)
  Others :: String -> Arg env a -> ToArg env a



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
mkFused ArgsNil ((LOp r _ _) :>: rs) k = mkFused ArgsNil rs $ \f -> k (addright r f)
mkFused (LOp l _ _ :>: ls) ArgsNil k = mkFused ls ArgsNil $ \f -> k (addleft l f)
mkFused ((LOp l (NotArr,_) _) :>: ls) rs k = mkFused ls rs $ \f -> k (addleft l f)
mkFused ls ((LOp r (NotArr,_)_ ) :>: rs) k = mkFused ls rs $ \f -> k (addright r f)
mkFused ((LOp l (Arr TupRunit,_)_ ) :>: ls) rs k = mkFused ls rs $ \f -> k (addleft l f)
mkFused ls ((LOp r (Arr TupRunit,_)_) :>: rs) k = mkFused ls rs $ \f -> k (addright r f)
mkFused (l'@(LOp l _ bl) :>: ls) (r'@(LOp r _ br) :>: rs) k
  | Left le <- getElabelForSort $ unOpLabel l'
  , Left re <- getElabelForSort $ unOpLabel r'
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
-- unsafeCoerce convinces the type checker that l and r are on the same array (i.e. both working on the same element type)
addboth (ArgArray In  _ _ _) (ArgArray In  _ _ _) f k = k $ unsafeCoerce $ Horizontal f
addboth (ArgArray Out _ _ _) (ArgArray In  _ _ _) f k = k $ unsafeCoerce $ Diagonal f
addboth (ArgArray Out _ _ _) (ArgArray Out _ _ _) _ _ = error "two producers of the same array"
addboth (ArgArray In  _ _ _) (ArgArray Out _ _ _) _ _ = error "reverse vertical/diagonal"
addboth _ _ _ _ = error "fusing non-arrays"

singleton :: MakesILP op => Label -> LabelledArgsOp op env args -> op args -> (forall args'. Clustered op args' -> r) -> r
singleton l largs op k = mkSOAs (mapArgs (\(LOp a _ _) -> a) largs) $ \soas ->
  sortArgs (soaExpand splitLabelledArgs soas (unOpLabels' largs)) $ \sa@(SA sort _) slv ->
    k $ Clustered (Op (SLV (SOp (SOAOp op soas) sa) slv) l) (mapArgs getClusterArg $ sort $ soaExpand splitLabelledArgsOp soas largs)
-- (subargsId $ sort $ soaExpand splitLabelledArgsOp soas largs)

sortArgs :: LabelledArgs env args -> (forall sorted. SortedArgs args sorted -> SubArgs sorted sorted -> r) -> r
sortArgs args k =
    k (SA
        sort
        unsort)
      (keepAll $ sort args)
  where
    sort :: PreArgs f args -> PreArgs f sorted
    sort   args = case argsFromList . map snd . sortOn fst . zip ls  . argsToList $ args of Exists a -> unsafeCoerce a
    unsort :: PreArgs f sorted -> PreArgs f args
    unsort srts = case argsFromList . map snd . sortOn fst . zip ls' . argsToList $ srts of Exists a -> unsafeCoerce a
    args' = argsToList args
    ls = map (\(Exists l) -> getElabelForSort l) args'
    ls' = map snd $ sortOn fst $ zip ls [1 :: Int ..]
    keepAll :: LabelledArgs env args -> SubArgs args args
    keepAll ArgsNil = SubArgsNil
    keepAll (_:>:as) = SubArgKeep `SubArgsLive` keepAll as
-- If it's a buffer, we only care about its unique label. If it's not a buffer, the other labels suffice to give any ordering.
getElabelForSort :: LabelledArg env a -> Either ELabel Labels
getElabelForSort (L (ArgArray m (ArrayR _ TupRsingle{}) _ _) (Arr (TupRsingle (C.Const e)),_))
  | In  <- m = Left e
  | Out <- m = Left e
getElabelForSort (L _ (_,ls)) = Right ls




subargsId :: PreArgs f args -> SubArgs args args
subargsId ArgsNil = SubArgsNil
subargsId (_ :>: args) = SubArgsLive SubArgKeep $ subargsId args

mkSOAs :: Args env args -> (forall expanded. SOAs args expanded -> r) -> r
mkSOAs ArgsNil k = k SOArgsNil
mkSOAs (a:>:args) k = mkSOAs args $ \soas -> mkSOA a $ \soa -> k (SOArgsCons soas soa)

mkSOA :: Arg env arg -> (forall result. SOA arg toappend result -> r) -> r
mkSOA     (ArgArray In  (ArrayR shr (TupRpair tl tr)) sh (TupRpair bufl bufr)) k =
  mkSOA   (ArgArray In  (ArrayR shr tr              ) sh bufr                ) $ \soar ->
    mkSOA (ArgArray In  (ArrayR shr tl              ) sh bufl                ) $ \soal ->
      k (SOArgTup soar soal)
mkSOA     (ArgArray Out (ArrayR shr (TupRpair tl tr)) sh (TupRpair bufl bufr)) k =
  mkSOA   (ArgArray Out (ArrayR shr tr              ) sh bufr                ) $ \soar ->
    mkSOA (ArgArray Out (ArrayR shr tl              ) sh bufl                ) $ \soal ->
      k (SOArgTup soar soal)
mkSOA (ArgArray In  _ _ TupRunit    ) k = k SOArgSingle
mkSOA (ArgArray Out _ _ TupRunit    ) k = k SOArgSingle
mkSOA (ArgArray In  _ _ TupRsingle{}) k = k SOArgSingle
mkSOA (ArgArray Out _ _ TupRsingle{}) k = k SOArgSingle
mkSOA (ArgVar _) k = k SOArgSingle
mkSOA (ArgExp _) k = k SOArgSingle
mkSOA (ArgFun _) k = k SOArgSingle
mkSOA (ArgArray Mut _ _ _) k = k SOArgSingle
mkSOA _ _ = error "pair or unit in a tuprsingle somewhere"

instance ShrinkArg (BackendClusterArg op) => SLVOperation (Clustered op) where
  slvOperation (Clustered cluster b) = Just $ ShrinkOperation $ \ff' a' a ->
    case slvCluster cluster ff' a' a of
      ShrunkOperation' cluster' args ->
        ShrunkOperation (Clustered cluster' $ shrinkArgs ff' b) args

instance SimplifyOperation (Clustered op)
  -- Default implementation, where detectCopy always returns []

-- instance SLVOperation (Cluster op) where
--   slvOperation cluster = -- Nothing
--     Just $ ShrinkOperation $ \sub args' args ->
--       case slvCluster cluster sub args' args of
--         ShrunkOperation' cluster' args'' -> ShrunkOperation cluster' args''

slvCluster :: Cluster op f -> SubArgs f f' -> Args env' f' -> Args env f -> ShrunkOperation' (Cluster op) env' f'
slvCluster (Op op label) sub args' _
  -- | ShrunkOperation' op' subargs <- undefined op sub args'
  | op' <- slvSLVOp op sub
  = ShrunkOperation' (Op op' label) args'
  where
    slvSLVOp :: SLVOp op big -> SubArgs big small -> SLVOp op small
    slvSLVOp (SLV op sa1) sa2 = SLV op (composeSubArgs sa1 sa2)

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

-- slvSLVedOp :: SLVedOp op f -> SubArgs f f' -> Args env' f' -> ShrunkOperation' (SLVedOp op) env' f'
-- slvSLVedOp (SLVOp op subargs) sub args' = ShrunkOperation' (SLVOp op $ composeSubArgs subargs sub) args'

-- instance SLVOperation (SLVedOp op) where
--   slvOperation (SLVOp op subargs) = Just $ ShrinkOperation (\sub args' _ -> ShrunkOperation (SLVOp op $ composeSubArgs subargs sub) args')






outvar :: Arg env (Out sh e) -> Arg env (Var' sh)
outvar (ArgArray Out (ArrayR shr _) sh _) = ArgVar $ groundToExpVar (shapeType shr) sh

varout :: Arg env (Var' sh) -> Arg env (Out sh e)
varout (ArgVar sh) = ArgArray Out (ArrayR (fromJust $ typeShape $ varsType sh) (error "fake")) (expToGroundVar sh) (error "fake")


slv  :: (forall sh e. f (Out sh e) -> f (Var' sh)) -> SubArgs args args' -> PreArgs f args -> PreArgs f args'
slv _ SubArgsNil ArgsNil = ArgsNil
slv f (SubArgsDead    sas) (arg:>:args) = f arg :>: slv f sas args
slv f (SubArgsLive SubArgKeep sas) (arg:>:args) = arg :>: slv f sas args
slv _ _ _ = error "not soa'ed"
slv' :: (forall sh e. f (Var' sh) -> f (Out sh e)) -> SubArgs args args' -> PreArgs f args' -> PreArgs f args
slv' _ SubArgsNil ArgsNil = ArgsNil
slv' f (SubArgsDead    sas) (arg:>:args) = f arg :>: slv' f sas args
slv' f (SubArgsLive SubArgKeep sas) (arg:>:args) = arg :>: slv' f sas args
slv' _ _ _ = error "not soa'ed"
slvIn  :: (forall sh e. f (Var' sh) -> f (Sh sh e)) -> SubArgs args args' -> Env f (InArgs args') -> Env f (InArgs args)
slvIn _ SubArgsNil Empty = Empty
slvIn f (SubArgsDead    sas) (Push env x) = Push (slvIn f sas env) (f    x)
slvIn f (SubArgsLive SubArgKeep sas) (Push env x) = Push (slvIn f sas env) x
slvIn _ _ _ = error "not soa'ed"
slvOut :: Args env args' -> SubArgs args args' -> Env f (OutArgs args) -> Env f (OutArgs args')
slvOut _ SubArgsNil Empty = Empty
slvOut (_:>:args) (SubArgsDead    sas) (Push env _) = slvOut args sas env
slvOut (a :>: args)  (SubArgsLive SubArgKeep sas) env = case a of
  ArgArray Out _ _ _
    | Push env' x <- env -> Push (slvOut args sas env') x
  ArgArray In  _ _ _ -> slvOut args sas env
  ArgArray Mut _ _ _ -> slvOut args sas env
  ArgVar _ -> slvOut args sas env
  ArgFun _ -> slvOut args sas env
  ArgExp _ -> slvOut args sas env
slvOut _ _ _ = error "not soa'ed"


showSorted :: LabelledArgsOp op env args -> String
showSorted ArgsNil = ""
showSorted (a :>: args) = case a of
  LOp (ArgArray m _ _ _) (_,ls) _ -> show m <> "{" <> show ls <> "}" <> showSorted args
  _ -> showSorted args
