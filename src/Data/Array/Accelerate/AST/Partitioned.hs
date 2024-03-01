{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE BangPatterns          #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeApplications #-}

{-# LANGUAGE TypeFamilyDependencies#-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE ViewPatterns #-}
{-# OPTIONS_GHC -Wno-orphans #-}

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
  GroundR(..), GroundsR, GroundVar, GroundVars, NFData'(..), Arg(..),
  AccessGroundR(..),
  PreArgs(..), Args, Modifier(..),
  Exp', Var', Fun', In, Out, Mut
) where

import Data.Array.Accelerate.AST.Idx
import Data.Array.Accelerate.AST.Operation hiding (OperationAcc, OperationAfun)

import Prelude hiding ( take )
import Data.Bifunctor
import Data.Array.Accelerate.Trafo.Desugar (ArrayDescriptor(..))
import Data.Array.Accelerate.Representation.Array (Array, Buffers, ArrayR (..))
import Data.Array.Accelerate.AST.LeftHandSide
import Data.Array.Accelerate.Representation.Shape (ShapeR (..), shapeType)
import Data.Type.Equality
import Unsafe.Coerce (unsafeCoerce)
import Data.Array.Accelerate.Representation.Type (TypeR, TupR (..), mapTupR, Distribute)
import Data.Array.Accelerate.Type (ScalarType (..), SingleType (..), NumType (..), IntegralType (..))
import Data.Array.Accelerate.AST.Environment (Env (..), prj')
import Data.Functor.Identity

import Data.Array.Accelerate.Trafo.Partitioning.ILP.Labels (LabelledArgs, LabelledArg (..), ALabel (..), ELabel (..), Label)
import Data.List (nub, sortOn)
import Lens.Micro (_1)
import qualified Data.Functor.Const as C
import Data.Array.Accelerate.Trafo.Partitioning.ILP.Graph (LabelledArgOp (..), BackendClusterArg, MakesILP (getClusterArg, combineBackendClusterArg), LabelledArgsOp, unOpLabels, BackendCluster)
import Data.Array.Accelerate.Trafo.Operation.LiveVars
import Data.Maybe (fromJust)
import Data.Array.Accelerate.AST.Var (varsType)

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
slvOut (a :>: args)  (SubArgsLive SubArgKeep sas) (Push env x) = case a of
  ArgArray Out _ _ _ -> Push (slvOut args sas env) x
  ArgArray In  _ _ _ -> slvOut args sas (Push env x)
  ArgArray Mut _ _ _ -> slvOut args sas (Push env x)
  ArgVar _ -> slvOut args sas (Push env x)
  ArgFun _ -> slvOut args sas (Push env x)
  ArgExp _ -> slvOut args sas (Push env x)
slvOut _ _ _ = error "not soa'ed"

-- a wrapper around operations which sorts the (term and type level) arguments on global labels, to line the arguments up for Fusion
data SortedOp op args where
  SOp :: SOAOp op args
      -> SortedArgs args sorted
      -> SortedOp op sorted

data SortedArgs args sorted where
  SA :: (forall f. PreArgs f args -> PreArgs f sorted)
     -> (forall f. PreArgs f sorted -> PreArgs f args)
     -> SortedArgs args sorted

-- a wrapper around operations for SOA: each individual buffer from an argument array may fuse differently
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

soaShrink :: forall args expanded f. (forall l r g. f (g l) -> f (g r) -> f (g (l,r))) -> SOAs args expanded -> PreArgs f expanded -> PreArgs f args
soaShrink _ SOArgsNil ArgsNil = ArgsNil
soaShrink f (SOArgsCons soas soa) args = case go soa args of (arg :>: args') -> arg :>: soaShrink f soas args'
  where
    go :: SOA arg appendto result -> PreArgs f result -> PreArgs f (arg -> appendto)
    go SOArgSingle args' = args'
    go (SOArgTup soar soal) args' = case go soal args' of
      argr :>: args'' -> case go soar args'' of
        argl :>: args''' -> f argr argl :>: args'''

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
splitLabelledArgsOp (LOp _ (Arr (TupRsingle _), _) b) = error "pair in single"
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

data Cluster op args where
  Op :: SortedOp op args -> Label -> Cluster op args
  Fused :: Fusion largs rargs args
        -> Cluster op largs
        -> Cluster op rargs
        -> Cluster op args

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

left :: Fusion largs rargs args -> Args env args -> Args env largs
left = left' (\(ArgVar sh) -> ArgArray Out (ArrayR (varsToShapeR sh) er) (mapTupR (\(Var t ix)->Var (GroundRscalar t) ix) sh) er)
  where er = error "accessing fused away array"
left' :: (forall sh e. f (Var' sh) -> f (Out sh e)) -> Fusion largs rargs args -> PreArgs f args -> PreArgs f largs
left' _ EmptyF ArgsNil = ArgsNil
left' k (Vertical arr f) (arg :>: args) = k arg :>: left' k f args
left' k (Horizontal   f) (arg:>:args)   = arg :>: left' k f args
left' k (Diagonal     f) (arg:>:args)   = arg :>: left' k f args
left' k (IntroI1      f) (arg:>:args)   = arg :>: left' k f args
left' k (IntroI2      f) (_  :>:args)   =         left' k f args
left' k (IntroO1      f) (arg:>:args)   = arg :>: left' k f args
left' k (IntroO2      f) (_  :>:args)   =         left' k f args
left' k (IntroL       f) (arg:>:args)   = arg :>: left' k f args
left' k (IntroR       f) (_  :>:args)   =         left' k f args

right :: Fusion largs rargs args -> Args env args -> Args env rargs
right = right' varToIn outToIn
right' :: (forall sh e. f (Var' sh) -> f (In sh e)) -> (forall sh e. f (Out sh e) -> f (In sh e)) -> Fusion largs rargs args -> PreArgs f args -> PreArgs f rargs
right' vi oi EmptyF ArgsNil = ArgsNil
right' vi oi (Vertical arr f) (arg :>: args) = vi arg :>: right' vi oi f args
right' vi oi (Diagonal     f) (arg :>: args) = oi arg :>: right' vi oi f args
right' vi oi (Horizontal   f) (arg :>: args) = arg :>: right' vi oi f args
right' vi oi (IntroI1      f) (_   :>: args) =         right' vi oi f args
right' vi oi (IntroI2      f) (arg :>: args) = arg :>: right' vi oi f args
right' vi oi (IntroO1      f) (_   :>: args) =         right' vi oi f args
right' vi oi (IntroO2      f) (arg :>: args) = arg :>: right' vi oi f args
right' vi oi (IntroL       f) (_   :>: args) =         right' vi oi f args
right' vi oi (IntroR       f) (arg :>: args) = arg :>: right' vi oi f args

varToIn :: Arg env (Var' sh) -> Arg env (In sh e)
varToIn (ArgVar sh) = ArgArray In (ArrayR (varsToShapeR sh) er) (mapTupR (\(Var t ix)->Var (GroundRscalar t) ix) sh) er
  where er = error "accessing fused away array"
outToIn :: Arg env (Out sh e) -> Arg env (In sh e)
outToIn (ArgArray Out x y z) = ArgArray In x y z
inToOut :: Arg env (In sh e) -> Arg env (Out sh e)
inToOut (ArgArray In x y z) = ArgArray Out x y z
varToOut = inToOut . varToIn

both :: (forall sh e. f (Out sh e) -> f (In sh e) -> f (Var' sh)) -> Fusion largs rargs args -> PreArgs f largs -> PreArgs f rargs -> PreArgs f args
both _ EmptyF ArgsNil ArgsNil = ArgsNil
both k (Vertical arr  f) (l:>:ls) (r:>:rs) = k l r :>: both k f ls rs
both k (Diagonal      f) (l:>:ls) (_:>:rs) = l     :>: both k f ls rs
both k (Horizontal    f) (l:>:ls) (_:>:rs) = l     :>: both k f ls rs
both k (IntroI1       f) (l:>:ls)      rs  = l     :>: both k f ls rs
both k (IntroI2       f)      ls  (r:>:rs) = r     :>: both k f ls rs
both k (IntroO1       f) (l:>:ls)      rs  = l     :>: both k f ls rs
both k (IntroO2       f)      ls  (r:>:rs) = r     :>: both k f ls rs
both k (IntroL        f) (l:>:ls)      rs  = l     :>: both k f ls rs
both k (IntroR        f)      ls  (r:>:rs) = r     :>: both k f ls rs


type PartitionedAcc  op = PreOpenAcc  (Clustered op)
type PartitionedAfun op = PreOpenAfun (Clustered op)



data Clustered op args = Clustered (Cluster op args) (BackendCluster op args)


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




data Both f g a = Both (f a) (g a)
fst' (Both x _) = x
snd' (Both _ y) = y

zipArgs :: PreArgs f a -> PreArgs g a -> PreArgs (Both f g) a
zipArgs ArgsNil ArgsNil = ArgsNil
zipArgs (f:>:fs) (g:>:gs) = Both f g :>: zipArgs fs gs

onZipped :: (f a -> f b -> f c) -> (g a -> g b -> g c) -> (Both f g a -> Both f g b -> Both f g c)
onZipped f g (Both fa ga) (Both fb gb) = Both (f fa fb) (g ga gb)

-- assumes that the arguments are already sorted!
fuse :: MakesILP op 
     => LabelledArgs env l -> LabelledArgs env r -> PreArgs f l -> PreArgs f r -> Clustered op l -> Clustered op r
     -> (forall sh e. f (Out sh e) -> f (In sh e) -> f (Var' sh))
     -> (forall args. PreArgs f args -> Clustered op args -> result)
     -> result
fuse labl labr largs rargs (Clustered cl bl) (Clustered cr br) c k = fuse' labl labr (zipArgs largs bl) (zipArgs rargs br) cl cr (onZipped c combineBackendClusterArg) $ \args c' -> k (mapArgs fst' args) (Clustered c' $ mapArgs snd' args)
-- assumes that the arguments are already sorted!
fuse' :: LabelledArgs env l -> LabelledArgs env r -> PreArgs f l -> PreArgs f r -> Cluster op l -> Cluster op r
      -> (forall sh e. f (Out sh e) -> f (In sh e) -> f (Var' sh))
      -> (forall args. PreArgs f args -> Cluster op args -> result)
      -> result
fuse' labl labr largs rargs l r c k = mkFused labl labr $ \f -> k (both c f largs rargs) (Fused f l r)

mkFused :: LabelledArgs env l -> LabelledArgs env r -> (forall args. Fusion l r args -> result) -> result
mkFused ArgsNil ArgsNil k = k EmptyF
mkFused ArgsNil ((L r _) :>: rs) k = mkFused ArgsNil rs $ \f -> k (addright r f)
mkFused (L l _ :>: ls) ArgsNil k = mkFused ls ArgsNil $ \f -> k (addleft l f)
mkFused ((L l (NotArr, _)) :>: ls) rs k = mkFused ls rs $ \f -> k (addleft l f)
mkFused ls ((L r (NotArr, _)) :>: rs) k = mkFused ls rs $ \f -> k (addright r f)
mkFused ((L l (Arr TupRunit, _)) :>: ls) rs k = mkFused ls rs $ \f -> k (addleft l f)
mkFused ls ((L r (Arr TupRunit, _)) :>: rs) k = mkFused ls rs $ \f -> k (addright r f)
mkFused (l'@(L l (Arr (TupRsingle (C.Const (ELabel llab))), _)) :>: ls) (r'@(L r (Arr (TupRsingle (C.Const (ELabel rlab))), _)) :>: rs) k
  | llab == rlab = mkFused ls rs $ \f -> addboth l r f k
  | llab <  rlab = mkFused ls (r':>:rs) $ \f -> k (addleft l f)
  | llab >  rlab = mkFused (l':>:ls) rs $ \f -> k (addright r f)
  | otherwise = error "simple math, the truth cannot be questioned"
mkFused ((L _ (Arr TupRpair{}, _)) :>: _) _ _ = error "not soa'd array"
mkFused _ ((L _ (Arr TupRpair{}, _)) :>: _) _ = error "not soa'd array"

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
singleton l largs op k = mkSOAs (unOpLabels largs) $ \soas ->
  sortArgs (soaExpand splitLabelledArgs soas (unOpLabels largs)) $ \sa@(SA sort _) ->
    k $ Clustered (Op (SOp (SOAOp op soas) sa) l) (mapArgs getClusterArg $ sort $ soaExpand splitLabelledArgsOp soas largs)
-- (subargsId $ sort $ soaExpand splitLabelledArgsOp soas largs)

sortArgs :: LabelledArgs env args -> (forall sorted. SortedArgs args sorted -> r) -> r
sortArgs args k = 
  -- if nub ls /= ls then error "not sure if this works" -- this means that some arguments have identical sets of labels. This should only be a problem if two array arguments share labelsets.
  -- else 
    k $ SA
    (\args -> case argsFromList . map snd . sortOn fst . zip ls  . argsToList $ args of Exists a -> unsafeCoerce a)
    (\srts -> case argsFromList . map snd . sortOn fst . zip ls' . argsToList $ srts of Exists a -> unsafeCoerce a)
  where
    args' = argsToList args
    ls = map (\(Exists (L _ (_,l)))->l) args'
    ls' = map snd $ sortOn fst $ zip ls [1..]

subargsId :: PreArgs f args -> SubArgs args args
subargsId ArgsNil = SubArgsNil
subargsId (_ :>: args) = SubArgsLive SubArgKeep $ subargsId args

-- doesn't actually need the labels, but the only usesite has them already
mkSOAs :: LabelledArgs env args -> (forall expanded. SOAs args expanded -> r) -> r
mkSOAs ArgsNil k = k SOArgsNil
mkSOAs (a:>:args) k = mkSOAs args $ \soas -> mkSOA a $ \soa -> k (SOArgsCons soas soa)

mkSOA :: LabelledArg env arg -> (forall result. SOA arg toappend result -> r) -> r
mkSOA     (L (ArgArray In  (ArrayR shr (TupRpair tl tr)) sh (TupRpair bufl bufr)) (Arr (TupRpair al ar), ls)) k = 
  mkSOA   (L (ArgArray In  (ArrayR shr tr              ) sh bufr                ) (Arr ar              , ls)) $ \soar ->
    mkSOA (L (ArgArray In  (ArrayR shr tl              ) sh bufl                ) (Arr al              , ls)) $ \soal ->
      k (SOArgTup soar soal)
mkSOA     (L (ArgArray Out (ArrayR shr (TupRpair tl tr)) sh (TupRpair bufl bufr)) (Arr (TupRpair al ar), ls)) k = 
  mkSOA   (L (ArgArray Out (ArrayR shr tr              ) sh bufr                ) (Arr ar              , ls)) $ \soar ->
    mkSOA (L (ArgArray Out (ArrayR shr tl              ) sh bufl                ) (Arr al              , ls)) $ \soal ->
      k (SOArgTup soar soal)
mkSOA (L (ArgArray In  _ _ TupRunit    ) _) k = k SOArgSingle
mkSOA (L (ArgArray Out _ _ TupRunit    ) _) k = k SOArgSingle
mkSOA (L (ArgArray In  _ _ TupRsingle{}) _) k = k SOArgSingle
mkSOA (L (ArgArray Out _ _ TupRsingle{}) _) k = k SOArgSingle
mkSOA (L (ArgVar _) _) k = k SOArgSingle
mkSOA (L (ArgExp _) _) k = k SOArgSingle
mkSOA (L (ArgFun _) _) k = k SOArgSingle
mkSOA (L (ArgArray Mut _ _ _) _) k = k SOArgSingle
mkSOA _ _ = error "pair or unit in a tuprsingle somewhere"

instance SLVOperation (Clustered op) where
  slvOperation = const Nothing

outvar :: Arg env (Out sh e) -> Arg env (Var' sh)
outvar (ArgArray Out (ArrayR shr _) sh _) = ArgVar $ groundToExpVar (shapeType shr) sh

instance SLVOperation op => SLVOperation (Cluster op) where
  slvOperation = const Nothing
  -- slvOperation (Op (SOp (SOAOp op soa) sa@(SA sort unsort)) l) = case slvOperation op of
  --   Nothing -> Nothing
  --   Just (ShrinkOperation f) -> Just $ ShrinkOperation $ \sub args' args -> 
  --     sortSub sa sub $ \sortedsub -> soaSub soa sortedsub $ \sub' ->
  --       case f 
  --         sub' 
  --         (shrinkArgs sub' $ soaShrink combine soa $ unsort $ growArgs sub args') 
  --         (soaShrink combine soa $ unsort args) 
  --         of
  --         ShrunkOperation op' args'' -> ShrunkOperation (Op (SOp (SOAOp op' $ _ args'') (SA _sort _unsort)) l) args''

  --   where
  --     sortSub :: SortedArgs big' big -> SubArgs big small ->(forall small'. SubArgs big' small' -> r) -> r
  --     sortSub _ _ k = _
  --     soaSub  :: SOAs       big' big -> SubArgs big small ->(forall small'. SubArgs big' small' -> r) -> r
  --     soaSub _ _ k = _
  --     -- opposite of shrinkArgs
  --     growArgs :: ShrinkArg arg => SubArgs f' f -> PreArgs arg f -> PreArgs arg f'
  --     growArgs = _

  -- slvOperation (Fused f l r) = Just $ fuseSLV f (fromJust $ slvOperation l) (fromJust $ slvOperation r)
  --   where
  --     fuseSLV :: Fusion l r a -> ShrinkOperation (Cluster op) l -> ShrinkOperation (Cluster op) r -> ShrinkOperation (Cluster op) a
  --     fuseSLV f (ShrinkOperation l) (ShrinkOperation r) = ShrinkOperation (\sub args' args -> 
  --       splitslvstuff f sub args' args $
  --         \f' lsub largs' largs rsub rargs' rargs ->
  --           case (l lsub largs' largs, r rsub rargs' rargs) of
  --             (ShrunkOperation lop largs'', ShrunkOperation rop rargs'') -> 
  --               ShrunkOperation (Fused f' lop rop) (both (\x _ -> outvar x) f' largs'' rargs''))

  --     splitslvstuff :: Fusion l r a
  --      -> SubArgs a a'
  --      -> Args env' a'
  --      -> Args env a
  --      -> (forall l' r'. Fusion l' r' a' -> SubArgs l l' -> Args env' l' -> Args env l -> SubArgs r r' -> Args env' r' -> Args env r -> result)
  --      -> result
  --     splitslvstuff EmptyF SubArgsNil ArgsNil ArgsNil k = k EmptyF SubArgsNil ArgsNil ArgsNil SubArgsNil ArgsNil ArgsNil
  --     splitslvstuff f (SubArgsLive (SubArgOut SubTupRskip) subs) args' args k = error "completely removed out arg using subtupr" --splitslvstuff f (SubArgsDead subs) args' args k
  --     splitslvstuff f (SubArgsLive (SubArgOut SubTupRkeep) subs) args' args k = splitslvstuff f (SubArgsLive SubArgKeep subs) args' args k
  --     splitslvstuff f (SubArgsLive (SubArgOut SubTupRpair{}) subs) (arg':>:args') (arg:>:args) k = error "not SOA'd array"
  --     splitslvstuff (Diagonal   f) (SubArgsDead subs) args' (arg@(ArgArray _ r sh _):>:args) k = splitslvstuff (Vertical r f) (SubArgsLive SubArgKeep subs) args' (ArgVar (groundToExpVar (shapeType $ arrayRshape r) sh) :>:args) k
  --     splitslvstuff (IntroO1    f) (SubArgsDead subs) (arg':>:args') (arg:>:args) k = splitslvstuff f subs args' args $ \f lsubs largs' largs rsubs rargs' rargs -> k (IntroL   f) (SubArgsDead lsubs) (arg':>:largs') (arg:>:largs)              rsubs          rargs'         rargs
  --     splitslvstuff (IntroO2    f) (SubArgsDead subs) (arg':>:args') (arg:>:args) k = splitslvstuff f subs args' args $ \f lsubs largs' largs rsubs rargs' rargs -> k (IntroR   f)              lsubs          largs'         largs  (SubArgsDead rsubs) (arg':>:rargs') (arg:>:rargs)
  --     splitslvstuff (IntroL     f) (SubArgsDead subs) (arg':>:args') (arg:>:args) k = error "out in IntroL/R"
  --     splitslvstuff (IntroR     f) (SubArgsDead subs) (arg':>:args') (arg:>:args) k = error "out in IntroL/R"
  --     splitslvstuff (Vertical r  f) (SubArgsLive SubArgKeep subs) (ArgVar arg':>:args') (ArgVar arg:>:args) k = splitslvstuff f subs args' args $ \f lsubs largs' largs rsubs rargs' rargs -> k (Vertical r f) (SubArgsLive SubArgKeep lsubs) (ArgArray Out r sh' buf :>:largs') (ArgArray Out r sh buf :>:largs) (SubArgsLive SubArgKeep rsubs) (ArgArray In r sh' buf :>:rargs') (ArgArray In r sh buf :>:rargs)
  --       where
  --         buf = error "fused away buffer"
  --         sh = expToGroundVar arg
  --         sh' = expToGroundVar arg'
  --     splitslvstuff (Diagonal   f) (SubArgsLive SubArgKeep subs) (arg'@(ArgArray Out r' sh' buf'):>:args') (arg@(ArgArray Out r sh buf):>:args) k = splitslvstuff f subs args' args $ \f lsubs largs' largs rsubs rargs' rargs -> k (Diagonal   f) (SubArgsLive SubArgKeep lsubs) (arg':>:largs') (arg:>:largs) (SubArgsLive SubArgKeep rsubs) (ArgArray In r' sh' buf':>:rargs') (ArgArray In r sh buf:>:rargs)
  --     splitslvstuff (Horizontal f) (SubArgsLive SubArgKeep subs) (arg':>:args') (arg:>:args) k = splitslvstuff f subs args' args $ \f lsubs largs' largs rsubs rargs' rargs -> k (Horizontal f) (SubArgsLive SubArgKeep lsubs) (       arg':>:largs') (       arg:>:largs) (SubArgsLive SubArgKeep rsubs) (      arg':>:rargs') (      arg:>:rargs)
  --     splitslvstuff (IntroI1    f) (SubArgsLive SubArgKeep subs) (arg':>:args') (arg:>:args) k = splitslvstuff f subs args' args $ \f lsubs largs' largs rsubs rargs' rargs -> k (IntroI1    f) (SubArgsLive SubArgKeep lsubs) (       arg':>:largs') (       arg:>:largs)                         rsubs                rargs'               rargs
  --     splitslvstuff (IntroI2    f) (SubArgsLive SubArgKeep subs) (arg':>:args') (arg:>:args) k = splitslvstuff f subs args' args $ \f lsubs largs' largs rsubs rargs' rargs -> k (IntroI2    f)                         lsubs                 largs'                largs  (SubArgsLive SubArgKeep rsubs) (      arg':>:rargs') (      arg:>:rargs)
  --     splitslvstuff (IntroO1    f) (SubArgsLive SubArgKeep subs) (arg':>:args') (arg:>:args) k = splitslvstuff f subs args' args $ \f lsubs largs' largs rsubs rargs' rargs -> k (IntroO1    f) (SubArgsLive SubArgKeep lsubs) (       arg':>:largs') (       arg:>:largs)                         rsubs                rargs'               rargs
  --     splitslvstuff (IntroO2    f) (SubArgsLive SubArgKeep subs) (arg':>:args') (arg:>:args) k = splitslvstuff f subs args' args $ \f lsubs largs' largs rsubs rargs' rargs -> k (IntroO2    f)                         lsubs                 largs'                largs  (SubArgsLive SubArgKeep rsubs) (      arg':>:rargs') (      arg:>:rargs)
  --     splitslvstuff (IntroL     f) (SubArgsLive SubArgKeep subs) (arg':>:args') (arg:>:args) k = splitslvstuff f subs args' args $ \f lsubs largs' largs rsubs rargs' rargs -> k (IntroL     f) (SubArgsLive SubArgKeep lsubs) (       arg':>:largs') (       arg:>:largs)                         rsubs                rargs'               rargs
  --     splitslvstuff (IntroR     f) (SubArgsLive SubArgKeep subs) (arg':>:args') (arg:>:args) k = splitslvstuff f subs args' args $ \f lsubs largs' largs rsubs rargs' rargs -> k (IntroR     f)                         lsubs                 largs'                largs  (SubArgsLive SubArgKeep rsubs) (      arg':>:rargs') (      arg:>:rargs)
