{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE BangPatterns        #-}
{-# LANGUAGE BlockArguments      #-}
{-# LANGUAGE EmptyCase           #-}
{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE FlexibleInstances   #-}
{-# LANGUAGE GADTs               #-}
{-# LANGUAGE InstanceSigs        #-}
{-# LANGUAGE LambdaCase          #-}
{-# LANGUAGE MagicHash           #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE PatternGuards       #-}
{-# LANGUAGE PatternSynonyms     #-}
{-# LANGUAGE RankNTypes          #-}
{-# LANGUAGE RecordWildCards     #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections       #-}
{-# LANGUAGE TypeApplications    #-}
{-# LANGUAGE TypeFamilies        #-}
{-# LANGUAGE TypeFamilyDependencies #-}
{-# LANGUAGE TypeOperators       #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ViewPatterns        #-}
{-# LANGUAGE LambdaCase        #-}

{-# OPTIONS_GHC -fno-warn-name-shadowing #-}
{-# OPTIONS_HADDOCK prune #-}
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

module Data.Array.Accelerate.Interpreter (
  module Data.Array.Accelerate.Interpreter,
  UniformScheduleFun
) where

import Prelude                                                      hiding (take, (!!), sum )
import Data.Array.Accelerate.AST.Partitioned hiding (Empty)
import qualified Data.Array.Accelerate.AST.Partitioned as P
import Data.Array.Accelerate.AST.Operation
import Data.Array.Accelerate.AST.Kernel
import Data.Array.Accelerate.Trafo.Desugar
import Data.Array.Accelerate.Trafo.Operation.Simplify (SimplifyOperation(..), copyOperationsForArray, detectMapCopies)
import qualified Data.Array.Accelerate.Debug.Internal as Debug
import Data.Array.Accelerate.Representation.Array
import Data.Array.Accelerate.Error
import Data.Array.Accelerate.Analysis.Match
import Data.Array.Accelerate.Representation.Ground
import Data.Array.Accelerate.Representation.Type
import Data.Array.Accelerate.Representation.Shape
import Data.Array.Accelerate.Representation.Slice
import Data.Array.Accelerate.AST.Environment hiding (Identity(..))
import Data.Array.Accelerate.Type
import Data.Primitive.Vec
import Data.Primitive.Types
import Data.Primitive.ByteArray
import Formatting hiding (int)
import Data.Text.Lazy.Builder
import Data.Array.Accelerate.Representation.Elt
import Data.Array.Accelerate.Representation.Vec
import Data.Array.Accelerate.Trafo.Exp.Substitution
import Unsafe.Coerce (unsafeCoerce)
import Control.Monad.ST
import Data.Bits
import Data.Array.Accelerate.Backend
import Data.Array.Accelerate.Trafo.Operation.LiveVars
import Data.Array.Accelerate.Trafo.Partitioning.ILP.Graph (MakesILP (..), Information (Info), Var (BackendSpecific), (-?>), fused, infusibleEdges, manifest, LabelledArgOp (LOp)) 
import qualified Data.Array.Accelerate.Trafo.Partitioning.ILP.Graph as Graph
import Data.Array.Accelerate.Trafo.Partitioning.ILP.Labels
import qualified Data.Set as Set
import Data.Array.Accelerate.Trafo.Partitioning.ILP.Solver
import Lens.Micro ((.~), (&))
import Data.Array.Accelerate.Array.Buffer
import Data.Array.Accelerate.Pretty.Operation ( PrettyOp(..) )
import Data.Array.Accelerate.Pretty.Partitioned ()
import Data.Array.Accelerate.Pretty.Schedule
import Data.Array.Accelerate.AST.Idx
import Data.Array.Accelerate.AST.LeftHandSide (lhsToTupR)
import Data.Functor.Identity ( Identity(Identity) )
import Data.Array.Accelerate.AST.Schedule
import Data.Array.Accelerate.AST.Execute

import Control.Concurrent (forkIO)
import Data.IORef
import Control.Concurrent.MVar

import Data.Array.Accelerate.AST.Schedule.Uniform (UniformScheduleFun)
import Data.Array.Accelerate.Trafo.Schedule.Uniform ()
import Data.Array.Accelerate.Pretty.Schedule.Uniform ()
import qualified Data.Array.Accelerate.AST.Schedule.Uniform as S
import qualified Data.Map as M

data Interpreter
instance Backend Interpreter where
  type Schedule Interpreter = UniformScheduleFun
  type Kernel Interpreter = InterpretKernel

-- Overly simplistic datatype: We simply ignore all the functions that don't make sense (e.g. for non-array, non-generate args, or non-input args).
-- We also just use Int->Int for the interpreter now, but should be able to use some type families to construct actual Fun (sh -> sh') functions that match up
-- to the shapes of the array arguments instead. That's not trivial, but it is doable and almost required for the code-generating backends. 
-- Another advantage would be increased typesafety (more obviously correct, etc): Int->Int is horrible in that aspect!
data BackpermutedArg env t = BPA (Arg env t) (Int -> Int)
type BackpermutedArgs env = PreArgs (BackpermutedArg env)
type ToBP' f = Env (BP f)
type ToBP = ToBP' Identity
data BP f a = BP (f a) (Int -> Int)
pattern PushBP :: () => (env' ~ (env, x)) => (Int -> Int) -> x -> ToBP env -> ToBP env'
pattern PushBP f x env = Push env (BP (Identity x) f)
{-# COMPLETE Empty, PushBP #-}
type BPFromArg env = ToBP' (FromArg' env)
newtype FromArg' env a = FromArg (FromArg env a) 
pattern PushBPFA :: () => (e' ~ (e, x)) => (Int -> Int) -> FromArg env x -> BPFromArg env e -> BPFromArg env e'
pattern PushBPFA f x env = Push env (BP (FromArg x) f)
{-# COMPLETE Empty, PushBPFA #-}

pattern PushFA :: () => (e' ~ (e, x)) => FromArg env x -> Env (FromArg' env) e -> Env (FromArg' env) e'
pattern PushFA x env = Push env (FromArg x)
{-# COMPLETE Empty, PushFA #-}
type BackpermutedEnv env = Env (BackpermutedEnvElem env)
data BackpermutedEnvElem env a = BPE (ToArg env a) (Int -> Int)

-- Pushes backpermute information through the cluster and stores it in the arguments, for use at the start of the loop (indexing) and in generates.
makeBackpermuteArg :: Args env args -> Val env -> Cluster' InterpretOp args -> BackpermutedArgs env args
makeBackpermuteArg args env (Cluster' io ast) = let o = getOutputEnv io args
                                                    i = fromAST ast o env
                                                in fromInputEnv io i
  where
    fromAST :: ClusterAST InterpretOp i o -> BackpermutedEnv env o -> Val env -> BackpermutedEnv env i
    fromAST None o _ = o
    fromAST (Bind lhs op ast) o env = let o' = fromAST ast o env 
                                      in lhsArgsEnv lhs o' (onOp op (lhsEnvArgs lhs o') env)

    onOp :: InterpretOp args -> BackpermutedArgs env args -> Val env -> BackpermutedArgs env args
    onOp IBackpermute (BPA f@(ArgFun f') _  :>: BPA i _                           :>: BPA o outF :>: ArgsNil) env =
      let ArgArray In  (ArrayR shr  _) (flip varsGetVal env -> sh ) _ = i
          ArgArray Out (ArrayR shr' _) (flip varsGetVal env -> sh') _ = o in
                       BPA f             id :>: BPA i ({-outF .-} toIndex shr sh . evalFun f' env . fromIndex shr' sh' . outF) :>: BPA o outF :>: ArgsNil
    onOp IGenerate    (BPA f _    :>: BPA o outF :>: ArgsNil) _ =
                       BPA f outF :>: BPA o outF :>: ArgsNil -- important: we store the Int -> Int besides the function argument!
    onOp IMap         (BPA f _  :>: BPA i _ :>: BPA o outF :>: ArgsNil) _ =
                       BPA f id :>: BPA i outF :>: BPA o outF :>: ArgsNil
    onOp IPermute args _ = args
    onOp IFold1 _ _ = undefined

    lhsEnvArgs :: LeftHandSideArgs body env' scope -> BackpermutedEnv env scope -> BackpermutedArgs env body
    lhsEnvArgs Base Empty = ArgsNil
    lhsEnvArgs (Reqr _ t lhs) env = case take' t env of (BPE (ArrArg r sh buf) f, env') -> BPA (ArgArray In r sh buf) f :>: lhsEnvArgs lhs env'
                                                        _ -> error "urk"
    lhsEnvArgs (Make   t lhs) env = case take' t env of (BPE (ArrArg r sh buf) f, env') -> BPA (ArgArray Out r sh buf) f :>: lhsEnvArgs lhs env'
                                                        _ -> error "urk"
    lhsEnvArgs (ExpArg lhs) (Push env (BPE (Others arg) f)) = BPA arg f :>: lhsEnvArgs lhs env
    lhsEnvArgs (Adju lhs) (Push env (BPE (Others arg) f)) = BPA arg f :>: lhsEnvArgs lhs env
    lhsEnvArgs (Ignr lhs) (Push env _) = lhsEnvArgs lhs env

    lhsArgsEnv :: LeftHandSideArgs body env' scope -> BackpermutedEnv env scope -> BackpermutedArgs env body -> BackpermutedEnv env env'
    lhsArgsEnv Base                   _                ArgsNil            = Empty
    lhsArgsEnv (Reqr t1 t2 lhs)       env              (BPA _ f :>: args) = case take' t2 env of (BPE arg          _, env') -> put' t1 (BPE arg f) (lhsArgsEnv lhs env' args)
    lhsArgsEnv (Make t     lhs)       env              (BPA _ f :>: args) = case take' t  env of (BPE (ArrArg r sh buf) _, env') -> Push (lhsArgsEnv lhs env' args) (BPE (OutArg r sh buf) f)
                                                                                                 _ -> error "urk"
    lhsArgsEnv (ExpArg     lhs) (Push env (BPE arg _)) (BPA _ f :>: args) = Push (lhsArgsEnv lhs env  args) (BPE arg f)
    lhsArgsEnv (Adju       lhs) (Push env (BPE arg _)) (BPA _ f :>: args) = Push (lhsArgsEnv lhs env  args) (BPE arg f)
    lhsArgsEnv (Ignr       lhs) (Push env arg)                      args  = Push (lhsArgsEnv lhs env  args) arg

    getOutputEnv :: ClusterIO args i o -> Args env args -> BackpermutedEnv env o
    getOutputEnv P.Empty       ArgsNil           = Empty
    getOutputEnv (Vertical t r io) (ArgVar vars :>: args) = put' t (BPE (ArrArg r (toGrounds vars) (error "accessing a fused away buffer")) id) (getOutputEnv io args) -- there is no buffer!
    getOutputEnv (Input      io) (ArgArray In r sh buf :>: args) = Push (getOutputEnv io args) (BPE (ArrArg r sh buf) id)
    getOutputEnv (Output t s e io) (ArgArray Out r sh buf :>: args) = put' t (BPE (ArrArg (ArrayR (arrayRshape r) e) sh (biggenBuffers s buf)) id) (getOutputEnv io args)
    getOutputEnv (MutPut     io) (arg :>: args) = Push (getOutputEnv io args) (BPE (Others arg) id)
    getOutputEnv (ExpPut'    io) (arg :>: args) = Push (getOutputEnv io args) (BPE (Others arg) id)

    biggenBuffers :: SubTupR e e' -> GroundVars env (Buffers e') -> GroundVars env (Buffers e)
    biggenBuffers SubTupRskip _ = error "accessing a simplified away buffer"
    biggenBuffers SubTupRkeep vars = vars
    biggenBuffers (SubTupRpair _ _) (TupRsingle _) = error "impossible???"
    biggenBuffers (SubTupRpair sl sr) (TupRpair bufl bufr) = TupRpair (biggenBuffers sl bufl) (biggenBuffers sr bufr)

    fromInputEnv :: ClusterIO args input output -> BackpermutedEnv env input -> BackpermutedArgs env args
    fromInputEnv P.Empty       Empty = ArgsNil
    fromInputEnv (Vertical _ _ io) (Push env (BPE (OutArg _ sh _) f)) = BPA (ArgVar (fromGrounds sh)) f :>: fromInputEnv io env
    fromInputEnv (Input    io) (Push env (BPE (ArrArg r sh buf) f)) = BPA (ArgArray In r sh buf) f :>: fromInputEnv io env
    fromInputEnv (Output _ s e io) (Push env (BPE (OutArg r sh buf) f)) = BPA (ArgArray Out (ArrayR (arrayRshape r) (subTupR s e)) sh (subTupR (onBuffers s) buf)) f :>: fromInputEnv io env
    fromInputEnv (MutPut   io) (Push env (BPE (Others arg) f)) = BPA arg f :>: fromInputEnv io env
    fromInputEnv (ExpPut'  io) (Push env (BPE (Others arg) f)) = BPA arg f :>: fromInputEnv io env
    fromInputEnv _ (Push _ (BPE (Others _) _)) = error "Array argument found in Other"

    onBuffers :: SubTupR e e' -> SubTupR (Buffers e) (Buffers e')
    onBuffers SubTupRskip = SubTupRskip
    onBuffers SubTupRkeep = SubTupRkeep
    onBuffers (SubTupRpair l r) = SubTupRpair (onBuffers l) (onBuffers r)

data InterpretOp args where
  IMap         :: InterpretOp (Fun' (s -> t)    -> In sh s -> Out sh  t -> ())
  IBackpermute :: InterpretOp (Fun' (sh' -> sh) -> In sh t -> Out sh' t -> ())
  IGenerate    :: InterpretOp (Fun' (sh -> t)              -> Out sh  t -> ())
  IPermute     :: InterpretOp (Fun' (e -> e -> e)
                              -> Mut sh' e
                              -> Fun' (sh -> PrimMaybe sh')
                              -> In sh e
                              -> ())
  IFold1       :: InterpretOp (Fun' (e -> e -> e) -> In (sh, Int) e -> Out sh e -> ())

instance DesugarAcc InterpretOp where
  mkMap         a b c   = Exec IMap         (a :>: b :>: c :>:       ArgsNil)
  mkBackpermute a b c   = Exec IBackpermute (a :>: b :>: c :>:       ArgsNil)
  mkGenerate    a b     = Exec IGenerate    (a :>: b :>:             ArgsNil)
  mkPermute     a b c d = Exec IPermute     (a :>: b :>: c :>: d :>: ArgsNil)
  mkFold        a Nothing b c = Exec IFold1 (a :>: b :>: c :>:       ArgsNil)
  mkFold        _ (Just _) _ _ = error "didn't implement this yet"
  -- etc, but the rest piggybacks off of Generate for now (see Desugar.hs)

instance SimplifyOperation InterpretOp where
  detectCopy _ IMap (ArgFun f :>: input :>: output :>: ArgsNil)
    = detectMapCopies f input output
  detectCopy matchVars' IBackpermute (ArgFun f :>: input@(ArgArray _ _ sh _) :>: output@(ArgArray _ _ sh' _) :>: ArgsNil)
    | Just Refl <- matchVars'  sh sh'
    , Just Refl <- isIdentity f = copyOperationsForArray input output
  detectCopy _ _ _ = []

instance SLVOperation InterpretOp where
  slvOperation IGenerate = Just $ ShrinkOperation $ \subArgs args@(ArgFun f :>: array :>: ArgsNil) _ -> case subArgs of
    SubArgKeep `SubArgsLive` SubArgKeep `SubArgsLive` SubArgsNil
      -> ShrunkOperation IGenerate args
    SubArgKeep `SubArgsLive` SubArgOut subTup `SubArgsLive` SubArgsNil
      -> ShrunkOperation IGenerate (ArgFun (subTupFun subTup f) :>: array :>: ArgsNil)
    _ `SubArgsLive` SubArgsDead _ -> internalError "At least one output should be preserved"

  slvOperation IMap = Just $ ShrinkOperation $ \subArgs args@(ArgFun f :>: input :>: output :>: ArgsNil) _ -> case subArgs of
    SubArgKeep `SubArgsLive` SubArgKeep `SubArgsLive` SubArgKeep `SubArgsLive` SubArgsNil
      -> ShrunkOperation IMap args
    SubArgKeep `SubArgsLive` SubArgKeep `SubArgsLive` SubArgOut subTup `SubArgsLive` SubArgsNil
      -> ShrunkOperation IMap (ArgFun (subTupFun subTup f) :>: input :>: output :>: ArgsNil)
    _ `SubArgsLive` _ `SubArgsLive` SubArgsDead _ -> internalError "At least one output should be preserved"

  slvOperation IBackpermute = Just $ ShrinkOperation $ \subArgs args@(f :>: ArgArray In (ArrayR shr r) sh buf :>: output :>: ArgsNil) _ -> case subArgs of
    SubArgKeep `SubArgsLive` SubArgKeep `SubArgsLive` SubArgKeep `SubArgsLive` SubArgsNil
      -> ShrunkOperation IBackpermute args
    SubArgKeep `SubArgsLive` SubArgKeep `SubArgsLive` SubArgOut s `SubArgsLive` SubArgsNil
      -> ShrunkOperation IBackpermute (f :>: ArgArray In (ArrayR shr (subTupR s r)) sh (subTupDBuf s buf) :>: output :>: ArgsNil)
    _ `SubArgsLive` _ `SubArgsLive` SubArgsDead _ -> internalError "At least one output should be preserved"
  
  slvOperation _ = Nothing -- TODO write for all constructors, and also, remind @IVO to make SLV support Nothing

data InterpretKernel env where
  InterpretKernel :: Cluster InterpretOp args -> Args env args -> InterpretKernel env

instance NFData' InterpretKernel where
  rnf' (InterpretKernel cluster args) = rnf' cluster `seq` rnfArgs args

instance IsKernel InterpretKernel where
  type KernelOperation InterpretKernel = InterpretOp

  compileKernel = InterpretKernel

instance PrettyKernel InterpretKernel where
  -- PrettyKernelBody provides a Val but prettyOpWithArgs expects a Val', should we change them to have the
  -- same type (either Val or Val'?)
  prettyKernel = PrettyKernelBody False $ \env (InterpretKernel cluster args) -> prettyOpWithArgs env cluster args

-- -2 is left>right, -1 is right>left, n is 'according to computation n' (e.g. Backpermute) 
-- (Note that Labels are uniquely identified by an Int, the parent just gives extra information)
-- Use Output = -3 for 'cannot be fused with consumer', as that is more difficult to express (we don't know the consumer yet)
-- We restrict all the Inputs to >= -2.
data OrderV = OrderIn  Label
            | OrderOut Label
  deriving (Eq, Ord, Show, Read)
pattern InDir, OutDir :: Label -> Graph.Var InterpretOp
pattern InDir  l = BackendSpecific (OrderIn l)
pattern OutDir l = BackendSpecific (OrderOut l)


-- TODO add parallelity (number of virtual threads, or perhaps number of dimensions per thread (0 = one element per thread, 1 = one row per thread, 2= one matrix per thread, etc)) to the backendvar.
-- Assuming statically known array sizes for a moment:
-- Cost function should reward parallelity == array size, or dimensions=0, or ideally dimensions <= min_dimensions_to_saturate_threads which depends on concrete sizes
-- like order, parallelity of arguments need to match for fusion
-- fusing map after fold is possible but costly (if the work of the map is big)
-- fusing backpermute after fold is possible and free, so cost function shouldn't care about parallelity for backpermutes
-- 'number of threads' model also expresses exclusive scans, whereas 'dimensions per thread' is much clearer in every other case.
-- Or can we keep this total size `n` for an exclusive scan from `n` to `n+1` elements? E.g. by returning in the format of scanl' (T2 (init res) last res)).
-- That actually sounds quite neat; follow-up question: Can we fuse the cost of that abstraction away?
-- Alternatively, we could simply have one operation that takes an array and one value, and produces a 1-bigger array prefixed by that value.
--    per inner row
-- this operation would fuse perfectly, and then an exclusive scan is simply an inclusive scan followed by this thing.
-- having a lot of those in one kernel would decrease occupancy a little, but that is okay.
-- conclusion: scan is actually not hard at all, because I can just choose the primitives it consists of.
-- TODO: look at the llvm scan kernels & the scan variations in our interface, and decide on the best combination of primitives
-- candidates: with/without seed, including/excluding the total reduction (4 combinations)
--             map, fold, append, prefix, suffix as auxiliary primitives

-- random note: many utilities such as append/concat would fuse so much better when backed by a simple primitive than when expressed as a generate

-- We will also need to know the total iteration size for a cluster, to evaluate it :)
-- Also, adding some of the above options (append/prefix/suffix), a corollary is that every operation needs to know whether they're `on` for a certain index.
-- i.e. if we fuse append into its two producing maps, the maps will be inactive for half the threads! If we fuse prefix with anything,
-- then the other thing will be inactive for every thread that corresponds to the first element of a row! Unless we have dim/thread>0
instance MakesILP InterpretOp where
  type BackendVar InterpretOp = OrderV
  type BackendArg InterpretOp = Maybe Int
  data BackendClusterArg InterpretOp arg = TODO
  mkGraph IBackpermute (_ :>: ((L _ (_, Set.toList -> lIns)) :>: _)) l@(Label i _) =
    Info
      mempty
      (  inputDirectionConstraint l lIns
      <> c (InDir l) .==. int i) -- enforce that the backpermute follows its own rules, but the output can be anything
      -- <> manifest lIn `impliesBinary` fused lIn l) -- Backpermute cannot diagonally fuse with its input: if you are manifest, you cannot be fused
      -- ^ is not strong enough, see my paper draft :p
      -- Instead, we need restrictions on _every_ Op saying that manifest => order < 0 (and make sure that every order which guarantees full evaluation is < 0).
      (inOutBounds l)
  mkGraph IGenerate _ l = Info mempty mempty (lower (-2) (OutDir l))
  mkGraph IMap (_ :>: L _ (_, Set.toList -> lIns) :>: _ :>: ArgsNil) l =
    Info
      mempty
      (  inputDirectionConstraint l lIns
      <> c (InDir l) .==. c (OutDir l))
      (inOutBounds l)
  mkGraph IPermute (_ :>: L _ (_, Set.toList -> ~[lTarget]) :>: _ :>: L _ (_, Set.toList -> lIns) :>: ArgsNil) l =
    Info
      (  mempty & infusibleEdges .~ Set.singleton (lTarget -?> l)) -- Cannot fuse with the producer of the target array
      (  inputDirectionConstraint l lIns)
      (  lower (-2) (InDir l)
      <> upper (OutDir l) (-3)) -- convention meaning infusible

  mkGraph IFold1 _ _ = undefined

  -- each array argument gets labelled with its order,
  -- this ensures that e.g. multiple inputs of the same array
  -- in different orders won't fuse horizontally, and that
  -- the correct one will be used by each consumer
  labelLabelledArg solution l (L arg@(ArgArray In  _ _ _) al) = LOp arg al . Just $ solution M.! OrderIn  l
  labelLabelledArg solution l (L arg@(ArgArray Out _ _ _) al) = LOp arg al . Just $ solution M.! OrderOut l
  labelLabelledArg _ _ (L arg al) = LOp arg al Nothing

  getClusterArg _ = TODO

  finalize = foldMap $ \l -> timesN (manifest l) .>. c (OutDir l)



instance ShrinkArg (BackendClusterArg InterpretOp) where
  shrinkArg _ _ = TODO
  deadArg _ = TODO

-- | If l and lIn are fused, the out-order of lIn and the in-order of l should match
inputDirectionConstraint :: Label -> [Label] -> Constraint InterpretOp
inputDirectionConstraint l = foldMap $ \lIn ->
                timesN (fused lIn l) .>=. c (InDir l) .-. c (OutDir lIn)
    <> (-1) .*. timesN (fused lIn l) .<=. c (InDir l) .-. c (OutDir lIn)

inOutBounds :: Label -> Bounds InterpretOp
inOutBounds l = lower (-2) (InDir l) <> lower (-2) (OutDir l)

instance NFData' InterpretOp where
  -- InterpretOp is an enumeration without fields,
  -- so WHNF is also normal form.
  --
  rnf' a = a `seq` ()

instance PrettyOp InterpretOp where
  prettyOp IMap         = "map"
  prettyOp IBackpermute = "backpermute"
  prettyOp IGenerate    = "generate"
  prettyOp IPermute     = "permute"
  prettyOp IFold1       = "fold1"

instance Execute UniformScheduleFun InterpretKernel where
  executeAfunSchedule = const $ executeScheduleFun Empty

executeScheduleFun :: Val env -> UniformScheduleFun InterpretKernel env t -> IOFun t
executeScheduleFun env (S.Sbody schedule) = executeSchedule env schedule
executeScheduleFun env (S.Slam lhs fun) = \input -> executeScheduleFun (env `push` (lhs, input)) fun

executeSchedule :: Val env -> S.UniformSchedule InterpretKernel env -> IO ()
executeSchedule !env = \case
  S.Return -> return ()
  S.Alet lhs binding body -> do
    value <- executeBinding env binding
    let env' = env `push` (lhs, value)
    executeSchedule env' body
  S.Effect effect next -> do
    executeEffect env effect
    executeSchedule env next
  S.Acond var true false next -> do
    let value = prj (varIdx var) env
    let branch = if value == 1 then true else false
    executeSchedule env branch
    executeSchedule env next
  S.Awhile io step input next -> do
    executeAwhile env io step (prjVars input env)
    executeSchedule env next
  S.Fork a b -> do
    _ <- forkIO (executeSchedule env b)
    executeSchedule env a

executeBinding :: Val env -> S.Binding env t -> IO t
executeBinding env = \case
  S.Compute expr ->
    return $ evalExp expr env
  S.NewSignal -> do
    mvar <- newEmptyMVar
    return (S.Signal mvar, S.SignalResolver mvar)
  S.NewRef _ -> do
    ioref <- newIORef $ internalError "Illegal schedule: Read from ref without value. Some synchronization might be missing."
    return (S.Ref ioref, S.OutputRef ioref)
  S.Alloc shr tp sh -> do
    let n = size shr $ prjVars sh env
    MutableBuffer buffer <- newBuffer tp n
    return $ Buffer buffer
  S.Use _ _ buffer ->
    return buffer
  S.Unit (Var tp ix) -> do
    mbuffer@(MutableBuffer buffer) <- newBuffer tp 1
    writeBuffer tp mbuffer 0 $ prj ix env
    return $ Buffer buffer
  S.RefRead ref -> do
    let S.Ref ioref = prj (varIdx ref) env
    readIORef ioref

executeEffect :: forall env. Val env -> S.Effect InterpretKernel env -> IO ()
executeEffect env = \case
  S.Exec kernelFun args ->
    executeKernelFun env Empty kernelFun args
  S.SignalAwait signals -> mapM_ await signals
  S.SignalResolve signals -> mapM_ resolve signals
  S.RefWrite ref valueVar -> do
    let S.OutputRef ioref = prj (varIdx ref) env
    let value = prj (varIdx valueVar) env
    writeIORef ioref value
  where
    await :: Idx env S.Signal -> IO ()
    await idx = do
      let S.Signal mvar = prj idx env
      readMVar mvar

    resolve :: Idx env S.SignalResolver -> IO ()
    resolve idx = do
      let S.SignalResolver mvar = prj idx env
      putMVar mvar ()

executeKernelFun :: Val env -> Val kenv -> OpenKernelFun InterpretKernel kenv t -> S.SArgs env t -> IO ()
executeKernelFun env kernelEnv (KernelFunLam KernelArgRscalar{} fun) (S.SArgScalar var :>: args)
  = executeKernelFun env (Push' kernelEnv (prj (varIdx var) env)) fun args
executeKernelFun env kernelEnv (KernelFunLam KernelArgRbuffer{} fun) (S.SArgBuffer _ var :>: args)
  = executeKernelFun env (Push' kernelEnv (prj (varIdx var) env)) fun args
executeKernelFun _   kernelEnv (KernelFunBody (InterpretKernel cluster args)) ArgsNil = evalCluster cluster args kernelEnv

executeAwhile
  :: Val env
  -> S.InputOutputR input output
  -> UniformScheduleFun InterpretKernel env (input -> S.Output PrimBool -> output -> ())
  -> input
  -> IO ()
executeAwhile env io step input = do
  -- Set up the output variables for this iteration (and the input for the next)
  (S.Signal mvarCondition, signalResolverCondition) <- executeBinding env S.NewSignal
  (S.Ref iorefCondition, outputRefCondition) <- executeBinding env $ S.NewRef $ GroundRscalar scalarType
  (output, nextInput) <- bindAwhileIO io

  -- Execute a step
  executeScheduleFun env step input (signalResolverCondition, outputRefCondition) output

  -- Check condition
  readMVar mvarCondition
  condition <- readIORef iorefCondition
  if condition == 1 then
    executeAwhile env io step nextInput
  else
    return ()

bindAwhileIO :: S.InputOutputR input output -> IO (output, input)
bindAwhileIO S.InputOutputRsignal = do
  mvar <- newEmptyMVar
  return (S.SignalResolver mvar, S.Signal mvar)
bindAwhileIO S.InputOutputRref = do
  ioref <- newIORef $ internalError "Illegal schedule: Read from ref without value. Some synchronization might be missing."
  return (S.OutputRef ioref, S.Ref ioref)
bindAwhileIO (S.InputOutputRpair io1 io2) = do
  (output1, input1) <- bindAwhileIO io1
  (output2, input2) <- bindAwhileIO io2
  return ((output1, output2), (input1, input2))
bindAwhileIO S.InputOutputRunit =
  return ((), ())

prjVars :: Vars s env t -> Val env -> t
prjVars TupRunit         _   = ()
prjVars (TupRpair v1 v2) env = (prjVars v1 env, prjVars v2 env)
prjVars (TupRsingle var) env = prj (varIdx var) env

fromArgs :: Int -> Val env -> Args env args -> FromIn env args
fromArgs _ _ ArgsNil = ()
fromArgs i env (ArgVar v :>: args) = (fromArgs i env args, v)
fromArgs i env (ArgExp e :>: args) = (fromArgs i env args, e)
fromArgs i env (ArgFun f :>: args) = (fromArgs i env args, f)
fromArgs i env (ArgArray Mut (ArrayR shr _) sh buf :>: args) = (fromArgs i env args, ArrayDescriptor shr sh buf)
fromArgs i env (ArgArray In (ArrayR shr typer) shv buf :>: args) =
  let buf' = varsGetVal buf env
      sh   = varsGetVal shv env
  in (fromArgs i env args, Value (indexBuffers typer buf' i) (Shape shr sh))
fromArgs i env (ArgArray Out (ArrayR shr _) sh _ :>: args) = (fromArgs i env args, Shape shr (varsGetVal sh env))


evalOp :: Int -> InterpretOp args -> Val env -> BPFromArg env (InArgs args) -> IO (Env (FromArg' env) (OutArgs args))
evalOp _ IMap         env (PushBPFA _ f    (PushBPFA _ (Value x (Shape shr sh)) _)) = pure $ PushFA (Value (evalFun f env x) (Shape shr sh)) Empty
evalOp _ IBackpermute _   (PushBPFA _ _    (PushBPFA _ (Value x _) (PushBPFA _ sh _))) = pure $ PushFA (Value x sh) Empty -- We evaluated the backpermute at the start already, now simply relabel the shape info
evalOp i IGenerate    env (PushBPFA f' f   (PushBPFA _ (Shape shr sh) _)) = pure $ PushFA (Value (evalFun f env $ fromIndex shr sh (f' i)) (Shape shr sh)) Empty -- apply f', the Int->Int backpermute function, to our index before evaluating the generate function.
evalOp i IPermute     env (PushBPFA _ comb (PushBPFA _ target (PushBPFA _ f (PushBPFA _ (Value (e :: e) (Shape shr sh)) _)))) =
  let typer = case comb of
        Lam lhs _ -> lhsToTupR lhs
        _ -> error "impossible; is a function" 
  in
  case evalFun f env (fromIndex shr sh i) of
    -- TODO double check: Is 0 Nothing?
    (0, _) -> pure $ PushFA target Empty
    (1, ((), sh)) -> case target of
      ArrayDescriptor shr shvars bufvars -> do
        let shsize = varsGetVal shvars env
        let j = toIndex shr shsize sh
        let buf = varsGetVal bufvars env
        let buf' = veryUnsafeUnfreezeBuffers @e typer buf
        x <- readBuffers @e typer buf' j
        let x' = evalFun comb env x e
        writeBuffers typer buf' j x'
        return $ PushFA target Empty
    -- How do tags work again? If 'e' is a sum type, does the tag get combined, or does it get its own tag?
    _ -> error "PrimMaybe's tag was non-zero and non-one" 
evalOp _ IFold1 _ _ = undefined

evalCluster :: Cluster InterpretOp args -> Args env args -> Val env -> IO ()
evalCluster (Cluster todoFoldInformation c@(Cluster' io ast)) args env = do
  let bp = makeBackpermuteArg args env c
  doNTimes 
    (iterationsize io args env)
    (\n -> do i <- evalIO1 n io bp env
              o <- evalAST n ast env i
              evalIO2 n io args env o)

-- TODO update when we add folds, reconsider when we add scans that add 1 to the size...
iterationsize :: ClusterIO args i o -> Args env args -> Val env -> Int
iterationsize io args env = case io of
  P.Empty -> error "no size"
  P.Output _ _ _ io' -> case args of ArgArray Out (ArrayR shr _) sh _ :>: args' -> arrsize shr (varsGetVal sh env)
  P.Vertical _ _ io' -> case args of -- skip past this one
    ArgVar _ :>: args' -> iterationsize io' args' env
  P.Input  io'       -> case args of ArgArray In  (ArrayR shr _) sh _ :>: args' -> iterationsize io' args' env   -- -> arrsize shr (varsGetVal sh env)
  P.MutPut io'       -> case args of ArgArray Mut (ArrayR shr _) sh _ :>: args' -> iterationsize io' args' env -- arrsize shr (varsGetVal sh env)
  P.ExpPut' io' -> case args of _ :>: args' -> iterationsize io' args' env -- skip past this one

arrsize :: ShapeR sh -> sh -> Int
arrsize ShapeRz () = 1
arrsize (ShapeRsnoc shr) (sh,x) = x * arrsize shr sh


doNTimes :: Monad m => Int -> (Int -> m ()) -> m ()
doNTimes n f
  | n == 0 = pure ()
  | otherwise = f (n-1) >> doNTimes (n-1) f

evalIO1 :: Int -> ClusterIO args i o -> BackpermutedArgs env args -> Val env -> IO (BPFromArg env i)
evalIO1 _ P.Empty                                         ArgsNil    _ = pure Empty
evalIO1 n (Vertical _ r io) (BPA (ArgVar vars          ) f :>: args) env = PushBPFA f (Shape (arrayRshape r) (varsGetVal vars env)) <$> evalIO1 n io args env
evalIO1 n (Input      io) (BPA (ArgArray In r sh buf ) f :>: args) env = PushBPFA f <$> value                                     <*> evalIO1 n io args env 
  where value = Value <$> indexBuffers' (arrayRtype  r) (varsGetVal buf env) (f n) 
                      <*> pure (Shape   (arrayRshape r) (varsGetVal sh  env))
evalIO1 n (Output _ _ _ io) (BPA (ArgArray Out r sh   _) f :>: args) env = PushBPFA f (Shape (arrayRshape r) (varsGetVal sh env))   <$> evalIO1 n io args env
evalIO1 n (MutPut     io) (BPA (ArgArray Mut r sh buf) f :>: args) env = PushBPFA f (ArrayDescriptor (arrayRshape r) sh buf)      <$> evalIO1 n io args env
evalIO1 n (ExpPut'    io) (BPA (ArgExp e)              f :>: args) env = PushBPFA f e                                             <$> evalIO1 n io args env
evalIO1 n (ExpPut'    io) (BPA (ArgVar e)              f :>: args) env = PushBPFA f e                                             <$> evalIO1 n io args env
evalIO1 n (ExpPut'    io) (BPA (ArgFun e)              f :>: args) env = PushBPFA f e                                             <$> evalIO1 n io args env

evalIO2 :: Int -> ClusterIO args i o -> Args env args -> Val env -> Env (FromArg' env) o -> IO ()
evalIO2 _ P.Empty ArgsNil _ Empty = pure ()
evalIO2 n (Vertical t _ io) (_ :>: args) env (take' t -> (_, o)) = evalIO2 n io args env o
evalIO2 n (Input      io) (_ :>: args) env (PushFA _ o) = evalIO2 n io args env o
evalIO2 n (MutPut     io) (_ :>: args) env (PushFA _ o) = evalIO2 n io args env o
evalIO2 n (ExpPut'     io) (_ :>: args) env (PushFA _ o) = evalIO2 n io args env o
evalIO2 n (Output t s _ io) (ArgArray Out (arrayRtype -> r) _ buf :>: args) env o = let (FromArg (Value x _), o') = take' t o in writeBuffers r (veryUnsafeUnfreezeBuffers r $ varsGetVal buf env) n (subTup s x) >> evalIO2 n io args env o'

evalAST :: forall i o env. Int -> ClusterAST InterpretOp i o -> Val env -> BPFromArg env i -> IO (Env (FromArg' env) o)
evalAST _ None _ Empty = pure Empty
evalAST n None env (PushBPFA _ x i) = flip Push (FromArg x) <$> evalAST n None env i
evalAST n (Bind lhs op ast) env i = do
  let i' = evalLHS1 lhs i env
  o' <- evalOp n op env i'
  let scope = evalLHS2 lhs i env o'
  evalAST n ast env scope

evalLHS1 :: forall body i scope env. LeftHandSideArgs body i scope -> BPFromArg env i -> Val env -> BPFromArg env (InArgs body)
evalLHS1 Base Empty _ = Empty
evalLHS1 (Reqr t _ lhs) i env = let (BP (FromArg x) f, i') = take' t i in PushBPFA f x (evalLHS1 lhs i' env)
evalLHS1 (Make _   lhs) (PushBPFA f x i') env = PushBPFA f x (evalLHS1 lhs i' env)
evalLHS1 (EArg     lhs) (PushBPFA f x i') env = PushBPFA f x (evalLHS1 lhs i' env)
evalLHS1 (FArg     lhs) (PushBPFA f x i') env = PushBPFA f x (evalLHS1 lhs i' env)
evalLHS1 (VArg     lhs) (PushBPFA f x i') env = PushBPFA f x (evalLHS1 lhs i' env)
evalLHS1 (Adju     lhs) (PushBPFA f x i') env = PushBPFA f x (evalLHS1 lhs i' env)
evalLHS1 (Ignr     lhs) (PushBPFA _ _ i') env =               evalLHS1 lhs i' env

evalLHS2 :: LeftHandSideArgs body i scope -> BPFromArg env i -> Val env -> Env (FromArg' env) (OutArgs body) -> BPFromArg env scope
evalLHS2 Base Empty _ Empty = Empty
evalLHS2 (Reqr t1 t2 lhs) i env o = let (x, i') = take' t1 i
                                    in                    put' t2 x       (evalLHS2 lhs i' env o)
evalLHS2 (Make t lhs) (PushBPFA f _ i) env (Push o y)   = put' t (BP y f) (evalLHS2 lhs i  env o)
evalLHS2 (EArg   lhs) (PushBPFA f e i) env           o  = PushBPFA f e    (evalLHS2 lhs i  env o)
evalLHS2 (FArg   lhs) (PushBPFA f e i) env           o  = PushBPFA f e    (evalLHS2 lhs i  env o)
evalLHS2 (VArg   lhs) (PushBPFA f e i) env           o  = PushBPFA f e    (evalLHS2 lhs i  env o)
evalLHS2 (Adju   lhs) (PushBPFA f _ i) env (PushFA m o) = PushBPFA f m    (evalLHS2 lhs i  env o)
evalLHS2 (Ignr   lhs) (PushBPFA f x i) env           o  = PushBPFA f x    (evalLHS2 lhs i  env o)


instance NFData' (Cluster InterpretOp) where
  --TODO

-- Program execution
-- -----------------

-- | Run a complete embedded array program using the reference interpreter.
--

-- run :: forall a. (HasCallStack, Sugar.Arrays a) => Smart.Acc a -> a
-- run _ = unsafePerformIO execute
--   where
--     acc :: PartitionedAcc InterpretOp () (DesugaredArrays (Sugar.ArraysR a))
--     !acc    = undefined -- convertAcc a
--     execute = do
--       Debug.dumpGraph $!! acc
--       Debug.dumpSimplStats
--       res <- phase "execute" Debug.elapsed $ undefined
--       return $ Sugar.toArr $ snd res

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

phase :: Builder -> Format Builder (Double -> Double -> Builder) -> IO a -> IO a
phase n fmt go = Debug.timed Debug.dump_phases (now ("phase " <> n <> ": ") % fmt) go




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

    ArrayInstr (Index buffer) ix -> indexBuffer (groundRelt $ varType buffer) (prj (varIdx buffer) aenv) (evalE ix)
    ArrayInstr (Parameter var) _ -> prj (varIdx var) aenv
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

