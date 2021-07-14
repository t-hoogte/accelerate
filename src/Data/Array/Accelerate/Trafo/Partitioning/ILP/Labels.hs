{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE EmptyCase #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE ViewPatterns #-}
module Data.Array.Accelerate.Trafo.Partitioning.ILP.Labels where


-- accelerate imports
import Data.Array.Accelerate.AST.Idx ( Idx, pattern ZeroIdx, pattern SuccIdx, pattern VoidIdx )
import Data.Array.Accelerate.AST.LeftHandSide ( LeftHandSide(..) )
import Data.Array.Accelerate.AST.Operation
import Data.Array.Accelerate.Representation.Type ( TupR(..) )

-- In this file, order very often subly does matter.
-- To keep this clear, we use S.Set whenever it does not,
-- and [] only when it does. It's also often efficient
-- by removing duplicates.
import qualified Data.Set as S

import Lens.Micro.TH ( makeLenses )
import Control.Monad.State ( (>=>), State )
import Lens.Micro.Mtl ((<%=))
import qualified Data.Map as M
import Lens.Micro ((^.))
import Data.Bifunctor (first)

{-
Label is for each AST node: every exec, every let, every branch of control flow, etc has a unique label.
Edge is a dependency between Labels

ELabel is for Environments: the environment consists of array-level and expression-level values (right?),
we give each value a unique ELabel. This helps to re-index AST nodes and expressions and args into the new environment,
provided that we have a LabelEnv with matching ELabels...
LabelEnv also has a S.Set Label for each value, denoting the current outgoing edges from that value: This is volatile information, while all the rest is static.

LabelArgs is the same as LabelEnv, except it is bound to Args. The ELabels in here point to the ELabels in Env
-}




-- identifies nodes with unique Ints. and tracks their dependencies
-- `Label x Nothing` means that label x is top-level.
-- `Label x (Just y)` means that label x is (at ilp-construction time determined to be) a subcomputation of label y
-- Invariant: for all x, there is at most one `Label x _`: the second field is not to discriminate vars but to log extra information.
data Label = Label
  { _labelId :: Int
  , _parent :: Maybe Label
  } deriving (Eq, Ord, Show, Read)
makeLenses ''Label

level :: Label -> Int
level (Label _ Nothing)  = 0
level (Label _ (Just l)) = 1 + level l

type Labels = S.Set Label
type ELabels = (ELabel, Labels)
data ALabel t where
  Arr :: ELabel -- buffer
     -- -> ELabel -- shape
      -> ALabel (m sh e) -- only matches on arrays, but supports In, Out and Mut
  NotArr :: ALabel (t e) -- matches on `Var' e`, `Exp' e` and `Fun' e` 

type ALabels t = (ALabel t, Labels) -- An ELabel if it corresponds to an array, otherwise Nothing

-- Map identifiers to labels
labelMap :: S.Set Label -> M.Map Int Label
labelMap = M.fromDistinctAscList . map (\l -> (l^.labelId, l)) . S.toAscList

-- identifies elements of the environment with unique Ints.
newtype ELabel = ELabel { runELabel :: Int }
  deriving (Show, Eq, Ord, Num)

-- | Keeps track of which argument belongs to which labels
data LabelledArg  env a = L (Arg env a) (ALabels a)
type LabelledArgs env = PreArgs (LabelledArg env)

instance Semigroup (LabelledArgs env args) where
  ArgsNil <> ArgsNil = ArgsNil
  (arg `L` (NotArr,l1)):>:largs1 <> (_ `L` (larg,   l2)):>:largs2 = arg `L` (larg, l1<>l2) :>: (largs1 <> largs2)
  (arg `L` (larg,  l1)):>:largs1 <> (_ `L` (NotArr, l2)):>:largs2 = arg `L` (larg, l1<>l2) :>: (largs1 <> largs2)
  _ <> _ = error "mappend for LabelArgs found two Arr labels"

unLabel :: LabelledArgs env args -> Args env args
unLabel ArgsNil              = ArgsNil
unLabel (arg `L` _ :>: args) = arg :>: unLabel args


-- | Keeps track of which array in the environment belongs to which label
data LabelEnv env where
  LabelEnvNil  :: LabelEnv ()
  (:>>>:)      :: ELabels -> LabelEnv t -> LabelEnv (t, s)
instance Semigroup (LabelEnv env) where
  LabelEnvNil <> LabelEnvNil = LabelEnvNil
  (e1,l1):>>>:lenv1 <> (e2,l2):>>>:lenv2
    | e1 == e2 = (e1, l1<>l2) :>>>: (lenv1 <> lenv2)
    | otherwise = error "mappend for LabelEnv found two different labels"

freshE' :: State ELabel ELabel
freshE' = id <%= (+1)


-------------------------------
-- Traversals over stuff to add/extract Labels and ELabels,
-- or otherwise manipulate LabelArgs' or LabelEnvs


-- | Note that this throws some info away: Pair (Wildcard, Single) and Pair (Single, Wildcard) give identical results.
-- Use sites need to store the LHS itself too.
addLhs :: LeftHandSide s v env env' -> Labels -> LabelEnv env -> State ELabel (LabelEnv env')
addLhs LeftHandSideWildcard{} _ = pure
addLhs LeftHandSideSingle{}   l = \lenv -> freshE' >>= \e -> pure ((e, l) :>>>: lenv)
addLhs (LeftHandSidePair x y) l = addLhs x l >=> addLhs y l


weakLhsEnv :: LeftHandSide s v env env' -> LabelEnv env' -> LabelEnv env
weakLhsEnv LeftHandSideSingle{} (_:>>>: env) = env
weakLhsEnv LeftHandSideWildcard{} env = env
weakLhsEnv (LeftHandSidePair l r) env = weakLhsEnv l (weakLhsEnv r env)

emptyLabelEnv :: LabelEnv env -> LabelEnv env
emptyLabelEnv LabelEnvNil = LabelEnvNil
emptyLabelEnv ((e,_):>>>:env) = (e, mempty) :>>>: emptyLabelEnv env

getAllLabelsEnv :: LabelEnv env -> Labels
getAllLabelsEnv LabelEnvNil = mempty
getAllLabelsEnv ((_,set) :>>>: lenv) = set <> getAllLabelsEnv lenv

getLabelArgs :: Args env args -> LabelEnv env -> LabelledArgs env args
getLabelArgs ArgsNil _ = ArgsNil
getLabelArgs (arg :>: args) e = arg `L` getLabelsArg arg e :>: getLabelArgs args e

getLabelsArg :: Arg env t -> LabelEnv env -> ALabels t
getLabelsArg (ArgVar tup)                  env = (\(Left x) -> x) $ getLabelsTup tup    env
getLabelsArg (ArgExp expr)                 env = getLabelsExp expr   env
getLabelsArg (ArgFun fun)                  env = getLabelsFun fun    env
-- TODO this gets us the singleton label assigned to the buffer, check whether this doesn't make us use/write an array before we know its size
-- honestly, this just doesn't cut it. Need a better way to both label arguments (for reconstruction later) and track dependencies (for ILP solving),
-- using this one S.Set for both conflicts (as seen in 'const' vs 'insert')
getLabelsArg (ArgArray _ _ shVars buVars) env = let Left (NotArr, shLabs) = getLabelsTup shVars env
                                                    Right (Arr x,     buLabs) = getLabelsTup buVars env
                                                in (Arr x, shLabs <> buLabs)

getLabelsTup :: TupR (Var a env) b -> LabelEnv env -> Either (ALabels (Var' b)) (ALabels (m sh b))
getLabelsTup TupRunit         _   = Left (NotArr, mempty)
getLabelsTup (TupRsingle var) env = Right $ getLabelsVar var env
getLabelsTup (TupRpair x y)   env = case (getLabelsTup x env, getLabelsTup y env) of
  (Left  (_, a), Left  (_, b)) -> Left (NotArr, a <> b)
  (Left  (_, a), Right (Arr z, b)) -> Right (Arr z, a <> b)
  (Right (Arr z, a), Left  (_, b)) -> Right (Arr z, a <> b)
  (Right (_, a), Right (_, b)) -> Left (NotArr, a <> b)
  _ -> error "who?"


getLabelsVar :: Var s env t -> LabelEnv env -> ALabels (m sh t)
getLabelsVar (varIdx -> idx) = getLabelsIdx idx

getLabelsIdx :: Idx env a -> LabelEnv env -> ALabels (m sh a)
getLabelsIdx ZeroIdx (el :>>>: _) = first Arr el
getLabelsIdx (SuccIdx idx) (_ :>>>: env) = getLabelsIdx idx env

getELabelIdx :: Idx env a -> LabelEnv env -> ELabel
getELabelIdx ZeroIdx ((e,_) :>>>: _) = e
getELabelIdx (SuccIdx idx) (_ :>>>: env) = getELabelIdx idx env

getLabelsExp :: OpenExp x env y -> LabelEnv env -> ALabels (Exp' y)
getLabelsExp = undefined -- TODO traverse everything, look for Idxs

getLabelsFun :: OpenFun x env y -> LabelEnv env -> ALabels (Fun' y)
getLabelsFun (Body expr) lenv = first body $ getLabelsExp expr lenv
getLabelsFun (Lam _ fun) lenv = first lam  $ getLabelsFun fun  lenv

updateLabelEnv :: Args env args -> LabelEnv env -> Label -> LabelEnv env
updateLabelEnv ArgsNil lenv _ = lenv
updateLabelEnv (arg :>: args) lenv l = case arg of
  -- CHECK we only look at the 'Buffer' vars here, not the 'shape' ones. Is that ok?
  ArgArray Out _ _ vars -> updateLabelEnv args (insertAtVars vars lenv $ S.insert l) l
  ArgArray Mut _ _ vars -> updateLabelEnv args (insertAtVars vars lenv $ S.insert l) l
  -- TODO maybe we should also traverse the other args? Does LabelEnv need two sets of Labels (potentially fusible & infusible)?
  _ -> updateLabelEnv args lenv l

-- Updates the labels with a function. In practice, this is either `S.insert l` or `const (S.singleton l)`
insertAtVars :: TupR (Var a env) b -> LabelEnv env -> (Labels -> Labels) -> LabelEnv env
insertAtVars TupRunit lenv _ = lenv
insertAtVars (TupRpair x y) lenv f = insertAtVars x (insertAtVars y lenv f) f
insertAtVars (TupRsingle (varIdx -> idx)) ((e,lset) :>>>: lenv) f = case idx of
  ZeroIdx -> (e, f lset) :>>>: lenv
  SuccIdx idx' ->       (e, lset) :>>>: insertAtVars (TupRsingle (Var undefined idx')) lenv f
insertAtVars (TupRsingle (varIdx -> idx)) LabelEnvNil _ = case idx of VoidIdx x -> x -- convincing the pattern coverage checker of the impossible case

-- | Like `getLabelArgs`, but ignores the `Out` arguments
getInputArgLabels :: Args env args -> LabelEnv env -> Labels
getInputArgLabels ArgsNil _ = mempty
getInputArgLabels (arg :>: args) lenv = getInputArgLabels args lenv <> case arg of
  ArgArray Out _ _ _ -> mempty
  _ -> snd $ getLabelsArg arg lenv

body :: ALabel (Exp' e) -> ALabel (Fun' e)
body NotArr = NotArr
lam  :: ALabel (Fun' f) -> ALabel (Fun' (e->f))
lam  NotArr = NotArr
