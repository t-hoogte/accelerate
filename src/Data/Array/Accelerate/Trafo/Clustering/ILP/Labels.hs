{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE EmptyCase #-}
{-# LANGUAGE ViewPatterns #-}
module Data.Array.Accelerate.Trafo.Clustering.ILP.Labels where


-- accelerate imports
import Data.Array.Accelerate.AST.Idx ( Idx(..) )
import Data.Array.Accelerate.AST.LeftHandSide ( LeftHandSide(..) )
import Data.Array.Accelerate.AST.Operation
import Data.Array.Accelerate.Representation.Type ( TupR(..) )

-- In this file, order very often subly does matter.
-- To keep this clear, we use S.Set whenever it does not,
-- and [] only when it does. It's also often efficient
-- by removing duplicates.
import qualified Data.Set as S


-- identifies nodes with unique Ints. and tracks their dependencies
type Label =  Int

-- identifies elements of the environment with unique Ints.
-- newtype'd to avoid confusing them with Label (above).
newtype ELabel = ELabel Int
  deriving (Show, Eq, Ord, Num)


-- | Keeps track of which argument belongs to which labels
data LabelArgs args where
  LabelArgsNil :: LabelArgs ()
  (:>>:)       :: S.Set Label -> LabelArgs t -> LabelArgs (s -> t)

-- | Keeps track of which array in the environment belongs to which label
data LabelEnv env where
  LabelEnvNil  :: LabelEnv ()
  (:>>>:)      :: (ELabel, S.Set Label) -> LabelEnv t -> LabelEnv (t, s)

addLhsLabels :: LeftHandSide s v env env' -> ELabel -> S.Set Label -> LabelEnv env -> (ELabel, LabelEnv env')
addLhsLabels LeftHandSideWildcard{} e _ lenv =     (e    , lenv)
addLhsLabels LeftHandSideSingle{}   e l lenv =     (e + 1, (e, l) :>>>: lenv)
addLhsLabels (LeftHandSidePair x y) e l lenv = let (e'   , lenv') = addLhsLabels x e l lenv
                                               in addLhsLabels y e' l lenv'

weakLhsEnv :: LeftHandSide s v env env' -> LabelEnv env' -> LabelEnv env
weakLhsEnv LeftHandSideSingle{} (_:>>>: env) = env
weakLhsEnv LeftHandSideWildcard{} env = env
weakLhsEnv (LeftHandSidePair l r) env = weakLhsEnv l (weakLhsEnv r env)

emptyLabelEnv :: LabelEnv env -> LabelEnv env
emptyLabelEnv LabelEnvNil = LabelEnvNil
emptyLabelEnv ((e,_):>>>:env) = (e, mempty) :>>>: emptyLabelEnv env

getAllLabelsEnv :: LabelEnv env -> S.Set Label
getAllLabelsEnv LabelEnvNil = mempty
getAllLabelsEnv ((_,set) :>>>: lenv) = set <> getAllLabelsEnv lenv

getLabelArgs :: Args env args -> LabelEnv env -> LabelArgs args
getLabelArgs ArgsNil _ = LabelArgsNil
getLabelArgs (arg :>: args) e = getLabelsArg arg e :>>: getLabelArgs args e

getLabelsArg :: Arg env t -> LabelEnv env -> S.Set Label
getLabelsArg (ArgVar tup)                  env = getLabelsTup tup    env
getLabelsArg (ArgExp expr)                 env = getLabelsExp expr   env
getLabelsArg (ArgFun fun)                  env = getLabelsFun fun    env
getLabelsArg (ArgArray _ _ shVars bufVars) env = getLabelsTup shVars env <> getLabelsTup bufVars env

getLabelsTup :: TupR (Var a env) b -> LabelEnv env -> S.Set Label
getLabelsTup TupRunit                     _   = mempty
getLabelsTup (TupRsingle var) env = getLabelsVar var env
getLabelsTup (TupRpair x y)               env = getLabelsTup x env <> getLabelsTup y env

getLabelsVar :: Var s env t -> LabelEnv env -> S.Set Label
getLabelsVar (varIdx -> idx) = getLabelsIdx idx

getLabelsIdx :: Idx env a -> LabelEnv env -> S.Set Label
getLabelsIdx ZeroIdx ((_,ls) :>>>: _) = ls
getLabelsIdx (SuccIdx idx) (_ :>>>: env) = getLabelsIdx idx env

getELabelIdx :: Idx env a -> LabelEnv env -> ELabel
getELabelIdx ZeroIdx ((e,_) :>>>: _) = e
getELabelIdx (SuccIdx idx) (_ :>>>: env) = getELabelIdx idx env

getLabelsExp :: OpenExp x env y -> LabelEnv env -> S.Set Label
getLabelsExp = undefined -- TODO traverse everything, look for Idxs

getLabelsFun :: OpenFun x env y -> LabelEnv env -> S.Set Label
getLabelsFun (Body expr) lenv = getLabelsExp expr lenv
getLabelsFun (Lam _ fun) lenv = getLabelsFun fun  lenv

updateLabelEnv :: Args env args -> LabelEnv env -> Label -> LabelEnv env
updateLabelEnv ArgsNil lenv _ = lenv
updateLabelEnv (arg :>: args) lenv l = case arg of
  -- CHECK we only look at the 'Buffer' vars here, not the 'shape' ones. Is that ok?
  ArgArray Out _ _ vars -> updateLabelEnv args (insertAtVars vars lenv l) l
  ArgArray Mut _ _ vars -> updateLabelEnv args (insertAtVars vars lenv l) l
  _ -> updateLabelEnv args lenv l

insertAtVars :: TupR (Var a env) b -> LabelEnv env -> Label -> LabelEnv env
insertAtVars TupRunit lenv _ = lenv
insertAtVars (TupRpair x y) lenv l = insertAtVars x (insertAtVars y lenv l) l
insertAtVars (TupRsingle (varIdx -> idx)) ((e,lset) :>>>: lenv) l = case idx of
  ZeroIdx -> (e, S.insert l lset) :>>>: lenv
  SuccIdx idx' ->       (e, lset) :>>>: insertAtVars (TupRsingle (Var undefined idx')) lenv l
insertAtVars (TupRsingle (varIdx -> idx)) LabelEnvNil _ = case idx of {}

-- | Like `getLabelArgs`, but ignores the `Out` arguments
getInputArgLabels :: Args env args -> LabelEnv env -> S.Set Label
getInputArgLabels ArgsNil _ = mempty
getInputArgLabels (arg :>: args) lenv = getInputArgLabels args lenv <> case arg of
  ArgArray Out _ _ _ -> mempty
  _ -> getLabelsArg arg lenv
