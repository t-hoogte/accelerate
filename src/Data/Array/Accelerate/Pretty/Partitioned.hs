{-# LANGUAGE FlexibleInstances   #-}
{-# LANGUAGE GADTs               #-}
{-# LANGUAGE LambdaCase          #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE PatternGuards       #-}
{-# LANGUAGE RankNTypes          #-}
{-# LANGUAGE RecordWildCards     #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications    #-}
{-# LANGUAGE TypeOperators       #-}
{-# LANGUAGE ViewPatterns        #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}
-- |
-- Module      : Data.Array.Accelerate.Pretty.Operation
-- Copyright   : [2008..2020] The Accelerate Team
-- License     : BSD3
--
-- Maintainer  : Trevor L. McDonell <trevor.mcdonell@gmail.com>
-- Stability   : experimental
-- Portability : non-portable (GHC extensions)
--

module Data.Array.Accelerate.Pretty.Partitioned (

) where

import Data.Array.Accelerate.Pretty.Exp hiding (Val(..))
import qualified Data.Array.Accelerate.Pretty.Exp as Pretty
import Data.Array.Accelerate.Pretty.Operation
import Data.Array.Accelerate.AST.Partitioned
import Data.Array.Accelerate.Type

import Data.Text.Prettyprint.Doc

import Prelude hiding (exp)

instance PrettyOp op => PrettyOp (Cluster' op) where
  prettyOp (Cluster' _ ast) = "{" <+> align (fillSep $ opNames ast)
    where
      opNames :: ClusterAST op env result -> [Adoc]
      opNames None             = ["}"]
      opNames (Bind _ op next) = prettyOp op : opNames next

  prettyOpWithArgs env (Cluster' io ast) args = case ops of
    [op']      -> group $ hang 2 $ vsep [ annotate Execute "execute", op' ]
    op' : ops' -> group $ hang 2 $ vsep $ [ annotate Execute "cluster", "{" <+> op'] ++ map (separator <>) ops' ++ ["}"]
    []         -> annotate Execute "cluster" <+> "{ }"
    where
      (inputEnv, outputEnv) = clusterEnv env io args
      (_, opsF) = prettyClusterAST outputEnv ast
      ops = opsF 0 inputEnv
      separator = "; "

instance PrettyOp op => PrettyOp (Cluster op) where
  prettyOp (Cluster _ c) = prettyOp c
  prettyOpWithArgs env (Cluster _ c) = prettyOpWithArgs env c

clusterEnv :: forall env f input output. Pretty.Val env -> ClusterIO f input output -> Args env f -> (Pretty.Val input, PartialVal output)
clusterEnv env = \cio args -> (input cio args, output cio args)
  where
    input :: ClusterIO t input' output' -> Args env t -> Pretty.Val input'
    input Empty ArgsNil
      = Pretty.Empty
    input (Vertical _ _ cio) (ArgVar sh :>: as)
      = Pretty.Push (input cio as) (prettyShapeVars env sh)
    input (Input cio) (a :>: as)
      = Pretty.Push (input cio as) (prettyArg env a)
    input (Output _ _ _ cio) (ArgArray Out _ sh _ :>: as)
      = Pretty.Push (input cio as) (prettyShapeVars env sh)
    input (MutPut cio) (a :>: as)
      = Pretty.Push (input cio as) (prettyArg env a)
    input (ExpPut' cio) (a :>: as)
      = Pretty.Push (input cio as) (prettyArg env a)

    output :: ClusterIO t input' output' -> Args env t -> PartialVal output'
    output Empty ArgsNil
      = PEnd
    output (Vertical t _ cio) (_ :>: as)
      = pSkipAt t (output cio as) -- We will name intermediate arrays in 'forward (Make _ _) _ _ _'
    output (Input cio) (a :>: as)
      = PPush (output cio as) (prettyArg env a)
    output (Output t _ _ cio) (a :>: as)
      = pInsertAt t (prettyArg env a) (output cio as)
    output (MutPut cio) (a :>: as)
      = PPush (output cio as) (prettyArg env a)
    output (ExpPut' cio) (a :>: as)
      = PPush (output cio as) (prettyArg env a)

-- The pretty printer gets an environment with Adocs of input variables (Val env, from clusterEnv)
-- which is propagated in the same flow as the cluster.
-- It also gets the names for the output environment (PartialVal result), which we propagate in reverse
-- direction. Hence this function both *takes* a 'Val env' (originating from the input variables)
-- and *returns* a 'PartialVal env' (originating from the output variables).
-- Variables which are absent in both environments represent arrays which are fused away.
--
prettyClusterAST :: PrettyOp op => PartialVal result -> ClusterAST op env result -> (PartialVal env, Int -> Pretty.Val env -> [Adoc])
prettyClusterAST envResult None = (envResult, \_ _ -> [])
prettyClusterAST envResult (Bind lhs op next) =
  ( backward lhs envOut
  , \fresh envIn ->
      let
        (fresh', envNext, args) = forward lhs fresh envIn envOut
      in
        prettyOpWithArgs' op args
        : next' fresh' envNext
  )
  where
    (envOut, next') = prettyClusterAST envResult next

prettyOpWithArgs' :: PrettyOp op => op t -> [Adoc] -> Adoc
prettyOpWithArgs' op args = hang 2 $ group $ vsep [prettyOp op, tupled args]

forward :: LeftHandSideArgs body env scope -> Int -> Pretty.Val env -> PartialVal scope -> (Int, Pretty.Val scope, [Adoc])
forward Base             fresh env _   = (fresh, env, [])
forward (Reqr t1 t2 lhs) fresh env out =
  ( fresh'
  , insertAt t2 arg env''
  , arg : args
  )
  where
    arg = prj (takeIdx t1) env
    env' = removeAt t1 env
    out' = pRemoveAt t2 out
    (fresh', env'', args) = forward lhs fresh env' out'
forward (Make t1 t2 lhs)     fresh (Pretty.Push env sh) out =
  ( fresh''
  , insertAt t name env'
  , arg : args
  )
  where
    (arg, name, fresh') = case pTakeAt t out of
      Just a ->  (a, a, fresh)
      Nothing -> (intermediate Out fresh sh, intermediate In fresh sh, fresh + 1)
    (fresh'', env', args) = forward lhs fresh' env (pRemoveAt t out)
forward (ExpArg lhs)     fresh env out = forwardSingle lhs fresh env out
forward (Adju lhs)       fresh env out = forwardSingle lhs fresh env out
forward (Ignr lhs)       fresh (Pretty.Push env x) out = (\(a, b, c) -> (a, Pretty.Push b x, c)) (forward lhs fresh env (pEnvTail out))

intermediate :: Modifier m -> Int -> Adoc -> Adoc
intermediate m idx sh = group $ vsep [prettyModifier m, "(" <> sh <> ")", "%" <> pretty idx]

forwardSingle :: LeftHandSideArgs body env scope -> Int -> Pretty.Val (env, t) -> PartialVal (scope, t) -> (Int, Pretty.Val (scope, t), [Adoc])
forwardSingle lhs fresh (Pretty.Push env a) out = (fresh', Pretty.Push env' a, a : args)
  where
    (fresh', env', args) = forward lhs fresh env $ pEnvTail out

backward :: LeftHandSideArgs body env scope -> PartialVal scope -> PartialVal env
backward _ PEnd = PEnd
backward (Reqr t1 t2 lhs) env = pWriteAt t1 (pTakeAt t2 env) $ backward lhs $ pRemoveAt t2 env
backward (Make t1 t2 lhs) env = PSkip $ backward lhs $ pRemoveAt t env
backward (ExpArg lhs) env = backwardSingle lhs env
backward (Adju lhs) env = backwardSingle lhs env
backward (Ignr lhs) env = backwardSingle lhs env

-- Helper for 'backward'
backwardSingle :: LeftHandSideArgs body env scope -> PartialVal (scope, t) -> PartialVal (env, t)
backwardSingle lhs (PSkip env)   = PSkip (backward lhs env)
backwardSingle lhs (PPush env a) = PPush (backward lhs env) a
backwardSingle _   PEnd          = PEnd

insertAt :: Take t env' env -> Adoc -> Pretty.Val env -> Pretty.Val env'
insertAt Here      a env                 = Pretty.Push env a
insertAt (There t) a (Pretty.Push env b) = Pretty.Push (insertAt t a env) b

removeAt :: Take t env env' -> Pretty.Val env -> Pretty.Val env'
removeAt Here (Pretty.Push env _) = env
removeAt (There t) (Pretty.Push env a) = Pretty.Push (removeAt t env) a

pInsertAt :: Take t env' env -> Adoc -> PartialVal env -> PartialVal env'
pInsertAt Here      a env = PPush env a
pInsertAt (There t) a env = case env of
  PEnd         -> PSkip (pInsertAt t a PEnd)
  PSkip env'   -> PSkip (pInsertAt t a env')
  PPush env' b -> PPush (pInsertAt t a env') b

pRemoveAt :: Take t env env' -> PartialVal env -> PartialVal env'
pRemoveAt Here      = pEnvTail
pRemoveAt (There t) = \case
  PEnd        -> PEnd
  PSkip env   -> PSkip (pRemoveAt t env)
  PPush env a -> PPush (pRemoveAt t env) a

pWriteAt :: Take t env' env -> Maybe Adoc -> PartialVal env -> PartialVal env'
pWriteAt t Nothing  = pSkipAt t
pWriteAt t (Just a) = pInsertAt t a

pSkipAt :: Take t env' env -> PartialVal env -> PartialVal env'
pSkipAt _         PEnd = PEnd
pSkipAt Here      env = PSkip env
pSkipAt (There t) (PSkip env)   = PSkip (pSkipAt t env)
pSkipAt (There t) (PPush env a) = PPush (pSkipAt t env) a

pTakeAt :: Take t env env' -> PartialVal env -> Maybe Adoc
pTakeAt Here      (PPush _ a) = Just a
pTakeAt (There t) (PPush e _) = pTakeAt t e
pTakeAt (There t) (PSkip e)   = pTakeAt t e
pTakeAt _         _           = Nothing

data PartialVal env where
  PEnd  ::                           PartialVal env
  PSkip :: PartialVal env         -> PartialVal (env, t)
  PPush :: PartialVal env -> Adoc -> PartialVal (env, t)

pEnvTail :: PartialVal (env, t) -> PartialVal env
pEnvTail PEnd          = PEnd
pEnvTail (PSkip env)   = env
pEnvTail (PPush env _) = env
