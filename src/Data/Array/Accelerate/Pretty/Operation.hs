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
-- |
-- Module      : Data.Array.Accelerate.Pretty.Operation
-- Copyright   : [2008..2020] The Accelerate Team
-- License     : BSD3
--
-- Maintainer  : Trevor L. McDonell <trevor.mcdonell@gmail.com>
-- Stability   : experimental
-- Portability : non-portable (GHC extensions)
--

module Data.Array.Accelerate.Pretty.Operation (
  PrettyOp(..),
  prettyAcc, prettyOpenAcc,
  prettyAfun, prettyOpenAfun,
  prettyGroundR, Val'(..),
  prettyArg, prettyShapeVars
) where

import Data.Array.Accelerate.Pretty.Exp
import Data.Array.Accelerate.Pretty.Type
import Data.Array.Accelerate.AST.Operation
import Data.Array.Accelerate.AST.LeftHandSide
import Data.Array.Accelerate.Array.Buffer
import Data.Array.Accelerate.Representation.Elt
import Data.Array.Accelerate.Representation.Type
import Data.Array.Accelerate.Type

import Data.Text.Prettyprint.Doc
import Data.String

import Prelude hiding (exp)

class PrettyOp op where
  prettyOp :: op t -> Either Adoc (Args env t -> Adoc)

prettyAcc :: PrettyOp op => OperationAcc op () t -> Adoc
prettyAcc = prettyOpenAcc empty'

prettyAfun :: PrettyOp op => OperationAfun op () f -> Adoc
prettyAfun = prettyOpenAfun empty'

prettyOpenAfun :: PrettyOp op => Val' benv -> OperationAfun op benv f -> Adoc
prettyOpenAfun env (Abody a) = prettyOpenAcc env a
prettyOpenAfun env (Alam lhs f) = "\\" <> lhs' <+> "->" <> hardline <> indent 2 (prettyOpenAfun env' f)
  where
    (env', lhs') = prettyGLhsWithTypes env lhs

prettyOpenAcc :: PrettyOp op => Val' benv -> OperationAcc op benv t -> Adoc
prettyOpenAcc env = \case
  Exec op args -> case prettyOp op of
    Left op' -> hang 2 $ group $ vsep [annotate Execute "execute", op', prettyArgs env args]
    Right op' -> hang 2 $ group $ vsep [annotate Execute "execute", op' args]
  Return vars -> hang 2 $ group $ vsep [annotate Statement "return", prettyVars env 10 vars]
  Compute exp -> hang 2 $ group $ vsep [annotate Statement "compute", prettyExp env exp]
  Alet (LeftHandSideWildcard TupRunit) _ bnd body
    -> prettyOpenAcc env bnd
        <> hardline
        <> prettyOpenAcc env body
  Alet lhs us bnd body
    | (env', lhs') <- prettyGLhsWithUniquenessTypes env lhs us
      -> hang 2 (group $ vsep [lhs' <+> "=", prettyOpenAcc env bnd])
         <> hardline
         <> prettyOpenAcc env' body
  Alloc _ tp sh -> hang 2 $ group $ vsep [annotate Statement "alloc", prettyScalarType tp <> "[" <> prettyShapeVars env sh <> "]"]
  Use tp n buffer -> hang 2 $ group $ vsep [annotate Statement "use" <+> prettyScalarType tp <> "[" <> pretty n <> "]", prettyBuffer tp n buffer]
  Unit var -> hang 2 $ group $ vsep [annotate Statement "unit", prettyVar env var]
  Acond c true false
    -> group $ vsep
        [ hang 2 $ group $ vsep
          [ if_ <+> prettyVar env c <+> then_
          , prettyOpenAcc env true
          ]
        , hang 2 $ group $ vsep
          [ else_
          , prettyOpenAcc env false
          ]
        ]
  Awhile us condition step initial
    -> "awhile" <+> prettyTupR (const $ prettyGroundRWithUniqueness) 10 (groundsRWithUniquenesses (mapTupR varType initial) us)
        <> hardline <> hang 4 ("  ( " <> prettyOpenAfun env condition)
        <> hardline <> "  )"
        <> hardline <> hang 4 ("  ( " <> prettyOpenAfun env step)
        <> hardline <> "  )"
        <> hardline <> indent 2 (prettyVars env 10 initial)

prettyArgs :: Val' benv -> Args benv f -> Adoc
prettyArgs env args = tupled $ map (\(Exists a) -> prettyArg env a) $ argsToList args

prettyArg :: Val' benv -> Arg benv t -> Adoc
prettyArg env (ArgVar vars) = prettyVars env 10 vars
prettyArg env (ArgExp e) = prettyExp env e
prettyArg env (ArgFun f) = prettyFun env f
prettyArg env (ArgArray m _ sh buffers) = group $ vsep [prettyModifier m, "(" <> prettyShapeVars env sh <> ")", prettyVars env 0 buffers]

prettyModifier :: Modifier m -> Adoc
prettyModifier In  = annotate Modifier "in"
prettyModifier Out = annotate Modifier "out"
prettyModifier Mut = annotate Modifier "mut"

prettyBuffer :: ScalarType tp -> Int -> Buffer tp -> Adoc
prettyBuffer _  0 _ = "[]"
prettyBuffer tp n b = align $ group $ "[ " <> vcat (mapTail (", " <>) $ map (fromString . showElt (TupRsingle tp)) $ bufferToList tp n b) <> " ]"

mapTail :: (a -> a) -> [a] -> [a]
mapTail f (x:xs) = x : map f xs
mapTail _ []     = []

-- Expressions
prettyFun :: Val' env -> Fun env f -> Adoc
prettyFun env = prettyPreOpenFun (prettyArrayInstr env) Empty

prettyExp :: Val' env -> Exp env t -> Adoc
prettyExp env = prettyPreOpenExp context0 (prettyArrayInstr env) Empty

prettyExp' :: Context -> Val' env -> Exp env t -> Adoc
prettyExp' ctx env = prettyPreOpenExp ctx (prettyArrayInstr env) Empty

prettyArrayInstr :: Val' env -> PrettyArrayInstr (ArrayInstr env)
prettyArrayInstr env context (Index arr) ix
  = parensIf (ctxPrecedence context < 9)
  $ sep [ prettyVar env arr
        , group (sep ["!!", ix context']) ]
  where
    context' = Context L R 9
prettyArrayInstr env context (Parameter var) _ = prettyVar env var

-- LHS
prettyGLhs :: Val' env -> GLeftHandSide t env env' -> (Val' env', Adoc)
prettyGLhs = prettyLhs' push Nothing False

prettyGLhsWithTypes :: Val' env -> GLeftHandSide t env env' -> (Val' env', Adoc)
prettyGLhsWithTypes = prettyLhs' push (Just $ \(Exists t) -> prettyGroundR t) False

prettyGLhsWithUniquenessTypes :: Val' env -> GLeftHandSide t env env' -> Uniquenesses t -> (Val' env', Adoc)
prettyGLhsWithUniquenessTypes env lhs us
  = prettyLhs'
      (\(GroundRWithUniqueness g _) -> push g)
      (Just $ \(Exists t) -> prettyGroundRWithUniqueness t)
      False
      env
      (lhsWithUniquesses lhs us)


-- Environment
data Val' env = Val' (Val env) Int Int

push :: GroundR t -> Val' env -> (Val' (env, t), Adoc)
push (GroundRbuffer _) (Val' env b s) = (Val' (Push env d) (b + 1) s, d)
  where d = "b" <> pretty b
push (GroundRscalar _) (Val' env b s) = (Val' (Push env d) b (s + 1), d)
  where d = "s" <> pretty s

empty' :: Val' ()
empty' = Val' Empty 0 0

-- Variables
prettyVar :: Val' env -> Var s env t -> Adoc
prettyVar (Val' env _ _) (Var _ ix) = prj ix env

prettyVars :: forall env s t. Val' env -> Precedence -> Vars s env t -> Adoc
prettyVars env = prettyTupR $ const $ prettyVar env

prettyShapeVars :: Val' env -> Vars s env sh -> Adoc
prettyShapeVars _   TupRunit = "Z"
prettyShapeVars env vars = encloseSep "Z :. " "" " :. " $ map (\(Exists v) -> prettyVar env v) $ flattenTupR vars

-- Types
prettyGroundR :: GroundR t -> Adoc
prettyGroundR (GroundRscalar tp) = prettyScalarType tp
prettyGroundR (GroundRbuffer tp) = "[" <> prettyScalarType tp <> "]"

prettyGroundRWithUniqueness :: GroundRWithUniqueness t -> Adoc
prettyGroundRWithUniqueness (GroundRWithUniqueness tp Unique) = prettyGroundR tp <> "¹"
prettyGroundRWithUniqueness (GroundRWithUniqueness tp Shared) = prettyGroundR tp <> ""
