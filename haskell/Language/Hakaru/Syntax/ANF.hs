{-# LANGUAGE DataKinds                 #-}
{-# LANGUAGE EmptyCase                 #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE FlexibleContexts          #-}
{-# LANGUAGE GADTs                     #-}
{-# LANGUAGE KindSignatures            #-}
{-# LANGUAGE MultiParamTypeClasses     #-}
{-# LANGUAGE OverloadedStrings         #-}
{-# LANGUAGE PolyKinds                 #-}
{-# LANGUAGE ScopedTypeVariables       #-}
{-# LANGUAGE TypeFamilies              #-}
{-# LANGUAGE TypeOperators             #-}

{-# OPTIONS_GHC -Wall -fwarn-tabs #-}
----------------------------------------------------------------
--                                                    2017.02.01
-- |
-- Module      :  Language.Hakaru.Syntax.ANF
-- Copyright   :  Copyright (c) 2016 the Hakaru team
-- License     :  BSD3
-- Maintainer  :
-- Stability   :  experimental
-- Portability :  GHC-only
--
--
----------------------------------------------------------------
module Language.Hakaru.Syntax.ANF (normalize, isValue) where

import           Data.Maybe
import           Control.Monad.Cont              (Cont, runCont, cont)

import           Language.Hakaru.Syntax.ABT
import           Language.Hakaru.Syntax.AST
import           Language.Hakaru.Syntax.IClasses
import           Language.Hakaru.Types.DataKind

import           Language.Hakaru.Syntax.Prelude

-- The renaming environment which maps variables in the original term to their
-- counterparts in the new term. This is needed since the mechanism which
-- ensures hygiene for the AST only factors in binders, but not free variables
-- in the expression being constructed. When we construct a new binding form, a
-- new variable is introduced and the variable in the old expression must be
-- mapped to the new one.

type Env = Assocs (Variable :: Hakaru -> *)

updateEnv :: forall (a :: Hakaru) . Variable a -> Variable a -> Env -> Env
updateEnv vin vout = insertAssoc (Assoc vin vout)

-- | The context in which A-normalization occurs. Represented as a continuation,
-- the context expects an expression of a particular type (usually a variable)
-- and produces a new expression as a result.
type Context abt a b = abt '[] a -> abt '[] b

-- | Extract a variable from an abt. This function is partial
getVar :: (ABT Term abt) => abt xs a -> Variable a
getVar abt = case viewABT abt of
               Var v -> v
               _     -> error "getVar: not given a variable"

-- | Useful function for generating fresh variables from an existing variable by
-- wrapping @binder@.
freshVar
  :: (ABT Term abt)
  => Variable a
  -> (Variable a -> abt xs b)
  -> abt (a ': xs) b
freshVar v f = binder (varHint v) (varType v) (f . getVar)

remapVar
  :: (ABT Term abt)
  => Variable a
  -> Env
  -> (Env -> abt xs b)
  -> abt (a ': xs) b
remapVar v env f = freshVar v $ \v' -> f (updateEnv v v' env)

-- | Entry point for the normalization process. Initializes normalize' with the
-- empty context.
normalize
  :: (ABT Term abt)
  => abt '[] a
  -> abt '[] a
normalize abt = normalize' abt emptyAssocs id

normalize'
  :: (ABT Term abt)
  => abt '[] a
  -> Env
  -> Context abt a b
  -> abt '[] b
normalize' = normalizeTail . viewABT

normalizeTail, normalizeSave
  :: (ABT Term abt)
  => View (Term abt) xs a
  -> Env
  -> (abt xs a -> abt '[] b)
  -> abt '[] b
normalizeTail (Var v)     env ctxt = ctxt (normalizeVar v env)
normalizeTail (Syn s)     env ctxt = normalizeTerm s env ctxt
normalizeTail view@Bind{} env ctxt = ctxt (normalizeReset view env)
normalizeSave (Var v)     env ctxt = ctxt (normalizeVar v env)
normalizeSave (Syn s)     env ctxt = normalizeTerm s env giveName
  where giveName abt' | isValue abt' = ctxt abt'
                      | otherwise    = let_ abt' ctxt
normalizeSave view@Bind{} env ctxt = ctxt (normalizeReset view env)

normalizeReset :: (ABT Term abt) => View (Term abt) xs a -> Env -> abt xs a
normalizeReset (Var v)    env = normalizeVar v env
normalizeReset (Syn s)    env = normalizeTerm s env id
normalizeReset (Bind v b) env = remapVar v env (normalizeReset b)

normalizeVar :: (ABT Term abt) => Variable a -> Env -> abt '[] a
normalizeVar v env = var $ fromMaybe v (lookupAssoc v env)

isValue
  :: (ABT Term abt)
  => abt xs a
  -> Bool
isValue abt =
  case viewABT abt of
    Var{}  -> True
    Bind{} -> False
    Syn s  -> isValueTerm s
  where
    isValueTerm Literal_{}  = True
    isValueTerm (Lam_ :$ _) = True
    isValueTerm _           = False

normalizeTerm
  :: forall abt a b
  .  (ABT Term abt)
  => Term abt a
  -> Env
  -> Context abt a b
  -> abt '[] b

normalizeTerm (Let_ :$ (rhs :* body :* End)) env ctxt =
  caseBind body $ \v body' ->
  normalize' rhs env $ \rhs' ->
  let mkbody env' = normalize' body' env' ctxt
  in syn (Let_ :$ rhs' :* remapVar v env mkbody :* End)

normalizeTerm (Case_ cond bs) env ctxt =
  normalizeSave (viewABT cond) env $ \ cond' ->
    let normalizeBranch :: forall xs d . abt xs d -> abt xs d
        normalizeBranch body = normalizeReset (viewABT body) env
        branches = map (fmap21 normalizeBranch) bs
    -- A possible optimization is to push the context into each conditional,
    -- possibly opening up other optimizations at the cost of code growth.
    in ctxt $ syn $ Case_ cond' branches

normalizeTerm term env ctxt = runCont (fmap syn (traverse21 f term)) ctxt
  where f :: forall xs c . abt xs c -> Cont (abt '[] b) (abt xs c)
        f abt = cont (n (viewABT abt) env)
        n :: forall xs c
          .  View (Term abt) xs c
          -> Env
          -> (abt xs c -> abt '[] b)
          -> abt '[] b
        -- TODO: Can we just let n=normalizeTail or n=normalizeSave?
        n = case term of MBind         :$ _ -> normalizeTail
                         Plate         :$ _ -> normalizeTail
                         Dirac         :$ _ -> normalizeTail
                         UnsafeFrom_ _ :$ _ -> normalizeTail
                         CoerceTo_   _ :$ _ -> normalizeTail
                         _                  -> normalizeSave
