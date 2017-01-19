{-# LANGUAGE CPP                       #-}
{-# LANGUAGE DataKinds                 #-}
{-# LANGUAGE EmptyCase                 #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE FlexibleContexts          #-}
{-# LANGUAGE GADTs                     #-}
{-# LANGUAGE KindSignatures            #-}
{-# LANGUAGE MultiParamTypeClasses     #-}
{-# LANGUAGE OverloadedStrings         #-}
{-# LANGUAGE PolyKinds                 #-}
{-# LANGUAGE TypeFamilies              #-}
{-# LANGUAGE TypeOperators             #-}
module Language.Hakaru.Syntax.ANF where

--------------------------------------------------------------------------------
-- An implementation of A-normalization as described in
--   https://pdfs.semanticscholar.org/5da1/4c8b7851e56e4bf08e30db4ced54be989768.pdf
-- A-normalization is not strictly necessary, but make implementing later
-- transformations easy, as all non-trivial operations are assigned names.
--
-- The planned pipeline:
-- 1. ANF conversion
-- 2. Expression hoising (perform operations as soon as their data dependencies
--    are satisified)
-- 3. (Conditional hoisting)
-- 4. CSE (in order to clean up work duplicated by hoisting)
--------------------------------------------------------------------------------

import           Prelude                          hiding ((+))

import qualified Data.Sequence      as S

import           Language.Hakaru.Syntax.ABT
import           Language.Hakaru.Syntax.AST
import           Language.Hakaru.Syntax.Datum
import           Language.Hakaru.Syntax.DatumCase
import           Language.Hakaru.Syntax.IClasses
import           Language.Hakaru.Syntax.TypeOf
import           Language.Hakaru.Syntax.Value
import           Language.Hakaru.Syntax.Variable
import           Language.Hakaru.Types.Coercion
import           Language.Hakaru.Types.DataKind
import           Language.Hakaru.Types.HClasses
import           Language.Hakaru.Types.Sing

import           Language.Hakaru.Syntax.Prelude

import           Debug.Trace

example1 = binder "a" sing $ \ a -> (triv $ real_ 1 + a)

example2 = let_ (real_ 1) $ \ a -> (triv (real_ 1 + a))

-- | The context in which A-normalization occurs. Represented as a continuation,
-- the context expects an expression of a particular type (usually a variable)
-- and produces a new expression as a result.
type Context abt a b = abt '[] a -> abt '[] b

-- | Entry point for the normalization process. Initializes normalize' with the
-- empty context.
normalize
  :: (ABT Term abt)
  => abt '[] a
  -> abt '[] a
normalize = flip normalize' id

normalize'
  :: (ABT Term abt)
  => abt '[] a
  -> Context abt a b
  -> abt '[] b
normalize' abt = caseVarSyn abt normalizeVar normalizeTerm

normalizeVar :: (ABT Term abt) => (Variable a) -> Context abt a b -> abt '[] b
normalizeVar v k = k (var v)

{-
 -normalizeArgs
 -  :: (ABT Term abt)
 -  => S.Seq (abt '[] a)
 -  -> (S.Seq (abt '[] a) -> abt '[] a)
 -  -> abt '[] a
 -normalizeArgs
 -}

isValue
  :: (ABT Term abt)
  => abt '[] a
  -> Bool
isValue abt = caseVarSyn abt (const True) isValueTerm
  where
    isValueTerm Literal_{}  = True
    isValueTerm Datum_{}     = True
    isValueTerm (Lam_ :$ _) = True
    isValueTerm _           = False

normalizeTerm
  :: (ABT Term abt)
  => Term abt a
  -> Context abt a b
  -> abt '[] b
normalizeTerm (NaryOp_ op args) = normalizeNaryOp op args
normalizeTerm (x :$ args)       = normalizeSCon x args
normalizeTerm term              = ($ syn term)

normalizeName
  :: (ABT Term abt)
  => abt '[] a
  -> Context abt a b
  -> abt '[] b
normalizeName abt ctxt = normalize' abt giveName
  where
    giveName abt' | isValue abt' = ctxt abt'
                  | otherwise    = let_ abt' ctxt

normalizeNaryOp
  :: (ABT Term abt)
  => NaryOp a
  -> S.Seq (abt '[] a)
  -> Context abt a b
  -> abt '[] b
normalizeNaryOp op args ctxt_ = go args (ctxt_ . syn . NaryOp_ op)
  where go args ctxt = undefined

normalizeSCon
  :: (ABT Term abt)
  => SCon args a
  -> SArgs abt args
  -> Context abt a b
  -> abt '[] b

normalizeSCon Let_ =
  \(rhs :* body :* End) ctxt -> caseBind body $
    \v@Variable{} body' ->
      normalize' rhs $ \rhs' ->
        let body'' = normalize' body' ctxt
        in syn (Let_ :$ rhs' :* bind v body'' :* End)

normalizeSCon Lam_ =
  \(body :* End) ctxt -> caseBind body $
    \v@Variable{} body' ->
      let body'' = bind v (normalize body')
      in ctxt $ syn (Lam_ :$ body'' :* End)

normalizeSCon Summate{} = undefined

