{-# LANGUAGE DataKinds                  #-}
{-# LANGUAGE EmptyCase                  #-}
{-# LANGUAGE ExistentialQuantification  #-}
{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE GADTs                      #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE KindSignatures             #-}
{-# LANGUAGE MultiParamTypeClasses      #-}
{-# LANGUAGE OverloadedStrings          #-}
{-# LANGUAGE PolyKinds                  #-}
{-# LANGUAGE ScopedTypeVariables        #-}
{-# LANGUAGE TypeFamilies               #-}
{-# LANGUAGE TypeOperators              #-}

{-# OPTIONS_GHC -Wall -fwarn-tabs #-}
----------------------------------------------------------------
--                                                    2017.02.01
-- |
-- Module      :  Language.Hakaru.Syntax.Uniquify
-- Copyright   :  Copyright (c) 2016 the Hakaru team
-- License     :  BSD3
-- Maintainer  :
-- Stability   :  experimental
-- Portability :  GHC-only
--
-- Performs renaming of Hakaru expressions to ensure globally unique variable
-- identifiers.
--
----------------------------------------------------------------
module Language.Hakaru.Syntax.Unroll where

import           Prelude                         hiding (product, (*), (+), (-),
                                                  (==), (>=))

import           Language.Hakaru.Syntax.ABT
import           Language.Hakaru.Syntax.AST
import           Language.Hakaru.Syntax.AST.Eq   (Varmap)
import           Language.Hakaru.Syntax.IClasses
import           Language.Hakaru.Syntax.Prelude
import           Language.Hakaru.Types.DataKind
import           Language.Hakaru.Types.HClasses

example :: TrivialABT Term '[] 'HInt
example = (summate (int_ 0) (int_ 100) $ \x -> x + (int_ 1 * int_ 42))

example2 :: TrivialABT Term '[] 'HNat
example2 = let_ (nat_ 1) $ \ a -> triv ((summate a (a + (nat_ 10)) (\i -> i)) +
                                        (product a (a + (nat_ 10)) (\i -> i)))

unroll :: forall abt xs a . (ABT Term abt) => abt xs a -> abt xs a
unroll = loop . viewABT
  where
    loop :: View (Term abt) ys a -> abt ys a
    loop (Var v)    = var v
    loop (Syn s)    = unrollTerm s
    loop (Bind v b) = bind v (loop b)

mklet :: ABT Term abt => Variable b -> abt '[] b -> abt '[] a -> abt '[] a
mklet v rhs body = syn (Let_ :$ rhs :* bind v body :* End)

unrollTerm
  :: (ABT Term abt)
  => Term abt a
  -> abt '[] a
unrollTerm ((Summate disc semi) :$ lo :* hi :* body :* End) =
  case (disc, semi) of
    (HDiscrete_Nat, HSemiring_Nat)  -> unrollSummate disc semi lo hi body
    (HDiscrete_Nat, HSemiring_Int)  -> unrollSummate disc semi lo hi body
    (HDiscrete_Nat, HSemiring_Prob) -> unrollSummate disc semi lo hi body
    (HDiscrete_Nat, HSemiring_Real) -> unrollSummate disc semi lo hi body

    (HDiscrete_Int, HSemiring_Nat)  -> unrollSummate disc semi lo hi body
    (HDiscrete_Int, HSemiring_Int)  -> unrollSummate disc semi lo hi body
    (HDiscrete_Int, HSemiring_Prob) -> unrollSummate disc semi lo hi body
    (HDiscrete_Int, HSemiring_Real) -> unrollSummate disc semi lo hi body

unrollTerm ((Product disc semi) :$ lo :* hi :* body :* End) =
  case (disc, semi) of
    (HDiscrete_Nat, HSemiring_Nat)  -> unrollProduct disc semi lo hi body
    (HDiscrete_Nat, HSemiring_Int)  -> unrollProduct disc semi lo hi body
    (HDiscrete_Nat, HSemiring_Prob) -> unrollProduct disc semi lo hi body
    (HDiscrete_Nat, HSemiring_Real) -> unrollProduct disc semi lo hi body

    (HDiscrete_Int, HSemiring_Nat)  -> unrollProduct disc semi lo hi body
    (HDiscrete_Int, HSemiring_Int)  -> unrollProduct disc semi lo hi body
    (HDiscrete_Int, HSemiring_Prob) -> unrollProduct disc semi lo hi body
    (HDiscrete_Int, HSemiring_Real) -> unrollProduct disc semi lo hi body

unrollTerm term        = syn $ fmap21 unroll term

unrollSummate
  :: (ABT Term abt, HSemiring_ a, HSemiring_ b, HEq_ a)
  => HDiscrete a
  -> HSemiring b
  -> abt '[] a
  -> abt '[] a
  -> abt '[a] b
  -> abt '[] b
unrollSummate disc semi lo hi body =
  caseBind body $ \v body' ->
  let body''   = unroll body'
      preamble = mklet v lo body''
      loop     = syn (Summate disc semi :$ lo + one :* hi :* bind v body'' :* End)
  -- The resulting expression must have the form (preamble + loop) since we
  -- rely on the ordering to produce the proper code post ANF (i.e. we need all
  -- expressions in the preamble to dominate those in the loop).
  in if_ (lo == hi) zero (preamble + loop)

unrollProduct
  :: (ABT Term abt, HSemiring_ a, HSemiring_ b, HEq_ a)
  => HDiscrete a
  -> HSemiring b
  -> abt '[] a
  -> abt '[] a
  -> abt '[a] b
  -> abt '[] b
unrollProduct disc semi lo hi body =
  caseBind body $ \v body' ->
  let body''   = unroll body'
      preamble = mklet v lo body''
      loop     = syn (Product disc semi :$ lo + one :* hi :* bind v body'' :* End)
  -- The resulting expression must have the form (preamble + loop) since we
  -- rely on the ordering to produce the proper code post ANF (i.e. we need all
  -- expressions in the preamble to dominate those in the loop).
  in if_ (lo == hi) one (preamble * loop)

