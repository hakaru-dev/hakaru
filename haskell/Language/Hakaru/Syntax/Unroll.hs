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
{-# LANGUAGE RankNTypes                 #-}
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
import           Data.Maybe (fromMaybe)
import           Control.Monad.Reader
import           Control.Monad.Fix
import           Language.Hakaru.Syntax.Variable
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

newtype Unroll a = Unroll { runUnroll :: Reader Varmap a }
  deriving (Functor, Applicative, Monad, MonadReader Varmap, MonadFix)

freshBinder
  :: (ABT Term abt)
  => Variable a
  -> (Variable a -> Unroll (abt xs b))
  -> Unroll (abt (a ': xs) b)
freshBinder var abt = binderM (varHint var) (varType var) $ \var' ->
  let v = case viewABT var' of
            Var v -> v
            _     -> error "oops"
  in local (insertAssoc (Assoc var v)) (abt v)

unroll :: forall abt xs a . (ABT Term abt) => abt xs a -> abt xs a
unroll abt = runReader (runUnroll $ unroll' abt) emptyAssocs

unroll' :: forall abt xs a . (ABT Term abt) => abt xs a -> Unroll (abt xs a)
unroll' = loop . viewABT
  where
    loop :: View (Term abt) ys a -> Unroll (abt ys a)
    loop (Var v)    = fmap (var . fromMaybe v . lookupAssoc v) ask
    loop (Syn s)    = unrollTerm s
    loop (Bind v b) = freshBinder v (const $ loop b)

mklet :: ABT Term abt => abt '[] b -> abt '[b] a -> abt '[] a
mklet rhs body = syn (Let_ :$ rhs :* body :* End)

mksummate, mkproduct
  :: (ABT Term abt)
  => HDiscrete a
  -> HSemiring b
  -> abt '[] a
  -> abt '[] a
  -> abt '[a] b
  -> abt '[] b
mksummate a b lo hi body = syn (Summate a b :$ lo :* hi :* body :* End)
mkproduct a b lo hi body = syn (Product a b :$ lo :* hi :* body :* End)

unrollTerm
  :: (ABT Term abt)
  => Term abt a
  -> Unroll (abt '[] a)
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

unrollTerm term        = fmap syn $ traverse21 unroll' term

unrollSummate
  :: (ABT Term abt, HSemiring_ a, HSemiring_ b, HEq_ a)
  => HDiscrete a
  -> HSemiring b
  -> abt '[] a
  -> abt '[] a
  -> abt '[a] b
  -> Unroll (abt '[] b)
unrollSummate disc semi lo hi body =
   caseBind body $ \v body' -> do
   lo' <- unroll' lo
   hi' <- unroll' hi
   letM lo' $ \loVar ->
     letM hi' $ \hiVar -> do
       preamble <- fmap (mklet lo') (freshBinder v $ \_ -> unroll' body')
       loop     <- fmap (mksummate disc semi (lo' + one) hi')
                        (freshBinder v $ \_ -> unroll' body')
       return $ if_ (lo == hi) zero (preamble + loop)

unrollProduct
  :: (ABT Term abt, HSemiring_ a, HSemiring_ b, HEq_ a)
  => HDiscrete a
  -> HSemiring b
  -> abt '[] a
  -> abt '[] a
  -> abt '[a] b
  -> Unroll (abt '[] b)
unrollProduct disc semi lo hi body =
   caseBind body $ \v body' -> do
   lo' <- unroll' lo
   hi' <- unroll' hi
   letM lo' $ \loVar ->
     letM hi' $ \hiVar -> do
       preamble <- fmap (mklet lo') (freshBinder v $ \_ -> unroll' body')
       loop     <- fmap (mkproduct disc semi (lo' + one) hi')
                        (freshBinder v $ \_ -> unroll' body')
       return $ if_ (lo == hi) one (preamble * loop)
