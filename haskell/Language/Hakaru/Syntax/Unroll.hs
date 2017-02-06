{-# LANGUAGE DataKinds                  #-}
{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE GADTs                      #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE RankNTypes                 #-}
{-# LANGUAGE ScopedTypeVariables        #-}
{-# LANGUAGE TypeOperators              #-}

{-# OPTIONS_GHC -Wall -fwarn-tabs #-}
----------------------------------------------------------------
--                                                    2017.02.01
-- |
-- Module      :  Language.Hakaru.Syntax.Unroll
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

import           Control.Monad.Reader
import           Data.Maybe                      (fromMaybe)
import           Language.Hakaru.Syntax.ABT
import           Language.Hakaru.Syntax.AST
import           Language.Hakaru.Syntax.AST.Eq   (Varmap)
import           Language.Hakaru.Syntax.IClasses
import           Language.Hakaru.Syntax.Prelude
import           Language.Hakaru.Types.DataKind
import           Language.Hakaru.Types.HClasses
import           Prelude                         hiding (product, (*), (+), (-),
                                                  (==), (>=))

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
freshBinder source f = binderM (varHint source) (varType source) $ \var' ->
  let v = caseVarSyn var' id (const $ error "oops")
  in local (insertAssoc (Assoc source v)) (f v)

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
unrollTerm (Summate disc semi :$ lo :* hi :* body :* End) =
  case (disc, semi) of
    (HDiscrete_Nat, HSemiring_Nat)  -> unrollSummate disc semi lo hi body
    (HDiscrete_Nat, HSemiring_Int)  -> unrollSummate disc semi lo hi body
    (HDiscrete_Nat, HSemiring_Prob) -> unrollSummate disc semi lo hi body
    (HDiscrete_Nat, HSemiring_Real) -> unrollSummate disc semi lo hi body

    (HDiscrete_Int, HSemiring_Nat)  -> unrollSummate disc semi lo hi body
    (HDiscrete_Int, HSemiring_Int)  -> unrollSummate disc semi lo hi body
    (HDiscrete_Int, HSemiring_Prob) -> unrollSummate disc semi lo hi body
    (HDiscrete_Int, HSemiring_Real) -> unrollSummate disc semi lo hi body

unrollTerm (Product disc semi :$ lo :* hi :* body :* End) =
  case (disc, semi) of
    (HDiscrete_Nat, HSemiring_Nat)  -> unrollProduct disc semi lo hi body
    (HDiscrete_Nat, HSemiring_Int)  -> unrollProduct disc semi lo hi body
    (HDiscrete_Nat, HSemiring_Prob) -> unrollProduct disc semi lo hi body
    (HDiscrete_Nat, HSemiring_Real) -> unrollProduct disc semi lo hi body

    (HDiscrete_Int, HSemiring_Nat)  -> unrollProduct disc semi lo hi body
    (HDiscrete_Int, HSemiring_Int)  -> unrollProduct disc semi lo hi body
    (HDiscrete_Int, HSemiring_Prob) -> unrollProduct disc semi lo hi body
    (HDiscrete_Int, HSemiring_Real) -> unrollProduct disc semi lo hi body

unrollTerm term        = fmap syn (traverse21 unroll' term)

-- Conditionally introduce a variable for the rhs if the rhs is not currently a
-- variable already. Be careful that the provided variable has been remaped to
-- its equivalent in the target term if altering the binding structure of the
-- program.
letM' :: (MonadFix m, ABT Term abt)
      => abt '[] a
      -> (abt '[] a -> m (abt '[] b))
      -> m (abt '[] b)
letM' e f =
  case viewABT e of
    Var _            -> f e
    Syn (Literal_ _) -> f e
    _                -> letM e f

unrollSummate
  :: (ABT Term abt, HSemiring_ a, HSemiring_ b, HEq_ a)
  => HDiscrete a
  -> HSemiring b
  -> abt '[] a
  -> abt '[] a
  -> abt '[a] b
  -> Unroll (abt '[] b)
unrollSummate disc semi lo hi body = do
   lo'   <- unroll' lo
   hi'   <- unroll' hi
   body' <- unroll' body
   letM' lo' $ \loVar ->
     letM' hi' $ \hiVar ->
       let preamble = mklet loVar body'
           loop     = mksummate disc semi (loVar + one) hiVar body'
       in return $ if_ (loVar == hiVar) zero (preamble + loop)

unrollProduct
  :: (ABT Term abt, HSemiring_ a, HSemiring_ b, HEq_ a)
  => HDiscrete a
  -> HSemiring b
  -> abt '[] a
  -> abt '[] a
  -> abt '[a] b
  -> Unroll (abt '[] b)
unrollProduct disc semi lo hi body = do
   lo'   <- unroll' lo
   hi'   <- unroll' hi
   body' <- unroll' body
   letM' lo' $ \loVar ->
     letM' hi' $ \hiVar ->
       let preamble = mklet loVar body'
           loop     = mkproduct disc semi (loVar + one) hiVar body'
       in return $ if_ (loVar == hiVar) one (preamble * loop)

