{-# LANGUAGE DataKinds                  #-}
{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE GADTs                      #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses      #-}
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
import           Language.Hakaru.Syntax.ABT      hiding (rename)
import           Language.Hakaru.Syntax.AST
import           Language.Hakaru.Syntax.AST.Eq   (Varmap)
import           Language.Hakaru.Syntax.Prelude  hiding ((>>=))
import           Language.Hakaru.Types.HClasses
import           Prelude                         hiding (product, (*), (+), (-),
                                                  (==), (>=))

newtype Unroll a = Unroll { runUnroll :: Reader Varmap a }
  deriving (Functor, Applicative, Monad, MonadReader Varmap, MonadFix)

rebind
  :: (ABT Term abt, MonadFix m)
  => Variable a
  -> (Variable a -> m (abt xs b))
  -> m (abt (a ': xs) b)
rebind source f = binderM (varHint source) (varType source) $ \var' ->
  let v = caseVarSyn var' id (const $ error "oops")
  in f v

renameInEnv
  :: (ABT Term abt, MonadReader Varmap m, MonadFix m)
  => Variable a
  -> m (abt xs b)
  -> m (abt (a ': xs) b)
renameInEnv source action = rebind source $ \v ->
  local (insertAssoc $ Assoc source v) action

unroll :: forall abt xs a . (ABT Term abt) => abt xs a -> abt xs a
unroll abt = runReader (runUnroll $ unroll' abt) emptyAssocs

unroll' :: forall abt xs a . (ABT Term abt) => abt xs a -> Unroll (abt xs a)
unroll' = cataABTM var_ renameInEnv (>>= unrollTerm)
  where
    var_ :: Variable b -> Unroll (abt '[] b)
    var_ v = fmap (var . fromMaybe v . lookupAssoc v) ask

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

unrollTerm term = return (syn term)

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
unrollSummate disc semi lo hi body =
   letM' lo $ \loVar ->
     letM' hi $ \hiVar ->
       let preamble = mklet loVar body
           loop     = mksummate disc semi (loVar + one) hiVar body
       in return $ if_ (loVar == hiVar) zero (preamble + loop)

unrollProduct
  :: (ABT Term abt, HSemiring_ a, HSemiring_ b, HEq_ a)
  => HDiscrete a
  -> HSemiring b
  -> abt '[] a
  -> abt '[] a
  -> abt '[a] b
  -> Unroll (abt '[] b)
unrollProduct disc semi lo hi body =
   letM' lo $ \loVar ->
     letM' hi $ \hiVar ->
       let preamble = mklet loVar body
           loop     = mkproduct disc semi (loVar + one) hiVar body
       in return $ if_ (loVar == hiVar) one (preamble * loop)

