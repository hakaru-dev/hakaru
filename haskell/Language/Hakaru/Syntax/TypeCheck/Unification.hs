{-# LANGUAGE CPP
           , ScopedTypeVariables
           , GADTs
           , DataKinds
           , KindSignatures
           , GeneralizedNewtypeDeriving
           , TypeOperators
           , FlexibleContexts
           , FlexibleInstances
           , OverloadedStrings
           , PatternGuards
           , Rank2Types
           , LiberalTypeSynonyms
           #-}

{-# OPTIONS_GHC -Wall -fwarn-tabs #-}
----------------------------------------------------------------
-- |
-- Module      :  Language.Hakaru.Syntax.TypeCheck
-- Copyright   :  Copyright (c) 2017 the Hakaru team
-- License     :  BSD3
-- Stability   :  experimental
-- Portability :  GHC-only
--
-- Ad-hoc implementation of unification (ad-hoc because polytypes are
-- inexpressible, and this module makes no attempt to express them).
----------------------------------------------------------------
module Language.Hakaru.Syntax.TypeCheck.Unification where

import Language.Hakaru.Syntax.TypeCheck.TypeCheckMonad
import Language.Hakaru.Types.DataKind (Hakaru(..), HPair)
import Language.Hakaru.Types.Sing
import Language.Hakaru.Syntax.IClasses
import qualified Language.Hakaru.Parser.AST as U
import Data.Text (Text)

type Metadata = Maybe U.SourceSpan

type Unify1 (t :: Hakaru -> Hakaru) r x
  =  Sing x
  -> Metadata
  -> (forall a . x ~ t a => Sing a -> TypeCheckMonad r)
  -> TypeCheckMonad r

type Unify2 (t :: Hakaru -> Hakaru -> Hakaru) r x
  =  Sing x
  -> Metadata
  -> (forall a b . x ~ t a b => Sing a -> Sing b -> TypeCheckMonad r)
  -> TypeCheckMonad r

class TCMTypeRepr x where
  toTypeRepr :: x -> Maybe (Either Text (Some1 (Sing :: Hakaru -> *)))

instance TCMTypeRepr (Sing (x :: Hakaru)) where
  toTypeRepr = Just . Right . Some1

instance TCMTypeRepr Text where
  toTypeRepr = Just . Left

instance TCMTypeRepr () where
  toTypeRepr () = Nothing

unifyMeasure :: Unify1 'HMeasure r x
unifyMeasure ty m k =
  case ty of
    SMeasure a -> k a
    _          -> typeMismatch m (Left "HMeasure") (Right ty)

unifyArray :: Unify1 'HArray r x
unifyArray ty m k =
  case ty of
    SArray a -> k a
    _        -> typeMismatch m (Left "HArray") (Right ty)

unifyFun :: Unify2 '(:->) r x
unifyFun ty m k =
  case ty of
    SFun a b -> k a b
    _        -> typeMismatch m (Left ":->") (Right ty)

unifyPair :: Unify2 HPair r x
unifyPair ty m k =
  maybe (typeMismatch m (Left "HPair") (Right ty)) id $ do
    SData (STyCon sym `STyApp` a `STyApp` b) _ <- Just ty
    Refl <- jmEq1 sym sSymbol_Pair
    Just $ k a b

matchTypes
  :: (TCMTypeRepr t0, TCMTypeRepr t1)
  => Sing (x :: Hakaru)
  -> Sing y
  -> Metadata
  -> t0 -> t1
  -> (x ~ y => TypeCheckMonad r)
  -> TypeCheckMonad r
matchTypes t0 t1 m e0 e1 k
  | Just Refl <- jmEq1 t0 t1 = k
  | otherwise                =
    let tyRepr
          :: TCMTypeRepr t
          => Sing (x :: Hakaru)
          -> t
          -> Either Text (Some1 (Sing :: Hakaru -> *))
        tyRepr d = maybe (Right $ Some1 d) id . toTypeRepr
        err = typeMismatch m
        err :: Either Text (Sing (x :: Hakaru))
            -> Either Text (Sing (y :: Hakaru))
            -> TypeCheckMonad r
    in case (tyRepr t0 e0, tyRepr t1 e1) of
         (Left a, Left b) -> err (Left a) (Left b)
         (Left a, Right (Some1 b)) -> err (Left a) (Right b)
         (Right (Some1 a), Left b) -> err (Right a) (Left b)
         (Right (Some1 a), Right (Some1 b)) -> err (Right a) (Right b)
