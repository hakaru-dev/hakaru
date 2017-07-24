{-# LANGUAGE FlexibleInstances
           , GADTs
           , DataKinds
           , TypeOperators
           , KindSignatures
           , LambdaCase
           , ViewPatterns
           , DeriveDataTypeable
           , StandaloneDeriving
           , OverlappingInstances
           #-}

{-# OPTIONS_GHC -Wall -fwarn-tabs #-}
-- |
-- Module      :  Language.Hakaru.Syntax.Transform
-- Copyright   :  Copyright (c) 2016 the Hakaru team
-- License     :  BSD3
-- Stability   :  experimental
-- Portability :  GHC-only
--
-- The internal syntax of Hakaru transformations, which are functions on Hakaru
-- terms which are neither primitive, nor expressible in terms of Hakaru
-- primitives.
----------------------------------------------------------------
module Language.Hakaru.Syntax.Transform
  (
  -- * Transformation internal syntax
    TransformImpl(..)
  , Transform(..)
  -- * Some utilities
  , transformName, allTransforms
  -- * Mapping of input type to output type for transforms
  , typeOfTransform
  )
  where


import Language.Hakaru.Syntax.SArgs
import Language.Hakaru.Syntax.IClasses
import Language.Hakaru.Types.DataKind
import Language.Hakaru.Types.Sing

import Data.Data (Data, Typeable)

import Data.List (stripPrefix)

----------------------------------------------------------------

-- | Some transformations have the same type and 'same' semantics, but are
--   implemented in multiple different ways. Such transformations are
--   distinguished in concrete syntax by differing keywords.
data TransformImpl = InMaple | InHaskell
  deriving (Eq, Ord, Show, Read, Data, Typeable)

-- | Transformations and their types. Like 'Language.Hakaru.Syntax.AST.SCon'.
data Transform :: [([Hakaru], Hakaru)] -> Hakaru -> * where
  Expect  ::
    Transform
      '[ LC ('HMeasure a), '( '[ a ], 'HProb) ] 'HProb

  Observe ::
    Transform
      '[ LC ('HMeasure a), LC a ] ('HMeasure a)

  MH ::
    Transform
      '[ LC (a ':-> 'HMeasure a), LC ('HMeasure a) ]
      (a ':-> 'HMeasure (HPair a 'HProb))

  MCMC ::
    Transform
      '[ LC (a ':-> 'HMeasure a), LC ('HMeasure a) ]
      (a ':-> 'HMeasure a)

  Disint :: TransformImpl ->
    Transform
      '[ LC ('HMeasure (HPair a b)) ]
      (a :-> HMeasure b)

  Summarize ::
    Transform '[ LC a ] a

  Simplify ::
    Transform '[ LC a ] a

  Reparam ::
    Transform '[ LC a ] a

deriving instance Eq   (Transform args a)
deriving instance Show (Transform args a)

instance Eq (Some2 Transform) where
  Some2 t0 == Some2 t1 =
    case (t0, t1) of
      (Expect    , Expect   ) -> True
      (Observe   , Observe  ) -> True
      (MH        , MH       ) -> True
      (MCMC      , MCMC     ) -> True
      (Disint k0 , Disint k1) -> k0==k1
      (Summarize , Summarize) -> True
      (Simplify  , Simplify ) -> True
      (Reparam   , Reparam  ) -> True
      _ -> False

instance Read (Some2 Transform) where
  readsPrec p s =
    let trs = map (\t'@(Some2 t) -> (show t, t')) allTransforms
        readMay (s', t)
          | Just rs <- stripPrefix s' s = [(t, rs)]
          | otherwise                   = []
    in concatMap readMay trs

-- | The concrete syntax names of transformations.
transformName :: Transform args a -> String
transformName =
  \case
    Expect    -> "expect"
    Observe   -> "observe"
    MH        -> "mh"
    MCMC      -> "mcmc"
    Disint k  -> "disint" ++
      (case k of
         InHaskell -> ""
         InMaple   -> "_m")
    Summarize -> "summarize"
    Simplify  -> "simplify"
    Reparam   -> "reparam"

-- | All transformations.
allTransforms :: [Some2 Transform]
allTransforms =
  [ Some2 Expect, Some2 Observe, Some2 MH, Some2 MCMC
  , Some2 (Disint InHaskell), Some2 (Disint InMaple)
  , Some2 Summarize, Some2 Simplify, Some2 Reparam ]

typeOfTransform
    :: Transform as x
    -> SArgsSing as
    -> Sing x
typeOfTransform t as =
  case (t,as) of
    (Expect   , _)
      -> SProb
    (Observe  , Pw _ e :* _ :* End)
      -> e
    (MH       , Pw _ (fst.sUnFun -> a) :* _ :* End)
      -> SFun a (SMeasure (sPair a SProb))
    (MCMC     , Pw _ a :* _)
      -> a
    (Disint k0, Pw _ (sUnPair.sUnMeasure -> (a,b)) :* End)
      -> SFun a (SMeasure b)
    (Summarize, Pw _ e :* End)
      -> e
    (Simplify , Pw _ e :* End)
      -> e
    (Reparam  , Pw _ e :* End)
      -> e
