{-# LANGUAGE CPP
           , FlexibleInstances
           , GADTs
           , DataKinds
           , TypeOperators
           , KindSignatures
           , LambdaCase
           , ViewPatterns
           , DeriveDataTypeable
           , StandaloneDeriving
           , OverlappingInstances
           , UndecidableInstances
           , RankNTypes
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
  -- * Transformation contexts
  , TransformCtx(..), HasTransformCtx(..), unionCtx, minimalCtx
  -- * Transformation tables
  , TransformTable(..), lookupTransform', simpleTable
  , unionTable, someTransformations
  )
  where


import Language.Hakaru.Syntax.ABT
import Language.Hakaru.Syntax.SArgs
import Language.Hakaru.Syntax.IClasses
import Language.Hakaru.Syntax.Variable
import Language.Hakaru.Types.DataKind
import Language.Hakaru.Types.Sing

import Control.Applicative (Alternative(..), Applicative(..))
import Data.Number.Nat
import Data.Data (Data, Typeable)
import Data.List (stripPrefix)
import Data.Monoid (Monoid(..))

#if !(MIN_VERSION_base(4,11,0))
import Data.Semigroup
#endif

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
      (a :-> 'HMeasure b)

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
  readsPrec _ s =
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
    (Disint _ , Pw _ (sUnPair.sUnMeasure -> (a,b)) :* End)
      -> SFun a (SMeasure b)
    (Summarize, Pw _ e :* End)
      -> e
    (Simplify , Pw _ e :* End)
      -> e
    (Reparam  , Pw _ e :* End)
      -> e

-- | The context in which a transformation is called.  Currently this is simply
--   the next free variable in the enclosing program, but it could one day be
--   expanded to include more information, e.g., an association of variables to
--   terms in the enclosing program.
newtype TransformCtx = TransformCtx
  { nextFreeVar :: Nat }
    deriving (Eq, Ord, Show)

-- | The smallest possible context, i.e. a default context suitable for use when
-- performing induction on terms which may contain transformations as subterms.
minimalCtx :: TransformCtx
minimalCtx = TransformCtx { nextFreeVar = 0 }

-- | The union of two contexts
unionCtx :: TransformCtx -> TransformCtx -> TransformCtx
unionCtx ctx0 ctx1 =
  TransformCtx { nextFreeVar = max (nextFreeVar ctx0) (nextFreeVar ctx1) }

instance Semigroup TransformCtx where
  (<>) = unionCtx

instance Monoid TransformCtx where
  mempty  = minimalCtx
#if !(MIN_VERSION_base(4,11,0))
  mappend = (<>)
#endif

-- | The class of types which have an associated context
class HasTransformCtx x where
  ctxOf :: x -> TransformCtx

instance HasTransformCtx (Variable (a :: Hakaru)) where
  ctxOf v = TransformCtx { nextFreeVar = varID v + 1 }

instance ABT syn abt => HasTransformCtx (abt (xs :: [Hakaru]) (a :: Hakaru)) where
  ctxOf t = TransformCtx { nextFreeVar = nextFree t }

-- | A functional lookup table which indicates how to expand
--   transformations. The function returns @Nothing@ when the transformation
--   shouldn't be expanded. When it returns @Just k@, @k@ is passed an @SArgs@
--   and a @TransformCtx@.
newtype TransformTable abt m
  =  TransformTable
  {  lookupTransform
  :: forall as b
  .  Transform as b
  -> Maybe (TransformCtx -> SArgs abt as -> m (Maybe (abt '[] b))) }

-- | A variant of @lookupTransform@ which joins the two layers of @Maybe@.
lookupTransform'
  :: (Applicative m)
  => TransformTable abt m
  -> Transform as b
  -> TransformCtx
  -> SArgs abt as -> m (Maybe (abt '[] b))
lookupTransform' tbl tr ctx args=
  case lookupTransform tbl tr of
    Just f  -> f ctx args
    Nothing -> pure Nothing

-- | Builds a 'simple' transformation table, i.e. one which doesn't make use of
--  the monadic context. Such a table is valid in every @Applicative@ context.
simpleTable
  :: (Applicative m)
  => (forall as b . Transform as b
                 -> Maybe (TransformCtx -> SArgs abt as -> Maybe (abt '[] b)))
  -> TransformTable abt m
simpleTable k = TransformTable $ \tr -> fmap (fmap (fmap pure)) $ k tr

-- | Take the left-biased union of two transformation tables
unionTable :: TransformTable abt m
           -> TransformTable abt m
           -> TransformTable abt m
unionTable tbl0 tbl1 = TransformTable $ \tr ->
  lookupTransform tbl0 tr <|>
  lookupTransform tbl1 tr

-- | Intersect a transformation table with a list of transformations
someTransformations :: [Some2 Transform]
                    -> TransformTable abt m
                    -> TransformTable abt m
someTransformations toExpand tbl = TransformTable $
  \tr -> if Some2 tr `elem` toExpand then lookupTransform tbl tr else Nothing
