{-# LANGUAGE DataKinds
          , KindSignatures
          , PolyKinds
          , StandaloneDeriving
          , DeriveDataTypeable
          #-}

-- Don't -Werror, because we can't tick the promoted (:$) in the deriving instance
{-# OPTIONS -Wall -fwarn-tabs #-}

module Language.Hakaru.Syntax.DataKind
    ( Hakaru(..)
    , HakaruFun(..)
    ) where

import Data.Typeable (Typeable)

----------------------------------------------------------------
-- | The universe/kind of Hakaru types.
data Hakaru star
    = HNat -- TODO: finish incorporating this everywhere...
    | HInt
    | HProb -- meaning: non-negative real number (not the [0,1] interval!)
    | HReal -- The real projective line, includes +/- infinity
    | HMeasure (Hakaru star)
    | HArray (Hakaru star)
    | HFun (Hakaru star) (Hakaru star)
    
    -- TODO: replace HBool, HUnit, HPair, HEither with the Embed stuff
    | HBool
    | HUnit
    | HPair (Hakaru star) (Hakaru star)
    | HEither (Hakaru star) (Hakaru star)
    
    -- The lists-of-lists are sum-of-products functors. The application
    -- form allows us to unroll fixpoints: @HMu sop ~= sop :$ HMu sop@.
    | HMu [[HakaruFun star]]
    | [[HakaruFun star]] :$ Hakaru star
    | HTag star [[HakaruFun star]]
    
    -- Used in "Language.Hakaru.Expect"
    -- TODO: replace HList with the Embed stuff
    | HList (Hakaru star)
    
    -- Used in "Language.Hakaru.Sample"
    -- TODO: replace HMaybe with the Embed stuff
    | HMaybe (Hakaru star)


-- | The identity and constant functors on @Hakaru*@. This gives
-- us limited access to type-variables in @Hakaru*@, for use in
-- recursive sums-of-products. Notably, however, it only allows a
-- single variable (namely the one bound by the closest binder) so
-- it can't encode mutual recursion or other non-local uses of
-- multiple binders.
--
-- Products and sums are represented as lists, so they aren't
-- in this datatype.
data HakaruFun star = Id | K (Hakaru star)


-- N.B., The @Proxy@ type from "Data.Proxy" is polykinded, so it works for @Hakaru*@ too. However, it is _not_ Typeable!


-- TODO: these instances are only used in 'Language.Hakaru.Simplify.closeLoop'; it would be cleaner to remove these instances and reimplement that function to work without them.
deriving instance Typeable 'HNat
deriving instance Typeable 'HInt
deriving instance Typeable 'HReal
deriving instance Typeable 'HProb
deriving instance Typeable 'HMeasure
deriving instance Typeable 'HArray
deriving instance Typeable 'HFun
deriving instance Typeable 'HBool
deriving instance Typeable 'HUnit
deriving instance Typeable 'HPair
deriving instance Typeable 'HEither
deriving instance Typeable 'HMu
deriving instance Typeable 'HTag
deriving instance Typeable (:$) -- HACK: can't tick this here...
deriving instance Typeable 'HList
deriving instance Typeable 'HMaybe
deriving instance Typeable 'Id
deriving instance Typeable 'K

----------------------------------------------------------------
----------------------------------------------------------- fin.