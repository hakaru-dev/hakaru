{-# LANGUAGE CPP
           , DataKinds
           , KindSignatures
           , GADTs
           , ScopedTypeVariables
           , Rank2Types
           , FlexibleContexts
           #-}

{-# OPTIONS_GHC -Wall -fwarn-tabs #-}
----------------------------------------------------------------
--                                                    2016.01.15
-- |
-- Module      :  Language.Hakaru.Syntax.TypeOf
-- Copyright   :  Copyright (c) 2015 the Hakaru team
-- License     :  BSD3
-- Maintainer  :  wren@community.haskell.org
-- Stability   :  experimental
-- Portability :  GHC-only
--
-- BUG: can't put this in "Language.Hakaru.Syntax.AST.Sing" because of some sort of cyclic dependency...
----------------------------------------------------------------
module Language.Hakaru.Syntax.TypeOf
    (
    -- * Get singletons for well-typed ABTs
      typeOf
    , typeOf_
    
    -- * Implementation details
    , getTermSing
    ) where

import qualified Data.Foldable as F
#if __GLASGOW_HASKELL__ < 710
import Data.Functor ((<$>))
#endif

import Language.Hakaru.Syntax.IClasses (Pair2(..), fst2, snd2)
import Language.Hakaru.Syntax.Variable (varType)
import Language.Hakaru.Syntax.ABT      (ABT, caseBind, paraABT)
import Language.Hakaru.Types.DataKind  (Hakaru())
import Language.Hakaru.Types.Sing      (Sing(..))
import Language.Hakaru.Types.Coercion
    (singCoerceCod, singCoerceDom, Coerce(..))
import Language.Hakaru.Syntax.Datum    (Branch(..))
import Language.Hakaru.Syntax.AST      (Term(..), SCon(..), SArgs(..))
import Language.Hakaru.Syntax.AST.Sing
    (sing_PrimOp, sing_MeasureOp, sing_NaryOp, sing_Literal)

----------------------------------------------------------------
----------------------------------------------------------------

-- | Given any well-typed term, produce the type. N.B., this is a
-- bit of a hack in order to avoid using 'SingI' or needing to
-- memoize the types of everything. You should really avoid using
-- this function if at all possible since it's very expensive.
--
-- BUG: we currently do not handle 'Datum_'. You should be able to
-- circumvent this by putting an 'Ann_' immediately before any
-- 'Datum_'.
typeOf :: (ABT Term abt) => abt '[] a -> Sing a
typeOf e0 =
    case typeOf_ e0 of
    Left  err -> error $ "typeOf: " ++ err
    Right typ -> typ


-- | A safe variant of 'typeOf', which returns the error message
-- as a string rather than throwing it as an exception. N.B., there
-- are only two ways this can fail (other than the bug about not
-- handling 'Datum_', which throws a TODO exeption rather than
-- returning an error message string): for 'Case_' and 'Superpose_'
-- if they are empty or all their branches fail.
typeOf_ :: (ABT Term abt) => abt '[] a -> Either String (Sing a)
typeOf_
    = unLiftSing
    . paraABT
        (LiftSing . return . varType)
        (\_ _ -> LiftSing . unLiftSing) -- cast out phantoms
        (LiftSing . getTermSing unLiftSing)


-- | This newtype serves two roles. First we add the phantom @xs@
-- so that we can fit this in with the types of 'paraABT'. And
-- second, we wrap up the 'Sing' in a monad for capturing errors,
-- so that we can bring them all the way to the top of the term
-- before deciding whether to throw them or not.
newtype LiftSing (xs :: [Hakaru]) (a :: Hakaru) =
    LiftSing { unLiftSing :: Either String (Sing a) }


----------------------------------------------------------------
-- | This is the core of the 'Term'-algebra for computing 'typeOf_'.
-- It is exported because it is useful for constructing other
-- 'Term'-algebras for use with 'paraABT'; namely, for callers who
-- need singletons for every subterm while converting an ABT to
-- something else (e.g., pretty printing).
--
-- The @r@ type is whatever it is you're building up via 'paraABT'.
-- The first argument to 'getTermSing' gives some way of projecting
-- a singleton out of @r@ (to avoid the need to map that projection
-- over the term before calling 'getTermSing'). You can then use
-- the resulting singleton for constructing the overall @r@ to be
-- returned.
getTermSing
    :: forall abt r
    .  (ABT Term abt)
    => (forall xs a. r xs a -> Either String (Sing a))
    -> forall a
    .  Term (Pair2 abt r) a
    -> Either String (Sing a)
getTermSing singify = go
    where
    getSing :: forall xs a. Pair2 abt r xs a -> Either String (Sing a)
    getSing = singify . snd2
    {-# INLINE getSing #-}

    getBranchSing
        :: forall a b
        .  Branch a (Pair2 abt r) b
        -> Either String (Sing b)
    getBranchSing (Branch _ e) = getSing e
    {-# INLINE getBranchSing #-}

    go :: forall a. Term (Pair2 abt r) a -> Either String (Sing a)
    go (Lam_ :$ r1 :* End) =
        caseBind (fst2 r1) $ \x _ ->
            SFun (varType x) <$> getSing r1
    go (App_ :$ r1 :* _ :* End) = do
        typ1 <- getSing r1
        case typ1 of
            SFun _ typ3            -> return typ3
            _ -> error "getTermSing: the impossible happened"
    go (Let_ :$ _  :* r2 :* End)    = getSing r2
    go (Ann_      typ :$ _)         = return typ
    go (CoerceTo_   c :$ r1 :* End) =
        maybe (coerceTo   c <$> getSing r1) return (singCoerceCod c)
    go (UnsafeFrom_ c :$ r1 :* End) =
        maybe (coerceFrom c <$> getSing r1) return (singCoerceDom c)
    go (PrimOp_     o :$ _)         = return . snd $ sing_PrimOp o
    go (MeasureOp_  o :$ _)         =
        return . SMeasure . snd $ sing_MeasureOp o
    go (Dirac  :$ r1 :* End)        = SMeasure <$> getSing r1
    go (MBind  :$ _  :* r2 :* End)  = getSing r2
    go (Expect :$ _)                = return SProb
    go (NaryOp_  o  _)              = return $ sing_NaryOp o
    go (Literal_ v)                 = return $ sing_Literal v
    go (Empty_   typ)               = return typ
    go (Array_   _  r2)             = SArray <$> getSing r2
    go (Datum_   d)                 = error "TODO: getTermSing{Datum_}"
    go (Case_    _  bs) = tryAll "Case_"      getBranchSing   bs
    go (Superpose_ pes) = tryAll "Superpose_" (getSing . snd) pes
    go (_ :$ _) = error "getTermSing: the impossible happened"


tryAll
    :: F.Foldable f
    => String
    -> (a -> Either String b)
    -> f a
    -> Either String b
tryAll name f =
    F.foldr step (Left $ "no unique type for " ++ name)
    where
    step x rest =
        case f x of
        r@(Right _) -> r
        Left _      -> rest
{-# INLINE tryAll #-}

----------------------------------------------------------------
----------------------------------------------------------- fin.
