{-# LANGUAGE CPP
           , DataKinds
           , PolyKinds
           , GADTs
           , TypeOperators
           , TypeFamilies
           , ExistentialQuantification
           #-}

{-# OPTIONS_GHC -Wall -fwarn-tabs #-}
----------------------------------------------------------------
--                                                    2016.04.27
-- |
-- Module      :  Language.Hakaru.Syntax.Datum
-- Copyright   :  Copyright (c) 2016 the Hakaru team
-- License     :  BSD3
-- Maintainer  :  wren@community.haskell.org
-- Stability   :  experimental
-- Portability :  GHC-only
--
-- Haskell types and helpers for Hakaru's user-defined data types.
-- At present we only support regular-recursive polynomial data
-- types. Reduction of case analysis on data types is in
-- "Language.Hakaru.Syntax.Datum".
--
-- /Developers note:/ many of the 'JmEq1' instances in this file
-- don't actually work because of problems with matching existentially
-- quantified types in the basis cases. For now I've left the
-- partially-defined code in place, but turned it off with the
-- @__PARTIAL_DATUM_JMEQ__@ CPP macro. In the future we should
-- either (a) remove this unused code, or (b) if the instances are
-- truly necessary then we should add the 'Sing' arguments everywhere
-- to make things work :(
----------------------------------------------------------------
module Language.Hakaru.Syntax.Datum
    (
    -- * Data constructors
      Datum(..), datumHint, datumType
    , DatumCode(..)
    , DatumStruct(..)
    , DatumFun(..)
    -- ** Some smart constructors for the \"built-in\" datatypes
    , dTrue, dFalse
    , dUnit
    , dPair
    , dLeft, dRight
    , dNil, dCons
    , dNothing, dJust
    -- *** Variants which allow explicit type passing.
    , dPair_
    , dLeft_, dRight_
    , dNil_, dCons_
    , dNothing_, dJust_

    -- * Pattern constructors
    , Branch(..)
    , Pattern(..)
    , PDatumCode(..)
    , PDatumStruct(..)
    , PDatumFun(..)
    -- ** Some smart constructors for the \"built-in\" datatypes
    , pTrue, pFalse
    , pUnit
    , pPair
    , pLeft, pRight
    , pNil, pCons
    , pNothing, pJust
    ) where

import qualified Data.Text     as Text
import           Data.Text     (Text)
#if __GLASGOW_HASKELL__ < 710
import Data.Monoid             (Monoid(..))
import Control.Applicative
#endif

import Language.Hakaru.Syntax.IClasses
-- TODO: make things polykinded so we can make our ABT implementation
-- independent of Hakaru's type system.
import Language.Hakaru.Types.DataKind
import Language.Hakaru.Types.Sing

----------------------------------------------------------------
----------------------------------------------------------------

#if __PARTIAL_DATUM_JMEQ__
cannotProve :: String -> a
cannotProve fun =
    error $ "Language.Hakaru.Syntax.Datum." ++ fun ++ ": Cannot prove Refl because of phantomness"
#endif


-- TODO: change the kind to @(Hakaru -> *) -> HakaruCon -> *@ so
-- we can avoid the use of GADTs? Would that allow us to actually
-- UNPACK?
--
-- | A fully saturated data constructor, which recurses as @ast@.
-- We define this type as separate from 'DatumCode' for two reasons.
-- First is to capture the fact that the datum is \"complete\"
-- (i.e., is a well-formed constructor). The second is to have a
-- type which is indexed by its 'Hakaru' type, whereas 'DatumCode'
-- involves non-Hakaru types.
--
-- The first component is a hint for what the data constructor
-- should be called when pretty-printing, giving error messages,
-- etc. Like the hints for variable names, its value is not actually
-- used to decide which constructor is meant or which pattern
-- matches.
data Datum :: (Hakaru -> *) -> Hakaru -> * where
    Datum
        :: {-# UNPACK #-} !Text
        -> !(Sing (HData' t))
        -> !(DatumCode (Code t) ast (HData' t))
        -> Datum ast (HData' t)

datumHint :: Datum ast (HData' t) -> Text
datumHint (Datum hint _ _) = hint

datumType :: Datum ast (HData' t) -> Sing (HData' t)
datumType (Datum _ typ _) = typ

-- N.B., This doesn't require jmEq on 'DatumCode' nor on @ast@. The
-- jmEq on the singleton is sufficient.
instance Eq1 ast => JmEq1 (Datum ast) where
    jmEq1 (Datum _ typ1 d1) (Datum _ typ2 d2) =
        case jmEq1 typ1 typ2 of
        Just proof@Refl
            | eq1 d1 d2 -> Just proof
        _               -> Nothing

instance Eq1 ast => Eq1 (Datum ast) where
    eq1 (Datum _ _ d1) (Datum _ _ d2) = eq1 d1 d2

instance Eq1 ast => Eq (Datum ast a) where
    (==) = eq1

-- TODO: instance Read (Datum ast a)

instance Show1 ast => Show1 (Datum ast) where
    showsPrec1 p (Datum hint typ d) =
        showParen_011 p "Datum" hint typ d

instance Show1 ast => Show (Datum ast a) where
    showsPrec = showsPrec1
    show      = show1

instance Functor11 Datum where
    fmap11 f (Datum hint typ d) = Datum hint typ (fmap11 f d)

instance Foldable11 Datum where
    foldMap11 f (Datum _ _ d) = foldMap11 f d

instance Traversable11 Datum where
    traverse11 f (Datum hint typ d) = Datum hint typ <$> traverse11 f d


----------------------------------------------------------------
infixr 7 `Et`, `PEt`

-- | The intermediate components of a data constructor. The intuition
-- behind the two indices is that the @[[HakaruFun]]@ is a functor
-- applied to the Hakaru type. Initially the @[[HakaruFun]]@ functor
-- will be the 'Code' associated with the Hakaru type; hence it's
-- the one-step unrolling of the fixed point for our recursive
-- datatypes. But as we go along, we'll be doing induction on the
-- @[[HakaruFun]]@ functor.
data DatumCode :: [[HakaruFun]] -> (Hakaru -> *) -> Hakaru -> * where
    -- BUG: haddock doesn't like annotations on GADT constructors
    -- <https://github.com/hakaru-dev/hakaru/issues/6>

    -- Skip rightwards along the sum.
    Inr :: !(DatumCode  xss abt a) -> DatumCode (xs ': xss) abt a
    -- Inject into the sum.
    Inl :: !(DatumStruct xs abt a) -> DatumCode (xs ': xss) abt a


-- N.B., these \"Foo1\" instances rely on polymorphic recursion,
-- since the @code@ changes at each constructor. However, we don't
-- actually need to abstract over @code@ in order to define these
-- functions, because (1) we never existentially close over any
-- codes, and (2) the code is always getting smaller; so we have
-- a good enough inductive hypothesis from polymorphism alone.

#if __PARTIAL_DATUM_JMEQ__
-- This instance works, but recurses into non-working instances.
instance JmEq1 ast => JmEq1 (DatumCode xss ast) where
    jmEq1 (Inr c) (Inr d) = jmEq1 c d
    jmEq1 (Inl c) (Inl d) = jmEq1 c d
    jmEq1 _       _       = Nothing
#endif

instance Eq1 ast => Eq1 (DatumCode xss ast) where
    eq1 (Inr c) (Inr d) = eq1 c d
    eq1 (Inl c) (Inl d) = eq1 c d
    eq1 _       _       = False

instance Eq1 ast => Eq (DatumCode xss ast a) where
    (==) = eq1

-- TODO: instance Read (DatumCode xss abt a)

instance Show1 ast => Show1 (DatumCode xss ast) where
    showsPrec1 p (Inr d) = showParen_1 p "Inr" d
    showsPrec1 p (Inl d) = showParen_1 p "Inl" d

instance Show1 ast => Show (DatumCode xss ast a) where
    showsPrec = showsPrec1
    show      = show1

instance Functor11 (DatumCode xss) where
    fmap11 f (Inr d) = Inr (fmap11 f d)
    fmap11 f (Inl d) = Inl (fmap11 f d)

instance Foldable11 (DatumCode xss) where
    foldMap11 f (Inr d) = foldMap11 f d
    foldMap11 f (Inl d) = foldMap11 f d

instance Traversable11 (DatumCode xss) where
    traverse11 f (Inr d) = Inr <$> traverse11 f d
    traverse11 f (Inl d) = Inl <$> traverse11 f d


----------------------------------------------------------------
data DatumStruct :: [HakaruFun] -> (Hakaru -> *) -> Hakaru -> * where
    -- BUG: haddock doesn't like annotations on GADT constructors
    -- <https://github.com/hakaru-dev/hakaru/issues/6>

    -- Combine components of the product. (\"et\" means \"and\" in Latin)
    Et  :: !(DatumFun    x         abt a)
        -> !(DatumStruct xs        abt a)
        ->   DatumStruct (x ': xs) abt a

    -- Close off the product.
    Done :: DatumStruct '[] abt a


#if __PARTIAL_DATUM_JMEQ__
instance JmEq1 ast => JmEq1 (DatumStruct xs ast) where
    jmEq1 (Et c1 Done) (Et d1 Done) = jmEq1 c1 d1 -- HACK: to handle 'Done' in the cases where we can.
    jmEq1 (Et c1 c2)   (Et d1 d2)   = do
        Refl <- jmEq1 c1 d1
        Refl <- jmEq1 c2 d2
        Just Refl
    jmEq1 Done Done = Just (cannotProve "jmEq1@DatumStruct{Done}")
    jmEq1 _    _    = Nothing
#endif

instance Eq1 ast => Eq1 (DatumStruct xs ast) where
    eq1 (Et c1 c2) (Et d1 d2) = eq1 c1 d1 && eq1 c2 d2
    eq1 Done       Done       = True
    eq1 _          _          = False

instance Eq1 ast => Eq (DatumStruct xs ast a) where
    (==) = eq1

-- TODO: instance Read (DatumStruct xs abt a)

instance Show1 ast => Show1 (DatumStruct xs ast) where
    showsPrec1 p (Et d1 d2) = showParen_11 p "Et" d1 d2
    showsPrec1 _ Done       = showString     "Done"

instance Show1 ast => Show (DatumStruct xs ast a) where
    showsPrec = showsPrec1
    show      = show1

instance Functor11 (DatumStruct xs) where
    fmap11 f (Et d1 d2) = Et (fmap11 f d1) (fmap11 f d2)
    fmap11 _ Done       = Done

instance Foldable11 (DatumStruct xs) where
    foldMap11 f (Et d1 d2) = foldMap11 f d1 `mappend` foldMap11 f d2
    foldMap11 _ Done       = mempty

instance Traversable11 (DatumStruct xs) where
    traverse11 f (Et d1 d2) = Et <$> traverse11 f d1 <*> traverse11 f d2
    traverse11 _ Done       = pure Done


----------------------------------------------------------------
-- TODO: do we like those constructor names? Should we change them?
data DatumFun :: HakaruFun -> (Hakaru -> *) -> Hakaru -> * where
    -- BUG: haddock doesn't like annotations on GADT constructors
    -- <https://github.com/hakaru-dev/hakaru/issues/6>

    -- Hit a leaf which isn't a recursive component of the datatype.
    Konst :: !(ast b) -> DatumFun ('K b) ast a
    -- Hit a leaf which is a recursive component of the datatype.
    Ident :: !(ast a) -> DatumFun 'I     ast a


#if __PARTIAL_DATUM_JMEQ__
instance JmEq1 ast => JmEq1 (DatumFun x ast) where
    jmEq1 (Konst e) (Konst f) = do
        Refl <- jmEq1 e f -- This 'Refl' should be free because @x@ is fixed
        Just (cannotProve "jmEq1@DatumFun{Konst}")
    jmEq1 (Ident e) (Ident f) = jmEq1 e f
    jmEq1 _         _         = Nothing
#endif

instance Eq1 ast => Eq1 (DatumFun x ast) where
    eq1 (Konst e) (Konst f) = eq1 e f
    eq1 (Ident e) (Ident f) = eq1 e f
    eq1 _         _         = False

instance Eq1 ast => Eq (DatumFun x ast a) where
    (==) = eq1

-- TODO: instance Read (DatumFun x abt a)

instance Show1 ast => Show1 (DatumFun x ast) where
    showsPrec1 p (Konst e) = showParen_1 p "Konst" e
    showsPrec1 p (Ident e) = showParen_1 p "Ident" e

instance Show1 ast => Show (DatumFun x ast a) where
    showsPrec = showsPrec1
    show      = show1

instance Functor11 (DatumFun x) where
    fmap11 f (Konst e) = Konst (f e)
    fmap11 f (Ident e) = Ident (f e)

instance Foldable11 (DatumFun x) where
    foldMap11 f (Konst e) = f e
    foldMap11 f (Ident e) = f e

instance Traversable11 (DatumFun x) where
    traverse11 f (Konst e) = Konst <$> f e
    traverse11 f (Ident e) = Ident <$> f e


----------------------------------------------------------------
-- In GHC 7.8 we can make the monomorphic smart constructors into
-- pattern synonyms, but 7.8 can't handle anything polymorphic (but
-- GHC 7.10 can). For libraries (e.g., "Language.Hakaru.Syntax.Prelude")
-- we can use functions to construct our Case_ statements, so library
-- designers don't need pattern synonyms. Whereas, for the internal
-- aspects of the compiler, we need to handle all possible Datum
-- values, so the pattern synonyms wouldn't even be helpful.

dTrue, dFalse :: Datum ast HBool
dTrue  = Datum tdTrue  sBool . Inl $ Done
dFalse = Datum tdFalse sBool . Inr . Inl $ Done

dUnit  :: Datum ast HUnit
dUnit  = Datum tdUnit sUnit . Inl $ Done

dPair :: (SingI a, SingI b) => ast a -> ast b -> Datum ast (HPair a b)
dPair = dPair_ sing sing

dPair_ :: Sing a -> Sing b -> ast a -> ast b -> Datum ast (HPair a b)
dPair_ a b x y =
    Datum tdPair (sPair a b) . Inl $ Konst x `Et` Konst y `Et` Done

dLeft :: (SingI a, SingI b) => ast a -> Datum ast (HEither a b)
dLeft = dLeft_ sing sing

dLeft_ :: Sing a -> Sing b -> ast a -> Datum ast (HEither a b)
dLeft_ a b =
    Datum tdLeft (sEither a b) . Inl . (`Et` Done) . Konst

dRight :: (SingI a, SingI b) => ast b -> Datum ast (HEither a b)
dRight = dRight_ sing sing

dRight_ :: Sing a -> Sing b -> ast b -> Datum ast (HEither a b)
dRight_ a b =
    Datum tdRight (sEither a b) . Inr . Inl . (`Et` Done) . Konst

dNil :: (SingI a) => Datum ast (HList a)
dNil = dNil_ sing

dNil_ :: Sing a -> Datum ast (HList a)
dNil_ a = Datum tdNil (sList a) . Inl $ Done

dCons :: (SingI a) => ast a -> ast (HList a) -> Datum ast (HList a)
dCons = dCons_ sing

dCons_ :: Sing a -> ast a -> ast (HList a) -> Datum ast (HList a)
dCons_ a x xs =
    Datum tdCons (sList a) . Inr . Inl $ Konst x `Et` Ident xs `Et` Done

dNothing :: (SingI a) => Datum ast (HMaybe a)
dNothing = dNothing_ sing

dNothing_ :: Sing a -> Datum ast (HMaybe a)
dNothing_ a = Datum tdNothing (sMaybe a) $ Inl Done

dJust :: (SingI a) => ast a -> Datum ast (HMaybe a)
dJust = dJust_ sing

dJust_ :: Sing a -> ast a -> Datum ast (HMaybe a)
dJust_ a = Datum tdJust (sMaybe a)  . Inr . Inl . (`Et` Done) . Konst


----------------------------------------------------------------
tdTrue, tdFalse, tdUnit, tdPair, tdLeft, tdRight, tdNil, tdCons, tdNothing, tdJust :: Text
tdTrue    = Text.pack "true"
tdFalse   = Text.pack "false"
tdUnit    = Text.pack "unit"
tdPair    = Text.pack "pair"
tdLeft    = Text.pack "left"
tdRight   = Text.pack "right"
tdNil     = Text.pack "nil"
tdCons    = Text.pack "cons"
tdNothing = Text.pack "nothing"
tdJust    = Text.pack "just"


----------------------------------------------------------------
----------------------------------------------------------------
-- TODO: negative patterns? (to facilitate reordering of case branches)
-- TODO: disjunctive patterns, a~la ML?
-- TODO: equality patterns for Nat\/Int? (what about Prob\/Real??)
-- TODO: exhaustiveness, non-overlap, dead-branch checking
--
-- | We index patterns by the type they scrutinize. This requires
-- the parser to be smart enough to build these patterns up, but
-- then it guarantees that we can't have 'Case_' of patterns which
-- can't possibly match according to our type system. In addition,
-- we also index patterns by the type of what variables they bind,
-- so that we can ensure that 'Branch' will never \"go wrong\".
-- Alas, this latter indexing means we can't use 'DatumCode',
-- 'DatumStruct', and 'DatumFun' but rather must define our own @P@
-- variants for pattern matching.
data Pattern :: [Hakaru] -> Hakaru -> * where
    -- BUG: haddock doesn't like annotations on GADT constructors
    -- <https://github.com/hakaru-dev/hakaru/issues/6>

    -- The \"don't care\" wildcard pattern.
    PWild :: Pattern '[]    a

    -- A pattern variable.
    PVar  :: Pattern '[ a ] a

    -- A data type constructor pattern. As with the 'Datum'
    -- constructor, the first component is a hint.
    PDatum
        :: {-# UNPACK #-} !Text
        -> !(PDatumCode (Code t) vars (HData' t))
        -> Pattern vars (HData' t)


#if __PARTIAL_DATUM_JMEQ__
instance JmEq2 Pattern where
    jmEq2 PWild PWild = Just (Refl, cannotProve "jmEq2@Pattern{PWild}")
    jmEq2 PVar  PVar  = Just (cannotProve "jmEq2@Pattern{PVar}", cannotProve "jmEq2@Pattern{PVar}")
    jmEq2 (PDatum _ d1) (PDatum _ d2) =
        jmEq2_fake d1 d2
        where
        jmEq2_fake
            :: PDatumCode xss  vars1 a1
            -> PDatumCode xss' vars2 a2
            -> Maybe (TypeEq vars1 vars2, TypeEq a1 a2)
        jmEq2_fake =
            error "jmEq2@Pattern{PDatum}: can't recurse because Code isn't injective" -- so @xss@ and @xss'@ aren't guaranteed to be the same
    jmEq2 _ _ = Nothing

instance JmEq1 (Pattern vars) where
    jmEq1 p1 p2 = jmEq2 p1 p2 >>= \(_,proof) -> Just proof
#endif

instance Eq2 Pattern where
    eq2 PWild         PWild         = True
    eq2 PVar          PVar          = True
    eq2 (PDatum _ d1) (PDatum _ d2) = eq2 d1 d2
    eq2 _           _               = False

instance Eq1 (Pattern vars) where
    eq1 = eq2

instance Eq (Pattern vars a) where
    (==) = eq1

-- TODO: instance Read (Pattern vars a)

instance Show2 Pattern where
    showsPrec2 _ PWild           = showString     "PWild"
    showsPrec2 _ PVar            = showString     "PVar"
    showsPrec2 p (PDatum hint d) = showParen_02 p "PDatum" hint d

instance Show1 (Pattern vars) where
    showsPrec1 = showsPrec2
    show1      = show2

instance Show (Pattern vars a) where
    showsPrec = showsPrec1
    show      = show1

-- TODO: as necessary Functor22, Foldable22, Traversable22


----------------------------------------------------------------
data PDatumCode :: [[HakaruFun]] -> [Hakaru] -> Hakaru -> * where
    PInr :: !(PDatumCode  xss vars a) -> PDatumCode (xs ': xss) vars a
    PInl :: !(PDatumStruct xs vars a) -> PDatumCode (xs ': xss) vars a


#if __PARTIAL_DATUM_JMEQ__
instance JmEq2 (PDatumCode xss) where
    jmEq2 (PInr c) (PInr d) = jmEq2 c d
    jmEq2 (PInl c) (PInl d) = jmEq2 c d
    jmEq2 _        _        = Nothing

-- This instance works, but recurses into non-working instances.
instance JmEq1 (PDatumCode xss vars) where
    jmEq1 (PInr c) (PInr d) = jmEq1 c d
    jmEq1 (PInl c) (PInl d) = jmEq1 c d
    jmEq1 _        _        = Nothing
#endif

instance Eq2 (PDatumCode xss) where
    eq2 (PInr c) (PInr d) = eq2 c d
    eq2 (PInl c) (PInl d) = eq2 c d
    eq2 _        _        = False

instance Eq1 (PDatumCode xss vars) where
    eq1 = eq2

instance Eq (PDatumCode xss vars a) where
    (==) = eq1

-- TODO: instance Read (PDatumCode xss vars a)

instance Show2 (PDatumCode xss) where
    showsPrec2 p (PInr d) = showParen_2 p "PInr" d
    showsPrec2 p (PInl d) = showParen_2 p "PInl" d

instance Show1 (PDatumCode xss vars) where
    showsPrec1 = showsPrec2
    show1      = show2

instance Show (PDatumCode xss vars a) where
    showsPrec = showsPrec1
    show      = show1

-- TODO: as necessary Functor22, Foldable22, Traversable22

----------------------------------------------------------------
data PDatumStruct :: [HakaruFun] -> [Hakaru] -> Hakaru -> * where
    PEt :: !(PDatumFun    x         vars1 a)
        -> !(PDatumStruct xs        vars2 a)
        ->   PDatumStruct (x ': xs) (vars1 ++ vars2) a

    PDone :: PDatumStruct '[] '[] a


-- This block of recursive functions are analogous to 'JmEq2' except
-- we only return the equality proof for the penultimate index
-- rather than both the penultimate and ultimate index. (Because
-- we /can/ return proofs for the penultimate index, but not for
-- the ultimate.) This is necessary for defining the @Eq1 (PDatumStruct
-- xs vars)@ and @Eq1 (Branch a abt)@ instances, since we need to
-- make sure the existential @vars@ match up.

-- N.B., that we can use 'Refl' in the 'PVar' case relies on the
-- fact that the @a@ parameter is fixed to be the same in both
-- patterns.
jmEq_P :: Pattern vs a -> Pattern ws a -> Maybe (TypeEq vs ws)
jmEq_P PWild         PWild         = Just Refl
jmEq_P PVar          PVar          = Just Refl
jmEq_P (PDatum _ p1) (PDatum _ p2) = jmEq_PCode p1 p2
jmEq_P _             _             = Nothing

jmEq_PCode
    :: PDatumCode xss vs a
    -> PDatumCode xss ws a
    -> Maybe (TypeEq vs ws)
jmEq_PCode (PInr p1) (PInr p2) = jmEq_PCode   p1 p2
jmEq_PCode (PInl p1) (PInl p2) = jmEq_PStruct p1 p2
jmEq_PCode _         _         = Nothing

jmEq_PStruct
    :: PDatumStruct xs vs a
    -> PDatumStruct xs ws a
    -> Maybe (TypeEq vs ws)
jmEq_PStruct (PEt c1 c2) (PEt d1 d2) = do
    Refl <- jmEq_PFun    c1 d1
    Refl <- jmEq_PStruct c2 d2
    Just Refl
jmEq_PStruct PDone PDone = Just Refl
jmEq_PStruct _     _     = Nothing

jmEq_PFun :: PDatumFun f vs a -> PDatumFun f ws a -> Maybe (TypeEq vs ws)
jmEq_PFun (PKonst p1) (PKonst p2) = jmEq_P p1 p2
jmEq_PFun (PIdent p1) (PIdent p2) = jmEq_P p1 p2
jmEq_PFun _           _           = Nothing


#if __PARTIAL_DATUM_JMEQ__
instance JmEq2 (PDatumStruct xs) where
    jmEq2 (PEt c1 c2) (PEt d1 d2) = do
        (Refl, Refl) <- jmEq2 c1 d1
        (Refl, Refl) <- jmEq2 c2 d2
        Just (Refl, Refl)
    jmEq2 PDone PDone = Just (Refl, cannotProve "jmEq2@PDatumStruct{PDone}")
    jmEq2 _     _     = Nothing

instance JmEq1 (PDatumStruct xs vars) where
    jmEq1 p1 p2 = jmEq2 p1 p2 >>= \(_,proof) -> Just proof
#endif

instance Eq2 (PDatumStruct xs) where
    eq2 p1 p2 = maybe False (const True) $ jmEq_PStruct p1 p2

instance Eq1 (PDatumStruct xs vars) where
    eq1 = eq2

instance Eq (PDatumStruct xs vars a) where
    (==) = eq1

-- TODO: instance Read (PDatumStruct xs vars a)

instance Show2 (PDatumStruct xs) where
    showsPrec2 p (PEt d1 d2) = showParen_22 p "PEt" d1 d2
    showsPrec2 _ PDone       = showString     "PDone"

instance Show1 (PDatumStruct xs vars) where
    showsPrec1 = showsPrec2
    show1      = show2

instance Show (PDatumStruct xs vars a) where
    showsPrec = showsPrec1
    show      = show1

-- TODO: as necessary Functor22, Foldable22, Traversable22


----------------------------------------------------------------
data PDatumFun :: HakaruFun -> [Hakaru] -> Hakaru -> * where
    PKonst :: !(Pattern vars b) -> PDatumFun ('K b) vars a
    PIdent :: !(Pattern vars a) -> PDatumFun 'I     vars a


#if __PARTIAL_DATUM_JMEQ__
instance JmEq2 (PDatumFun x) where
    jmEq2 (PKonst p1) (PKonst p2) = do
        (Refl, Refl) <- jmEq2 p1 p2
        Just (Refl, cannotProve "jmEq2@PDatumFun{PKonst}")
    jmEq2 (PIdent p1) (PIdent p2) = jmEq2 p1 p2
    jmEq2 _ _ = Nothing

instance JmEq1 (PDatumFun x vars) where
    jmEq1 (PKonst e) (PKonst f) = do
        Refl <- jmEq1 e f
        Just (cannotProve "jmEq1@PDatumFun{PKonst}")
    jmEq1 (PIdent e) (PIdent f) = jmEq1 e f
    jmEq1 _          _          = Nothing
#endif

instance Eq2 (PDatumFun x) where
    eq2 (PKonst e) (PKonst f) = eq2 e f
    eq2 (PIdent e) (PIdent f) = eq2 e f
    eq2 _          _          = False

instance Eq1 (PDatumFun x vars) where
    eq1 = eq2

instance Eq (PDatumFun x vars a) where
    (==) = eq1

-- TODO: instance Read (PDatumFun x vars a)

instance Show2 (PDatumFun x) where
    showsPrec2 p (PKonst e) = showParen_2 p "PKonst" e
    showsPrec2 p (PIdent e) = showParen_2 p "PIdent" e

instance Show1 (PDatumFun x vars) where
    showsPrec1 = showsPrec2
    show1      = show2

instance Show (PDatumFun x vars a) where
    showsPrec = showsPrec1
    show      = show1

-- TODO: as necessary Functor22, Foldable22, Traversable22


----------------------------------------------------------------
pTrue, pFalse :: Pattern '[] HBool
pTrue  = PDatum tdTrue  . PInl $ PDone
pFalse = PDatum tdFalse . PInr . PInl $ PDone

pUnit  :: Pattern '[] HUnit
pUnit  = PDatum tdUnit . PInl $ PDone

-- HACK: using undefined like that isn't going to help if we use
-- the variant of eqAppendIdentity that actually needs the Sing...
varsOfPattern :: Pattern vars a -> proxy vars
varsOfPattern _ = error "TODO: varsOfPattern"

pPair
    :: Pattern vars1 a
    -> Pattern vars2 b
    -> Pattern (vars1 ++ vars2) (HPair a b)
pPair x y =
    case eqAppendIdentity (varsOfPattern y) of
    Refl -> PDatum tdPair . PInl $ PKonst x `PEt` PKonst y `PEt` PDone

pLeft :: Pattern vars a -> Pattern vars (HEither a b)
pLeft x =
    case eqAppendIdentity (varsOfPattern x) of
    Refl -> PDatum tdLeft . PInl $ PKonst x `PEt` PDone

pRight :: Pattern vars b -> Pattern vars (HEither a b)
pRight y =
    case eqAppendIdentity (varsOfPattern y) of
    Refl -> PDatum tdRight . PInr . PInl $ PKonst y `PEt` PDone

pNil :: Pattern '[] (HList a)
pNil = PDatum tdNil . PInl $ PDone

pCons :: Pattern vars1 a
    -> Pattern vars2 (HList a)
    -> Pattern (vars1 ++ vars2) (HList a)
pCons x xs = 
    case eqAppendIdentity (varsOfPattern xs) of
    Refl -> PDatum tdCons . PInr . PInl $ PKonst x `PEt` PIdent xs `PEt` PDone

pNothing :: Pattern '[] (HMaybe a)
pNothing = PDatum tdNothing . PInl $ PDone

pJust :: Pattern vars a -> Pattern vars (HMaybe a)
pJust x =
    case eqAppendIdentity (varsOfPattern x) of
    Refl -> PDatum tdJust . PInr . PInl $ PKonst x `PEt` PDone

----------------------------------------------------------------
-- TODO: a pretty infix syntax, like (:=>) or something?
--
-- TODO: this datatype is helpful for capturing the existential;
-- but other than that, it should be replaced\/augmented with a
-- type for pattern automata, so we can optimize case analysis.
--
-- TODO: if we used the argument order @Branch abt a b@ then we
-- could give @Foo2@ instances instead of just @Foo1@ instances.
-- Also would possibly let us talk about branches as profunctors
-- mapping @a@ to @b@. Would either of these actually be helpful
-- in practice for us?
data Branch
    (a   :: Hakaru)                  -- The type of the scrutinee.
    (abt :: [Hakaru] -> Hakaru -> *) -- The 'ABT' of the body.
    (b   :: Hakaru)                  -- The type of the body.
    = forall xs. Branch
        !(Pattern xs a)
        !(abt xs b)

instance Eq2 abt => Eq1 (Branch a abt) where
    eq1 (Branch p1 e1) (Branch p2 e2) =
        case jmEq_P p1 p2 of
        Nothing   -> False
        Just Refl -> eq2 e1 e2

instance Eq2 abt => Eq (Branch a abt b) where
    (==) = eq1

-- TODO: instance Read (Branch abt a b)

instance Show2 abt => Show1 (Branch a abt) where
    showsPrec1 p (Branch pat e) = showParen_22 p "Branch" pat e

instance Show2 abt => Show (Branch a abt b) where
    showsPrec = showsPrec1
    show      = show1

instance Functor21 (Branch a) where
    fmap21 f (Branch p e) = Branch p (f e)

instance Foldable21 (Branch a) where
    foldMap21 f (Branch _ e) = f e

instance Traversable21 (Branch a) where
    traverse21 f (Branch pat e) = Branch pat <$> f e

----------------------------------------------------------------
----------------------------------------------------------- fin.
