{-# LANGUAGE CPP
           , DataKinds
           , PolyKinds
           , GADTs
           , StandaloneDeriving
           , TypeOperators
           , TypeFamilies
           , Rank2Types
           #-}

{-# OPTIONS_GHC -Wall -fwarn-tabs #-}
----------------------------------------------------------------
--                                                    2015.10.23
-- |
-- Module      :  Language.Hakaru.Syntax.Datum
-- Copyright   :  Copyright (c) 2015 the Hakaru team
-- License     :  BSD3
-- Maintainer  :  wren@community.haskell.org
-- Stability   :  experimental
-- Portability :  GHC-only
--
-- Haskell types and helpers for Hakaru's user-defined data types.
-- At present we only support regular-recursive polynomial data
-- types. Reduction of case analysis on data types is in
-- "Language.Hakaru.Syntax.Datum".
----------------------------------------------------------------
module Language.Hakaru.Syntax.Datum
    (
    -- * Data constructors
      Datum(..), datumHint
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
#endif

import Language.Hakaru.Syntax.IClasses
import Language.Hakaru.Syntax.DataKind

----------------------------------------------------------------
----------------------------------------------------------------
-- TODO: add @Sing (HData' t)@ to the Datum constructor?
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
        -> !(DatumCode (Code t) ast (HData' t))
        -> Datum ast (HData' t)

datumHint :: Datum ast (HData' t) -> Text
datumHint (Datum hint _) = hint

instance Eq1 ast => Eq1 (Datum ast) where
    eq1 (Datum _ d1) (Datum _ d2) = eq1 d1 d2

instance Eq1 ast => Eq (Datum ast a) where
    (==) = eq1

-- TODO: instance Read (Datum ast a)

instance Show1 ast => Show1 (Datum ast) where
    showsPrec1 p (Datum hint d) = showParen_01 p "Datum" hint d

instance Show1 ast => Show (Datum ast a) where
    showsPrec = showsPrec1
    show      = show1

instance Functor11 Datum where
    fmap11 f (Datum hint d) = Datum hint (fmap11 f d)

instance Foldable11 Datum where
    foldMap11 f (Datum _ d) = foldMap11 f d


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
    -- | Skip rightwards along the sum.
    Inr :: !(DatumCode  xss abt a) -> DatumCode (xs ': xss) abt a
    -- | Inject into the sum.
    Inl :: !(DatumStruct xs abt a) -> DatumCode (xs ': xss) abt a


-- N.B., these \"Foo1\" instances rely on polymorphic recursion,
-- since the @code@ changes at each constructor. However, we don't
-- actually need to abstract over @code@ in order to define these
-- functions, because (1) we never existentially close over any
-- codes, and (2) the code is always getting smaller; so we have
-- a good enough inductive hypothesis from polymorphism alone.

instance Eq1 ast => Eq1 (DatumCode xss ast) where
    eq1 (Inr c) (Inr d) = eq1 c d
    eq1 (Inl c) (Inl d) = eq1 c d
    eq1 _       _       = False

-- TODO: instance Read (DatumCode xss abt a)

instance Show1 ast => Show1 (DatumCode xss ast) where
    showsPrec1 p (Inr d) = showParen_1 p "Inr" d
    showsPrec1 p (Inl d) = showParen_1 p "Inl" d

instance Show1 ast => Show (DatumCode xss ast a) where
    showsPrec = showsPrec1

instance Functor11 (DatumCode xss) where
    fmap11 f (Inr d) = Inr (fmap11 f d)
    fmap11 f (Inl d) = Inl (fmap11 f d)

instance Foldable11 (DatumCode xss) where
    foldMap11 f (Inr d) = foldMap11 f d
    foldMap11 f (Inl d) = foldMap11 f d


----------------------------------------------------------------
data DatumStruct :: [HakaruFun] -> (Hakaru -> *) -> Hakaru -> * where
    -- | Combine components of the product. (\"et\" means \"and\" in Latin)
    Et  :: !(DatumFun    x         abt a)
        -> !(DatumStruct xs        abt a)
        ->   DatumStruct (x ': xs) abt a

    -- | Close off the product.
    Done :: DatumStruct '[] abt a

instance Eq1 ast => Eq1 (DatumStruct xs ast) where
    eq1 (Et c1 c2) (Et d1 d2) = eq1 c1 d1 && eq1 c2 d2
    eq1 Done       Done       = True
    eq1 _          _          = False

-- TODO: instance Read (DatumStruct xs abt a)

instance Show1 ast => Show1 (DatumStruct xs ast) where
    showsPrec1 p (Et d1 d2) = showParen_11 p "Et" d1 d2
    showsPrec1 _ Done       = showString     "Done"

instance Show1 ast => Show (DatumStruct xs ast a) where
    showsPrec = showsPrec1

instance Functor11 (DatumStruct xs) where
    fmap11 f (Et d1 d2) = Et (fmap11 f d1) (fmap11 f d2)
    fmap11 _ Done       = Done

instance Foldable11 (DatumStruct xs) where
    foldMap11 f (Et d1 d2) = foldMap11 f d1 `mappend` foldMap11 f d2
    foldMap11 _ Done       = mempty


----------------------------------------------------------------
-- TODO: do we like those constructor names? Should we change them?
data DatumFun :: HakaruFun -> (Hakaru -> *) -> Hakaru -> * where
    -- | Hit a leaf which isn't a recursive component of the datatype.
    Konst :: !(ast b) -> DatumFun ('K b) ast a
    -- | Hit a leaf which is a recursive component of the datatype.
    Ident :: !(ast a) -> DatumFun 'I     ast a

instance Eq1 ast => Eq1 (DatumFun x ast) where
    eq1 (Konst e) (Konst f) = eq1 e f
    eq1 (Ident e) (Ident f) = eq1 e f
    eq1 _         _         = False

-- TODO: instance Read (DatumFun x abt a)

instance Show1 ast => Show1 (DatumFun x ast) where
    showsPrec1 p (Konst e) = showParen_1 p "Konst" e
    showsPrec1 p (Ident e) = showParen_1 p "Ident" e

instance Show1 ast => Show (DatumFun x ast a) where
    showsPrec = showsPrec1

instance Functor11 (DatumFun x) where
    fmap11 f (Konst e) = Konst (f e)
    fmap11 f (Ident e) = Ident (f e)

instance Foldable11 (DatumFun x) where
    foldMap11 f (Konst e) = f e
    foldMap11 f (Ident e) = f e


----------------------------------------------------------------
-- In GHC 7.8 we can make the monomorphic smart constructors into
-- pattern synonyms, but 7.8 can't handle anything polymorphic (but
-- GHC 7.10 can). For libraries (e.g., "Language.Hakaru.Syntax.Prelude")
-- we can use functions to construct our Case_ statements, so library
-- designers don't need pattern synonyms. Whereas, for the internal
-- aspects of the compiler, we need to handle all possible Datum
-- values, so the pattern synonyms wouldn't even be helpful.

dTrue, dFalse :: Datum ast HBool
dTrue      = Datum tdTrue  . Inl $ Done
dFalse     = Datum tdFalse . Inr . Inl $ Done

dUnit      :: Datum ast HUnit
dUnit      = Datum tdUnit . Inl $ Done

dPair      :: ast a -> ast b -> Datum ast (HPair a b)
dPair a b  = Datum tdPair . Inl $ Konst a `Et` Konst b `Et` Done

dLeft      :: ast a -> Datum ast (HEither a b)
dLeft      = Datum tdLeft . Inl . (`Et` Done) . Konst

dRight     :: ast b -> Datum ast (HEither a b)
dRight     = Datum tdRight . Inr . Inl . (`Et` Done) . Konst

dNil       :: Datum ast (HList a)
dNil       = Datum tdNil. Inl $ Done

dCons      :: ast a -> ast (HList a) -> Datum ast (HList a)
dCons x xs = Datum tdCons . Inr . Inl $ Konst x `Et` Ident xs `Et` Done

dNothing   :: Datum ast (HMaybe a)
dNothing   = Datum tdNothing . Inl $ Done

dJust      :: ast a -> Datum ast (HMaybe a)
dJust      = Datum tdJust . Inr . Inl . (`Et` Done) . Konst


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
    -- | The \"don't care\" wildcard pattern.
    PWild :: Pattern '[]    a

    -- | A pattern variable.
    PVar  :: Pattern '[ a ] a

    -- | A data type constructor pattern. As with the 'Datum'
    -- constructor, the first component is a hint.
    PDatum
        :: {-# UNPACK #-} !Text
        -> !(PDatumCode (Code t) vars (HData' t))
        -> Pattern vars (HData' t)

instance Eq1 (Pattern vars) where
    eq1 PWild         PWild         = True
    eq1 PVar          PVar          = True
    eq1 (PDatum _ d1) (PDatum _ d2) = eq1 d1 d2
    eq1 _           _               = False

instance Eq (Pattern vars a) where
    (==) = eq1

-- TODO: instance Read (Pattern vars a)

instance Show1 (Pattern vars) where
    showsPrec1 _ PWild           = showString     "PWild"
    showsPrec1 _ PVar            = showString     "PVar"
    showsPrec1 p (PDatum hint d) = showParen_01 p "PDatum" hint d

instance Show (Pattern vars a) where
    showsPrec = showsPrec1
    show      = show1


----------------------------------------------------------------
data PDatumCode :: [[HakaruFun]] -> [Hakaru] -> Hakaru -> * where
    PInr :: !(PDatumCode  xss vars a) -> PDatumCode (xs ': xss) vars a
    PInl :: !(PDatumStruct xs vars a) -> PDatumCode (xs ': xss) vars a

instance Eq1 (PDatumCode xss vars) where
    eq1 (PInr c) (PInr d) = eq1 c d
    eq1 (PInl c) (PInl d) = eq1 c d
    eq1 _        _        = False

-- TODO: instance Read (PDatumCode xss vars a)

instance Show1 (PDatumCode xss vars) where
    showsPrec1 p (PInr d) = showParen_1 p "PInr" d
    showsPrec1 p (PInl d) = showParen_1 p "PInl" d

instance Show (PDatumCode xss vars a) where
    showsPrec = showsPrec1


----------------------------------------------------------------
data PDatumStruct :: [HakaruFun] -> [Hakaru] -> Hakaru -> * where
    PEt :: !(PDatumFun    x         vars1 a)
        -> !(PDatumStruct xs        vars2 a)
        ->   PDatumStruct (x ': xs) (vars1 ++ vars2) a

    PDone :: PDatumStruct '[] '[] a

instance Eq1 (PDatumStruct xs vars) where
    eq1 (PEt c1 c2) (PEt d1 d2) =
        error "TODO: Eq1{PEt}: make sure existentials match up"
        -- > eq1 c1 d1 && eq1 c2 d2
        -- TODO: we could do it with some instance of @jmEq@; which is just further begging for making @jmEq@ into a kind-class (i.e., a typeclass indexed by a kind instead of by a type). /Could/ do it without that kind-class, but will be namespace ugliness
        -- TODO: maybe we could just push @jmEq@ into the 'Eq1' class like the other abt library on Haskage does?
    eq1 PDone       PDone       = True
    eq1 _           _           = False

-- TODO: instance Read (PDatumStruct xs vars a)

instance Show1 (PDatumStruct xs vars) where
    showsPrec1 p (PEt d1 d2) = showParen_11 p "PEt" d1 d2
    showsPrec1 _ PDone       = showString     "PDone"

instance Show (PDatumStruct xs vars a) where
    showsPrec = showsPrec1


----------------------------------------------------------------
data PDatumFun :: HakaruFun -> [Hakaru] -> Hakaru -> * where
    PKonst :: !(Pattern vars b) -> PDatumFun ('K b) vars a
    PIdent :: !(Pattern vars a) -> PDatumFun 'I     vars a

instance Eq1 (PDatumFun x vars) where
    eq1 (PKonst e) (PKonst f) = eq1 e f
    eq1 (PIdent e) (PIdent f) = eq1 e f
    eq1 _          _          = False

-- TODO: instance Read (PDatumFun x vars a)

instance Show1 (PDatumFun x vars) where
    showsPrec1 p (PKonst e) = showParen_1 p "PKonst" e
    showsPrec1 p (PIdent e) = showParen_1 p "PIdent" e

instance Show (PDatumFun x vars a) where
    showsPrec = showsPrec1


----------------------------------------------------------------
pTrue, pFalse :: Pattern '[] HBool
pTrue  = PDatum tpTrue  . PInl $ PDone
pFalse = PDatum tpFalse . PInr . PInl $ PDone

pUnit  :: Pattern '[] HUnit
pUnit  = PDatum tpUnit . PInl $ PDone

-- HACK: using undefined like that isn't going to help if we use the variant of eqAppendNil that actually needs the Sing...
varsOfPattern :: Pattern vars a -> proxy vars
varsOfPattern _ = error "TODO: varsOfPattern"

pPair
    :: Pattern vars1 a
    -> Pattern vars2 b
    -> Pattern (vars1 ++ vars2) (HPair a b)
pPair a b =
    case eqAppendNil (varsOfPattern b) of
    Refl -> PDatum tpPair . PInl $ PKonst a `PEt` PKonst b `PEt` PDone

pLeft :: Pattern vars a -> Pattern vars (HEither a b)
pLeft a =
    case eqAppendNil (varsOfPattern a) of
    Refl -> PDatum tpLeft . PInl $ PKonst a `PEt` PDone

pRight :: Pattern vars b -> Pattern vars (HEither a b)
pRight b =
    case eqAppendNil (varsOfPattern b) of
    Refl -> PDatum tpRight . PInr . PInl $ PKonst b `PEt` PDone

pNil :: Pattern '[] (HList a)
pNil = PDatum tpNil . PInl $ PDone

pCons :: Pattern vars1 a
    -> Pattern vars2 (HList a)
    -> Pattern (vars1 ++ vars2) (HList a)
pCons x xs = 
    case eqAppendNil (varsOfPattern xs) of
    Refl -> PDatum tpCons . PInr . PInl $ PKonst x `PEt` PIdent xs `PEt` PDone

pNothing :: Pattern '[] (HMaybe a)
pNothing = PDatum tpNothing . PInl $ PDone

pJust :: Pattern vars a -> Pattern vars (HMaybe a)
pJust a =
    case eqAppendNil (varsOfPattern a) of
    Refl -> PDatum tpJust . PInr . PInl $ PKonst a `PEt` PDone

----------------------------------------------------------------
tpTrue, tpFalse, tpUnit, tpPair, tpLeft, tpRight, tpNil, tpCons, tpNothing, tpJust :: Text
tpTrue    = Text.pack "pTrue"
tpFalse   = Text.pack "pFalse"
tpUnit    = Text.pack "pUnit"
tpPair    = Text.pack "pPair"
tpLeft    = Text.pack "pLeft"
tpRight   = Text.pack "pRight"
tpNil     = Text.pack "pNil"
tpCons    = Text.pack "pCons"
tpNothing = Text.pack "pNothing"
tpJust    = Text.pack "pJust"

----------------------------------------------------------------
----------------------------------------------------------------
-- TODO: a pretty infix syntax, like (:=>) or something
-- TODO: this type is helpful for capturing the existential, if we
-- ever end up keeping track of local binding environments; but
-- other than that, it should be replaced\/augmented with a type
-- for pattern automata, so we can optimize case analysis.
data Branch :: Hakaru -> ([Hakaru] -> Hakaru -> *) -> Hakaru -> * where
    Branch
        :: !(Pattern xs a)
        -> !(abt xs b)
        -> Branch a abt b

instance Eq2 abt => Eq1 (Branch a abt) where
    eq1 (Branch p1 e1) (Branch p2 e2) =
        error "TODO: Eq1{Branch}: make sure existentials match up"
        -- p1 `eq1` p2 && e1 `eq2` e2

instance Eq2 abt => Eq (Branch a abt b) where
    (==) = eq1

-- TODO: instance Read (Branch abt a b)

instance Show2 abt => Show1 (Branch a abt) where
    showsPrec1 p (Branch pat e) = showParen_02 p "Branch" pat e

instance Show2 abt => Show (Branch a abt b) where
    showsPrec = showsPrec1
    show      = show1

instance Functor21 (Branch a) where
    fmap21 f (Branch p e) = Branch p (f e)

instance Foldable21 (Branch a) where
    foldMap21 f (Branch _ e) = f e

----------------------------------------------------------------
----------------------------------------------------------- fin.
