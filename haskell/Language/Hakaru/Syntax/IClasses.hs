-- TODO: move this file somewhere else, like "Language.Hakaru.IClasses"
{-# LANGUAGE CPP
           , PolyKinds
           , DataKinds
           , TypeOperators
           , GADTs
           , TypeFamilies
           , Rank2Types
           , ScopedTypeVariables
           , ConstraintKinds
           , MultiParamTypeClasses
           , FlexibleInstances
           , UndecidableInstances
           #-}
{-# OPTIONS_GHC -Wall -fwarn-tabs #-}
----------------------------------------------------------------
--                                                    2016.04.28
-- |
-- Module      :  Language.Hakaru.Syntax.IClasses
-- Copyright   :  Copyright (c) 2016 the Hakaru team
-- License     :  BSD3
-- Maintainer  :  wren@community.haskell.org
-- Stability   :  experimental
-- Portability :  GHC-only
--
-- A collection of classes generalizing standard classes in order
-- to support indexed types.
--
-- TODO: DeriveDataTypeable for all our newtypes?
----------------------------------------------------------------
module Language.Hakaru.Syntax.IClasses
    (
    -- * Showing indexed types
      Show1(..), shows1, showList1
    , Show2(..), shows2, showList2
    -- ** Some more-generic helper functions for showing things
    , showListWith
    , showTuple
    -- ** some helpers for implementing the instances
    , showParen_0
    , showParen_1
    , showParen_2
    , showParen_01
    , showParen_02
    , showParen_11
    , showParen_12
    , showParen_22
    , showParen_010
    , showParen_011
    , showParen_111

    -- * Equality
    , Eq1(..)
    , Eq2(..)
    , TypeEq(..), symmetry, transitivity, congruence
    , JmEq1(..)
    , JmEq2(..)

    -- * Generalized abstract nonsense
    , Functor11(..), Fix11(..), cata11, ana11, hylo11
    , Functor12(..)
    , Functor21(..)
    , Functor22(..)
    , Foldable11(..), Lift1(..)
    , Foldable12(..)
    , Foldable21(..), Lift2(..)
    , Foldable22(..)
    , Traversable11(..)
    , Traversable12(..)
    , Traversable21(..)
    , Traversable22(..)

    -- * Helper types
    , Some1(..)
    , Some2(..)
    , Pair1(..), fst1, snd1
    , Pair2(..), fst2, snd2
    , Pointwise(..), PointwiseP(..)
    -- ** List types
    , type (++), eqAppendIdentity, eqAppendAssoc
    , List1(..), append1
    , List2(..)
    , DList1(..), toList1, fromList1, dnil1, dcons1, dsnoc1, dsingleton1, dappend1
    -- ** Constraints
    , All(..), Holds(..)
    ) where

import Prelude hiding   (id, (.))
import Control.Category (Category(..))
import Unsafe.Coerce    (unsafeCoerce)
import GHC.Exts         (Constraint)
#if __GLASGOW_HASKELL__ < 710
import Data.Monoid      (Monoid(..))
import Control.Applicative
#endif

----------------------------------------------------------------
----------------------------------------------------------------
-- TODO: cf., <http://hackage.haskell.org/package/abt-0.1.1.0>
-- | Uniform variant of 'Show' for @k@-indexed types. This differs
-- from @transformers:@'Data.Functor.Classes.Show1' in being
-- polykinded, like it ought to be.
--
-- Alas, I don't think there's any way to derive instances the way
-- we can derive for 'Show'.
class Show1 (a :: k -> *) where
    {-# MINIMAL showsPrec1 | show1 #-}

    showsPrec1 :: Int -> a i -> ShowS
    showsPrec1 _ x s = show1 x ++ s

    show1 :: a i -> String
    show1 x = shows1 x ""

shows1 :: (Show1 a) => a i -> ShowS
shows1 =  showsPrec1 0

showList1 :: (Show1 a) => [a i] -> ShowS
showList1 = showListWith shows1

{-
-- BUG: these require (Show (i::k)) in the class definition of Show1
instance Show1 Maybe where
    showsPrec1 = showsPrec
    show1      = show

instance Show1 [] where
    showsPrec1 = showsPrec
    show1      = show

instance Show1 ((,) a) where
    showsPrec1 = showsPrec
    show1      = show

instance Show1 (Either a) where
    showsPrec1 = showsPrec
    show1      = show
-}


----------------------------------------------------------------
-- TODO: how to show, in general, that @Show2 a@ implies @Show1 (a i)@ for all @i@... This is needed for 'Datum' which uses the 'LC_' trick...
class Show2 (a :: k1 -> k2 -> *) where
    {-# MINIMAL showsPrec2 | show2 #-}

    showsPrec2 :: Int -> a i j -> ShowS
    showsPrec2 _ x s = show2 x ++ s

    show2 :: a i j -> String
    show2 x = shows2 x ""

shows2 :: (Show2 a) => a i j -> ShowS
shows2 =  showsPrec2 0

showList2 :: Show2 a => [a i j] -> ShowS
showList2 = showListWith shows2


----------------------------------------------------------------
-- This implementation taken from 'showList' in base-4.8:"GHC.Show",
-- generalizing over the showing function. Looks like this is available from base-4.8.2.0:"Text.Show"
showListWith :: (a -> ShowS) -> [a] -> ShowS
showListWith f = start
    where
    start []     s = "[]" ++ s
    start (x:xs) s = '[' : f x (go xs)
        where
        go []     = ']' : s
        go (y:ys) = ',' : f y (go ys)


-- This implementation taken from 'show_tuple' in base-4.8:"GHC.Show",
-- verbatim.
showTuple :: [ShowS] -> ShowS
showTuple ss
    = showChar '('
    . foldr1 (\s r -> s . showChar ',' . r) ss
    . showChar ')'


showParen_0 :: Show a => Int -> String -> a -> ShowS
showParen_0 p s e =
    showParen (p > 9)
        ( showString s
        . showString " "
        . showsPrec 11 e
        )

showParen_1 :: Show1 a => Int -> String -> a i -> ShowS
showParen_1 p s e =
    showParen (p > 9)
        ( showString s
        . showString " "
        . showsPrec1 11 e
        )

showParen_2 :: Show2 a => Int -> String -> a i j -> ShowS
showParen_2 p s e =
    showParen (p > 9)
        ( showString s
        . showString " "
        . showsPrec2 11 e
        )

showParen_01 :: (Show b, Show1 a) => Int -> String -> b -> a i -> ShowS
showParen_01 p s e1 e2 =
    showParen (p > 9)
        ( showString s
        . showString " "
        . showsPrec  11 e1
        . showString " "
        . showsPrec1 11 e2
        )

showParen_02 :: (Show b, Show2 a) => Int -> String -> b -> a i j -> ShowS
showParen_02 p s e1 e2 =
    showParen (p > 9)
        ( showString s
        . showString " "
        . showsPrec  11 e1
        . showString " "
        . showsPrec2 11 e2
        )

showParen_11 :: (Show1 a, Show1 b) => Int -> String -> a i -> b j -> ShowS
showParen_11 p s e1 e2 =
    showParen (p > 9)
        ( showString s
        . showString " "
        . showsPrec1 11 e1
        . showString " "
        . showsPrec1 11 e2
        )

showParen_12 :: (Show1 a, Show2 b) => Int -> String -> a i -> b j l -> ShowS
showParen_12 p s e1 e2 =
    showParen (p > 9)
        ( showString s
        . showString " "
        . showsPrec1 11 e1
        . showString " "
        . showsPrec2 11 e2
        )

showParen_22 :: (Show2 a, Show2 b) => Int -> String -> a i1 j1 -> b i2 j2 -> ShowS
showParen_22 p s e1 e2 =
    showParen (p > 9)
        ( showString s
        . showString " "
        . showsPrec2 11 e1
        . showString " "
        . showsPrec2 11 e2
        )

showParen_010
    :: (Show a, Show1 b, Show c)
    => Int -> String -> a -> b i -> c -> ShowS
showParen_010 p s e1 e2 e3 =
    showParen (p > 9)
        ( showString s
        . showString " "
        . showsPrec  11 e1
        . showString " "
        . showsPrec1 11 e2
        . showString " "
        . showsPrec  11 e3
        )

showParen_011
    :: (Show a, Show1 b, Show1 c)
    => Int -> String -> a -> b i -> c j -> ShowS
showParen_011 p s e1 e2 e3 =
    showParen (p > 9)
        ( showString s
        . showString " "
        . showsPrec  11 e1
        . showString " "
        . showsPrec1 11 e2
        . showString " "
        . showsPrec1 11 e3
        )

showParen_111
    :: (Show1 a, Show1 b, Show1 c)
    => Int -> String -> a i -> b j -> c k -> ShowS
showParen_111 p s e1 e2 e3 =
    showParen (p > 9)
        ( showString s
        . showString " "
        . showsPrec1 11 e1
        . showString " "
        . showsPrec1 11 e2
        . showString " "
        . showsPrec1 11 e3
        )

----------------------------------------------------------------
----------------------------------------------------------------
-- | Uniform variant of 'Eq' for homogeneous @k@-indexed types.
-- N.B., we keep this separate from the 'JmEq1' class because for
-- some types we may be able to decide 'eq1' while not being able
-- to decide 'jmEq1' (e.g., if using phantom types rather than
-- GADTs). N.B., this function returns value\/term equality! That
-- is, the following four laws must hold relating the 'Eq1' class
-- to the 'Eq' class:
--
--     (1) if @eq1 x y == True@, then @x@ and @y@ have the same
--         type index and @(x == y) == True@
--     (2) if @eq1 x y == False@ where @x@ and @y@ have the same
--         type index, then @(x == y) == False@
--     (3) if @(x == y) == True@, then @eq1 x y == True@
--     (4) if @(x == y) == False@, then @eq1 x y == False@
--
-- Alas, I don't think there's any way to derive instances the way
-- we can derive for 'Eq'.
class Eq1 (a :: k -> *) where
    eq1 :: a i -> a i -> Bool
    -- TODO: how do we give the default instance for whenever we have a JmEq1 instance?
    -- TODO: is there a way to require the induced @Eq (a i)@ instance to be given?


class Eq2 (a :: k1 -> k2 -> *) where
    eq2 :: a i j -> a i j -> Bool



----------------------------------------------------------------
----------------------------------------------------------------
-- TODO: it'd be okay to use @(:~:)@ from "Data.Typeable" instead of defining our own. Except that one doesn't define the Category instance, symmetry, or congruence...

-- | Concrete proofs of type equality. In order to make use of a
-- proof @p :: TypeEq a b@, you must pattern-match on the 'Refl'
-- constructor in order to show GHC that the types @a@ and @b@ are
-- equal.
data TypeEq :: k -> k -> * where
    Refl :: TypeEq a a

instance Category TypeEq where
    id          = Refl
    Refl . Refl = Refl

-- | Type equality is symmetric.
symmetry :: TypeEq a b -> TypeEq b a
symmetry Refl = Refl

-- | Type equality is transitive. N.B., this is has a more general
-- type than @(.)@
transitivity :: TypeEq a b -> TypeEq b c -> TypeEq a c
transitivity Refl Refl = Refl

-- | Type constructors are extensional.
congruence :: TypeEq a b -> TypeEq (f a) (f b)
congruence Refl = Refl


-- TODO: Should we add an additional method which only checks for index equality, ignoring possible differences at the term\/value level?
--
-- | Uniform variant of 'Eq' for heterogeneous @k@-indexed types.
-- N.B., this function returns value\/term equality! That is, the
-- following four laws must hold relating the 'JmEq1' class to the
-- 'Eq1' class:
--
--     (1) if @jmEq1 x y == Just Refl@, then @x@ and @y@ have the
--         same type index and @eq1 x y == True@
--     (2) if @jmEq1 x y == Nothing@ where @x@ and @y@ have the
--         same type index, then @eq1 x y == False@
--     (3) if @eq1 x y == True@, then @jmEq1 x y == Just Refl@
--     (4) if @eq1 x y == False@, then @jmEq1 x y == Nothing@
--
-- Alas, I don't think there's any way to derive instances the way
-- we can derive for 'Eq'.
class Eq1 a => JmEq1 (a :: k -> *) where
    jmEq1 :: a i -> a j -> Maybe (TypeEq i j)

class Eq2 a => JmEq2 (a :: k1 -> k2 -> *) where
    jmEq2 :: a i1 j1 -> a i2 j2 -> Maybe (TypeEq i1 i2, TypeEq j1 j2)


----------------------------------------------------------------
----------------------------------------------------------------
-- TODO: rather than having this plethora of classes for different
-- indexing, define newtypes for 1-natural transformations, 2-natural
-- transformations, etc; and then define a single higher-order functor
-- class which is parameterized by the input and output categories.

-- | A functor on the category of @k@-indexed types (i.e., from
-- @k@-indexed types to @k@-indexed types). We unify the two indices,
-- because that seems the most helpful for what we're doing; we
-- could, of course, offer a different variant that maps @k1@-indexed
-- types to @k2@-indexed types...
--
-- Alas, I don't think there's any way to derive instances the way
-- we can derive for 'Functor'.
class Functor11 (f :: (k1 -> *) -> k2 -> *) where
    fmap11 :: (forall i. a i -> b i) -> f a j -> f b j

class Functor12 (f :: (k1 -> *) -> k2 -> k3 -> *) where
    fmap12 :: (forall i. a i -> b i) -> f a j l -> f b j l

-- | A functor from @(k1,k2)@-indexed types to @k3@-indexed types.
class Functor21 (f :: (k1 -> k2 -> *) -> k3 -> *) where
    fmap21 :: (forall h i. a h i -> b h i) -> f a j -> f b j


-- | A functor from @(k1,k2)@-indexed types to @(k3,k4)@-indexed types.
class Functor22 (f :: (k1 -> k2 -> *) -> k3 -> k4 -> *) where
    fmap22 :: (forall h i. a h i -> b h i) -> f a j l -> f b j l


----------------------------------------------------------------
newtype Fix11 (f :: (k -> *) -> k -> *) (i :: k) =
    Fix11 { unFix11 :: f (Fix11 f) i }

cata11
    :: forall f a j
    .  (Functor11 f)
    => (forall i. f a i -> a i)
    -> Fix11 f j -> a j
cata11 alg = go
    where
    go :: forall j'. Fix11 f j' -> a j'
    go = alg . fmap11 go . unFix11

ana11
    :: forall f a j
    .  (Functor11 f)
    => (forall i. a i -> f a i)
    -> a j -> Fix11 f j
ana11 coalg = go
    where
    go :: forall j'. a j' -> Fix11 f j'
    go = Fix11 . fmap11 go . coalg

hylo11
    :: forall f a b j
    .  (Functor11 f)
    => (forall i. a i -> f a i)
    -> (forall i. f b i -> b i)
    -> a j
    -> b j
hylo11 coalg alg = go
    where
    go :: forall j'. a j' -> b j'
    go = alg . fmap11 go . coalg

-- TODO: a tracing evaluator: <http://www.timphilipwilliams.com/posts/2013-01-16-fixing-gadts.html>


----------------------------------------------------------------
-- TODO: in theory we could define some Monoid1 class to avoid the
-- explicit dependency on Lift1 in fold1's type. But we'd need that
-- Monoid1 class to have some sort of notion of combining things
-- at different indices...

-- | A foldable functor on the category of @k@-indexed types.
--
-- Alas, I don't think there's any way to derive instances the way
-- we can derive for 'Foldable'.
class Functor11 f => Foldable11 (f :: (k1 -> *) -> k2 -> *) where
    {-# MINIMAL fold11 | foldMap11 #-}

    fold11 :: (Monoid m) => f (Lift1 m) i -> m
    fold11 = foldMap11 unLift1

    foldMap11 :: (Monoid m) => (forall i. a i -> m) -> f a j -> m
    foldMap11 f = fold11 . fmap11 (Lift1 . f)

-- TODO: standard Foldable wrappers 'and11', 'or11', 'all11', 'any11',...


class Functor12 f => Foldable12 (f :: (k1 -> *) -> k2 -> k3 -> *) where
    {-# MINIMAL fold12 | foldMap12 #-}

    fold12 :: (Monoid m) => f (Lift1 m) j l -> m
    fold12 = foldMap12 unLift1

    foldMap12 :: (Monoid m) => (forall i. a i -> m) -> f a j l -> m
    foldMap12 f = fold12 . fmap12 (Lift1 . f)

class Functor21 f => Foldable21 (f :: (k1 -> k2 -> *) -> k3 -> *) where
    {-# MINIMAL fold21 | foldMap21 #-}

    fold21 :: (Monoid m) => f (Lift2 m) j -> m
    fold21 = foldMap21 unLift2

    foldMap21 :: (Monoid m) => (forall h i. a h i -> m) -> f a j -> m
    foldMap21 f = fold21 . fmap21 (Lift2 . f)

class Functor22 f =>
    Foldable22 (f :: (k1 -> k2 -> *) -> k3 -> k4 -> *)
    where
    {-# MINIMAL fold22 | foldMap22 #-}

    fold22 :: (Monoid m) => f (Lift2 m) j l -> m
    fold22 = foldMap22 unLift2

    foldMap22 :: (Monoid m) => (forall h i. a h i -> m) -> f a j l -> m
    foldMap22 f = fold22 . fmap22 (Lift2 . f)

----------------------------------------------------------------
----------------------------------------------------------------
class Foldable11 t => Traversable11 (t :: (k1 -> *) -> k2 -> *) where
    traverse11
        :: Applicative f
        => (forall i. a i -> f (b i))
        -> t a j
        -> f (t b j)
    {-
    sequenceA :: Applicative f => t (f a) -> f (t a)
    mapM :: Monad m => (a -> m b) -> t a -> m (t b)
    sequence :: Monad m => t (m a) -> m (t a)
    -}

class Foldable12 t => Traversable12 (t :: (k1 -> *) -> k2 -> k3 -> *) where
    traverse12
        :: Applicative f
        => (forall i. a i -> f (b i))
        -> t a j l
        -> f (t b j l)

class Foldable21 t => Traversable21 (t :: (k1 -> k2 -> *) -> k3 -> *) where
    traverse21
        :: Applicative f
        => (forall h i. a h i -> f (b h i))
        -> t a j
        -> f (t b j)

class Foldable22 t =>
    Traversable22 (t :: (k1 -> k2 -> *) -> k3 -> k4 -> *)
    where
    traverse22
        :: Applicative f
        => (forall h i. a h i -> f (b h i))
        -> t a j l
        -> f (t b j l)

----------------------------------------------------------------
----------------------------------------------------------------
-- | Any unindexed type can be lifted to be (trivially) @k@-indexed.
newtype Lift1 (a :: *) (i :: k) =
    Lift1 { unLift1 :: a }
    deriving (Read, Show, Eq, Ord)

instance Show a => Show1 (Lift1 a) where
    showsPrec1 p (Lift1 x) = showsPrec p x
    show1        (Lift1 x) = show x

instance Eq a => Eq1 (Lift1 a) where
    eq1 (Lift1 a) (Lift1 b) = a == b


----------------------------------------------------------------
-- | Any unindexed type can be lifted to be (trivially) @(k1,k2)@-indexed.
newtype Lift2 (a :: *) (i :: k1) (j :: k2) =
    Lift2 { unLift2 :: a }
    deriving (Read, Show, Eq, Ord)

instance Show a => Show2 (Lift2 a) where
    showsPrec2 p (Lift2 x) = showsPrec p x
    show2        (Lift2 x) = show x

instance Show a => Show1 (Lift2 a i) where
    showsPrec1 p (Lift2 x) = showsPrec p x
    show1        (Lift2 x) = show x

instance Eq a => Eq2 (Lift2 a) where
    eq2 (Lift2 a) (Lift2 b) = a == b

instance Eq a => Eq1 (Lift2 a i) where
    eq1 (Lift2 a) (Lift2 b) = a == b

----------------------------------------------------------------
data Pointwise (f :: k0 -> *) (g :: k1 -> *) (x :: k0) (y :: k1) where
    Pw :: f x -> g y -> Pointwise f g x y

data PointwiseP (f :: k0 -> *) (g :: k1 -> *) (xy :: (k0, k1)) where
    PwP :: f x -> g y -> PointwiseP f g '(x,y)

----------------------------------------------------------------
-- BUG: haddock doesn't like annotations on GADT constructors. So
-- here we'll avoid using the GADT syntax, even though it'd make
-- the data type declaration prettier\/cleaner.
-- <https://github.com/hakaru-dev/hakaru/issues/6>
--
-- | Existentially quantify over a single index.
-- TODO: replace 'SomeVariable' with @(Some1 Variable)@
data Some1 (a :: k -> *)
    = forall i. Some1 !(a i)

instance Show1 a => Show (Some1 a) where
    showsPrec p (Some1 x) = showParen_1 p "Some1" x

instance JmEq1 a  => Eq (Some1 a) where
    Some1 x == Some1 y = maybe False (const True) (jmEq1 x y)


-- | Existentially quantify over two indices.
data Some2 (a :: k1 -> k2 -> *)
    = forall i j. Some2 !(a i j)

instance Show2 a => Show (Some2 a) where
    showsPrec p (Some2 x) = showParen_2 p "Some2" x

instance JmEq2 a  => Eq (Some2 a) where
    Some2 x == Some2 y = maybe False (const True) (jmEq2 x y)


----------------------------------------------------------------
-- | A lazy pairing of identically @k@-indexed values.
data Pair1 (a :: k -> *) (b :: k -> *) (i :: k) =
    Pair1 (a i) (b i)

fst1 :: Pair1 a b i -> a i
fst1 (Pair1 x _) = x

snd1 :: Pair1 a b i -> b i
snd1 (Pair1 _ y) = y

instance (Show1 a, Show1 b) => Show1 (Pair1 a b) where
    showsPrec1 p (Pair1 x y) = showParen_11 p "Pair1" x y

instance (Show1 a, Show1 b) => Show (Pair1 a b i) where
    showsPrec = showsPrec1
    show      = show1

-- TODO: derived Eq, JmEq, functor, foldable, traversable instances

----------------------------------------------------------------
-- | A lazy pairing of identically @(k1,k2)@-indexed values.
data Pair2 (a :: k1 -> k2 -> *) (b :: k1 -> k2 -> *) (i :: k1) (j :: k2) =
    Pair2 (a i j) (b i j)

fst2 :: Pair2 a b i j -> a i j
fst2 (Pair2 x _) = x

snd2 :: Pair2 a b i j -> b i j
snd2 (Pair2 _ y) = y

instance (Show2 a, Show2 b) => Show2 (Pair2 a b) where
    showsPrec2 p (Pair2 x y) = showParen_22 p "Pair2" x y

instance (Show2 a, Show2 b) => Show1 (Pair2 a b i) where
    showsPrec1 = showsPrec2
    show1      = show2

instance (Show2 a, Show2 b) => Show (Pair2 a b i j) where
    showsPrec = showsPrec1
    show      = show1

-- TODO: derived Eq, JmEq, functor, foldable, traversable instances


----------------------------------------------------------------
----------------------------------------------------------------
-- TODO: move all the list stuff off somewhere else

-- BUG: how do we actually use the term-level @(++)@ at the type level? Or do we have to redefine it ourselves (as below)? If we define it ourselves, how can we make sure it's usable? In particular, how can we prove associativity and that @'[]@ is a /two-sided/ identity element?
type family (xs :: [k]) ++ (ys :: [k]) :: [k] where
    '[]       ++ ys = ys
    (x ': xs) ++ ys = x ': (xs ++ ys)

{-
-- BUG: having the instances for @[[HakaruFun]]@ and @[HakaruFun]@ precludes giving a general kind-polymorphic data instance for type-level lists; so we have to monomorphize it to just the @[Hakaru]@ kind.
-- TODO: we should figure out some way to clean that up without introducing too much ambiguity\/overloading of the constructor names.
data instance Sing (xs :: [Hakaru]) where
    SNil  :: Sing ('[] :: [Hakaru])
    SCons :: !(Sing x) -> !(Sing xs) -> Sing ((x ': xs) :: [Hakaru])

-- BUG: ghc calls all these orphan instances, even though the data instance is defined here... Will that actually cause problems? Should we move this to TypeEq.hs?
instance Show1 (Sing :: [Hakaru] -> *) where
    showsPrec1 p s =
        case s of
        SNil        -> showString     "SNil"
        SCons s1 s2 -> showParen_11 p "SCons" s1 s2
instance Show (Sing (xs :: [Hakaru])) where
    showsPrec = showsPrec1
    show      = show1
instance SingI ('[] :: [Hakaru]) where
    sing = SNil
instance (SingI x, SingI xs) => SingI ((x ': xs) :: [Hakaru]) where
    sing = SCons sing sing
-}


-- | The empty list is (also) a right-identity for @('++')@. Because
-- we define @('++')@ by induction on the first argument, this
-- identity doesn't come for free but rather must be proven.
eqAppendIdentity :: proxy xs -> TypeEq xs (xs ++ '[])
-- This version should be used for runtime performance
eqAppendIdentity _ = unsafeCoerce Refl
{-
-- This version demonstrates that our use of unsafeCoerce is sound
-- BUG: to have an argument of type @Sing xs@, instead of an arbitrary @proxy xs@, we'd need to store the singleton somewhere (prolly in the 'Branch', for the use site in TypeCheck.hs) or else produce it somehow
eqAppendIdentity :: Sing (xs :: [Hakaru]) -> TypeEq xs (xs ++ '[])
eqAppendIdentity SNil        = Refl
eqAppendIdentity (SCons _ s) = case eqAppendIdentity s of Refl -> Refl
-}


-- To make a version that doesn't require proxies, we'd need to
-- enable -XAllowAmbiguousTypes. We'd need to do this even just to
-- drop the second or third proxies, which aren't needed for the
-- safe version.
--
-- | @('++')@ is associative. This identity doesn't come for free
-- but rather must be proven.
eqAppendAssoc
    :: proxy1 xs
    -> proxy2 ys
    -> proxy3 zs
    -> TypeEq ((xs ++ ys) ++ zs) (xs ++ (ys ++ zs))
-- This version should be used for runtime performance
eqAppendAssoc _ _ _ = unsafeCoerce Refl
{-
-- This version demonstrates that our use of unsafeCoerce is sound
-- BUG: to have the arguments be of type @Sing xs@, instead of arbitrary proxy types, we'd need to store the singletons somewhere (for the use site in TypeCheck.hs), but where?
eqAppendAssoc
    :: Sing (xs :: [Hakaru])
    -> Sing (ys :: [Hakaru])
    -> Sing (zs :: [Hakaru])
    -> TypeEq ((xs ++ ys) ++ zs) (xs ++ (ys ++ zs))
eqAppendAssoc SNil         _  _  = Refl
eqAppendAssoc (SCons _ sx) sy sz =
    case eqAppendAssoc sx sy sz of Refl -> Refl
-}

-- TODO: eqAppendNil :: proxy xs -> proxy ys -> TypeEq '[] (xs ++ ys) -> (TypeEq '[] xs, TypeEq '[] ys)


----------------------------------------------------------------
infixr 5 `Cons1`

-- | A /lazy/ list of @k@-indexed elements, itself indexed by the
-- list of indices
data List1 :: (k -> *) -> [k] -> * where
    Nil1  :: List1 a '[]
    Cons1 :: a x -> List1 a xs -> List1 a (x ': xs)


append1 :: List1 a xs -> List1 a ys -> List1 a (xs ++ ys)
append1 Nil1         ys = ys
append1 (Cons1 x xs) ys = Cons1 x (append1 xs ys)


instance Show1 a => Show1 (List1 a) where
    showsPrec1 _ Nil1         = showString     "Nil1"
    showsPrec1 p (Cons1 x xs) = showParen_11 p "Cons1" x xs

instance Show1 a => Show (List1 a xs) where
    showsPrec = showsPrec1
    show      = show1

instance JmEq1 a  => JmEq1 (List1 a) where
    jmEq1 Nil1         Nil1         = Just Refl
    jmEq1 (Cons1 x xs) (Cons1 y ys) =
        jmEq1 x  y  >>= \Refl ->
        jmEq1 xs ys >>= \Refl ->
        Just Refl
    jmEq1 _ _ = Nothing

instance Eq1 a  => Eq1 (List1 a) where
    eq1 Nil1         Nil1         = True
    eq1 (Cons1 x xs) (Cons1 y ys) = eq1 x y && eq1 xs ys

instance Eq1 a  => Eq (List1 a xs) where
    (==) = eq1

instance Functor11 List1 where
    fmap11 _ Nil1         = Nil1
    fmap11 f (Cons1 x xs) = Cons1 (f x) (fmap11 f xs)

instance Foldable11 List1 where
    foldMap11 _ Nil1         = mempty
    foldMap11 f (Cons1 x xs) = f x `mappend` foldMap11 f xs

instance Traversable11 List1 where
    traverse11 _ Nil1         = pure Nil1
    traverse11 f (Cons1 x xs) = Cons1 <$> f x <*> traverse11 f xs

----------------------------------------------------------------
-- | Lifting of relations pointwise to lists
data List2 :: (k0 -> k1 -> *) -> [k0] -> [k1] -> * where
  Nil2  :: List2 f '[] '[]
  Cons2 :: f x y -> List2 f xs ys -> List2 f (x ': xs) (y ': ys)

----------------------------------------------------------------
data Holds (c :: k -> Constraint) (x :: k) where
  Holds :: c x => Holds c x

class All (c :: k -> Constraint) (xs :: [k]) where
  allHolds :: List1 (Holds c) xs

instance All c '[] where allHolds = Nil1
instance (All c xs, c x)
  => All c (x ': xs) where allHolds = Cons1 Holds allHolds

----------------------------------------------------------------
-- TODO: cf the interface of <https://hackage.haskell.org/package/dlist-0.7.1.2/docs/Data-DList.html>
-- | A difference-list variant of 'List1'.
newtype DList1 a xs =
    DList1 { unDList1 :: forall ys. List1 a ys -> List1 a (xs ++ ys) }


toList1 :: DList1 a xs -> List1 a xs
toList1 dx@(DList1 xs) =
    case eqAppendIdentity dx of
    Refl -> xs Nil1

fromList1 :: List1 a xs -> DList1 a xs
fromList1 xs = DList1 (append1 xs)
    -- N.B., using @DList1 . append1@ doesn't type check

dnil1 :: DList1 a '[]
dnil1 = DList1 id

dcons1 :: a x -> DList1 a xs -> DList1 a (x ': xs)
dcons1 x (DList1 xs) = DList1 (Cons1 x . xs)

-- TODO: for this access pattern it's prolly better to define some @DListR@ where the index is in the reverse order of the list itself (or else uses type-level snoc-lists); that way we can avoid needing to use 'eqAppendAssoc' at every step...
dsnoc1 :: DList1 a xs -> a x -> DList1 a (xs ++ '[ x ])
dsnoc1 dx@(DList1 xs) x =
    DList1 $ \ys ->
        case eqAppendAssoc dx (dsingleton1 x) ys of
        Refl -> xs (Cons1 x ys)

-- HACK: we need to give this a top-level definition rather than
-- inlining it in order to prove that the resulting index is @[x]@
-- rather than possibly some other @(x:xs)@. No, I'm not sure why
-- GHC can't infer that...
dsingleton1 :: a x -> DList1 a '[ x ]
dsingleton1 x = DList1 (Cons1 x)

dappend1 :: DList1 a xs -> DList1 a ys -> DList1 a (xs ++ ys)
dappend1 dx@(DList1 xs) dy@(DList1 ys) =
    DList1 $ \zs ->
        case eqAppendAssoc dx dy zs of
        Refl -> xs (ys zs)

{-
instance Show1 a => Show1 (DList1 a) where
    showsPrec1 p xs =

instance Show1 a => Show (DList1 a xs) where
    showsPrec = showsPrec1
    show      = show1

instance JmEq1 a => JmEq1 (DList1 a) where
    jmEq1 xs ys =

instance Eq1 a => Eq1 (DList1 a) where
    eq1 xs ys =

instance Eq1 a => Eq (DList1 a xs) where
    (==) = eq1

instance Functor11 DList1 where
    fmap11 f xs =

instance Foldable11 DList1 where
    foldMap11 f xs =

instance Traversable11 DList1 where
    traverse11 f xs =
-}

----------------------------------------------------------------
----------------------------------------------------------- fin.
