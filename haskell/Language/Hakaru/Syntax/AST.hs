{-# LANGUAGE CPP
           , DataKinds
           , PolyKinds
           , GADTs
           , StandaloneDeriving
           , TypeOperators
           , TypeFamilies
           , FlexibleContexts
           , UndecidableInstances
           , Rank2Types
           , DeriveDataTypeable
           , LambdaCase
           #-}

{-# OPTIONS_GHC -Wall -fwarn-tabs #-}
----------------------------------------------------------------
--                                                    2016.02.21
-- |
-- Module      :  Language.Hakaru.Syntax.AST
-- Copyright   :  Copyright (c) 2016 the Hakaru team
-- License     :  BSD3
-- Maintainer  :  wren@community.haskell.org
-- Stability   :  experimental
-- Portability :  GHC-only
--
-- The generating functor for the raw syntax, along with various
-- helper types. For a more tutorial sort of introduction to how
-- things are structured here and in "Language.Hakaru.Syntax.ABT",
-- see <http://winterkoninkje.dreamwidth.org/103978.html>
--
-- TODO: are we finally at the place where we can get rid of all
-- those annoying underscores?
--
-- TODO: what is the runtime cost of storing all these dictionary
-- singletons? For existential type variables, it should be the
-- same as using a type class constraint; but for non-existential
-- type variables it'll, what, double the size of the AST?
----------------------------------------------------------------
module Language.Hakaru.Syntax.AST
    (
    -- * Syntactic forms
      SCon(..)
    , SArgs(..)
    , Term(..)
    , Transform(..), TransformImpl(..)
    , transformName, allTransforms
    -- * Operators
    , LC, LCs, UnLCs
    , LC_(..)
    , NaryOp(..)
    , PrimOp(..)
    , ArrayOp(..)
    , MeasureOp(..)
    -- * Constant values
    , Literal(..)
    
    -- * implementation details
    , foldMapPairs
    , traversePairs
    , module Language.Hakaru.Syntax.SArgs
    , module Language.Hakaru.Syntax.Transform
    ) where

import           Data.Sequence (Seq)
import qualified Data.Foldable as F
import qualified Data.List.NonEmpty as L
#if __GLASGOW_HASKELL__ < 710
import           Data.Monoid   (Monoid(..))
import           Control.Applicative
import           Data.Traversable
#endif

import           Control.Arrow ((***))
import           Data.Ratio    (numerator, denominator)

import Data.Data ()

import Data.Number.Natural
import Language.Hakaru.Syntax.IClasses
import Language.Hakaru.Types.DataKind
import Language.Hakaru.Types.Sing
import Language.Hakaru.Types.HClasses
import Language.Hakaru.Types.Coercion
import Language.Hakaru.Syntax.Datum
import Language.Hakaru.Syntax.Reducer
import Language.Hakaru.Syntax.ABT (ABT(syn))

import Language.Hakaru.Syntax.SArgs
import Language.Hakaru.Syntax.Transform

----------------------------------------------------------------
----------------------------------------------------------------
-- BUG: can't UNPACK 'Integer' and 'Natural' like we can for 'Int' and 'Nat'
--
-- | Numeric literals for the primitive numeric types. In addition
-- to being normal forms, these are also ground terms: that is, not
-- only are they closed (i.e., no free variables), they also have
-- no bound variables and thus no binding forms. Notably, we store
-- literals using exact types so that none of our program transformations
-- have to worry about issues like overflow or floating-point fuzz.
data Literal :: Hakaru -> * where
    LNat   :: !Natural -> Literal 'HNat
    LInt   :: !Integer -> Literal 'HInt
    LProb  :: {-# UNPACK #-} !NonNegativeRational -> Literal 'HProb
    LReal  :: {-# UNPACK #-} !Rational            -> Literal 'HReal

instance JmEq1 Literal where
    jmEq1 (LNat  x) (LNat  y) = if x == y then Just Refl else Nothing
    jmEq1 (LInt  x) (LInt  y) = if x == y then Just Refl else Nothing
    jmEq1 (LProb x) (LProb y) = if x == y then Just Refl else Nothing
    jmEq1 (LReal x) (LReal y) = if x == y then Just Refl else Nothing
    jmEq1 _         _         = Nothing

instance Eq1 Literal where
    eq1 (LNat  x) (LNat  y) = x == y
    eq1 (LInt  x) (LInt  y) = x == y
    eq1 (LProb x) (LProb y) = x == y
    eq1 (LReal x) (LReal y) = x == y
    -- Because of GADTs, the following is apparently redundant
    -- eq1 _         _          = False

instance Eq (Literal a) where
    (==) = eq1

-- TODO: instance Read (Literal a)

instance Show1 Literal where
    showsPrec1 p t =
        case t of
        LNat  v -> showParen_0 p "LNat"  v
        LInt  v -> showParen_0 p "LInt"  v
        LProb v -> showParen_0 p "LProb" v -- TODO: pretty print as decimals instead of using the Show Rational instance
        LReal v -> showParen_0 p "LReal" v -- TODO: pretty print as decimals instead of using the Show Rational instance

instance Show (Literal a) where
    showsPrec = showsPrec1
    show      = show1


-- TODO: first optimize the @Coercion a b@ to choose the most desirable of many equivalent paths?
instance Coerce Literal where
    coerceTo   CNil         v = v
    coerceTo   (CCons c cs) v = coerceTo cs (primCoerceTo c v)

    coerceFrom CNil         v = v
    coerceFrom (CCons c cs) v = primCoerceFrom c (coerceFrom cs v)

instance PrimCoerce Literal where
    primCoerceTo c =
        case c of
        Signed     HRing_Int        -> \(LNat  n) -> LInt  (nat2int   n)
        Signed     HRing_Real       -> \(LProb p) -> LReal (prob2real p)
        Continuous HContinuous_Prob -> \(LNat  n) -> LProb (nat2prob  n)
        Continuous HContinuous_Real -> \(LInt  i) -> LReal (int2real  i)
        where
        -- HACK: type signatures needed to avoid defaulting
        nat2int   :: Natural -> Integer
        nat2int   = fromNatural
        nat2prob  :: Natural -> NonNegativeRational
        nat2prob  = unsafeNonNegativeRational . toRational -- N.B., is actually safe here
        prob2real :: NonNegativeRational -> Rational
        prob2real = fromNonNegativeRational
        int2real  :: Integer -> Rational
        int2real  = fromIntegral

    primCoerceFrom c =
        case c of
        Signed     HRing_Int        -> \(LInt  i) -> LNat  (int2nat   i)
        Signed     HRing_Real       -> \(LReal r) -> LProb (real2prob r)
        Continuous HContinuous_Prob -> \(LProb p) -> LNat  (prob2nat  p)
        Continuous HContinuous_Real -> \(LReal r) -> LInt  (real2int  r)
        where
        -- HACK: type signatures needed to avoid defaulting
        -- TODO: how to handle the errors? Generate error code in hakaru? capture it in a monad?
        int2nat  :: Integer -> Natural
        int2nat x =
            case toNatural x of
            Just y  -> y
            Nothing -> error $ "primCoerceFrom@Literal: negative HInt " ++ show x
        prob2nat :: NonNegativeRational -> Natural
        prob2nat x =
            if denominator x == 1
            then numerator x
            else error $ "primCoerceFrom@Literal: non-integral HProb " ++ show x
        real2prob :: Rational -> NonNegativeRational
        real2prob x =
            case toNonNegativeRational x of
            Just y  -> y
            Nothing -> error $ "primCoerceFrom@Literal: negative HReal " ++ show x
        real2int :: Rational -> Integer
        real2int x =
            if denominator x == 1
            then numerator x
            else error $ "primCoerceFrom@Literal: non-integral HReal " ++ show x


----------------------------------------------------------------
-- TODO: helper functions for splitting NaryOp_ into components to group up like things. (e.g., grouping all the Literals together so we can do constant propagation)

-- | Primitive associative n-ary functions. By flattening the trees
-- for associative operators, we can more easily perform equivalence
-- checking and pattern matching (e.g., to convert @exp (a * log
-- b)@ into @b ** a@, regardless of whether @a@ is a product of
-- things or not). Notably, because of this encoding, we encode
-- things like subtraction and division by their unary operators
-- (negation and reciprocal).
--
-- We do not make any assumptions about whether these semigroups
-- are monoids, commutative, idempotent, or anything else. That has
-- to be handled by transformations, rather than by the AST itself.
data NaryOp :: Hakaru -> * where
    And  :: NaryOp HBool
    Or   :: NaryOp HBool
    Xor  :: NaryOp HBool
    -- N.B., even though 'Iff' is associative (in Boolean algebras),
    -- we should not support n-ary uses in our *surface* syntax.
    -- Because it's too easy for folks to confuse "a <=> b <=> c"
    -- with "(a <=> b) /\ (b <=> c)".
    Iff  :: NaryOp HBool -- == Not (Xor x y)

    -- These two don't necessarily have identity elements; thus,
    -- @NaryOp_ Min []@ and @NaryOp_ Max []@ may not be well-defined...
    -- TODO: check for those cases!
    Min  :: !(HOrd a) -> NaryOp a
    Max  :: !(HOrd a) -> NaryOp a

    Sum  :: !(HSemiring a) -> NaryOp a
    Prod :: !(HSemiring a) -> NaryOp a

    {-
    GCD  :: !(GCD_Domain a) -> NaryOp a
    LCM  :: !(GCD_Domain a) -> NaryOp a
    -}

-- TODO: instance Read (NaryOp a)
deriving instance Show (NaryOp a)

instance JmEq1 NaryOp where
    jmEq1 And      And      = Just Refl
    jmEq1 Or       Or       = Just Refl
    jmEq1 Xor      Xor      = Just Refl
    jmEq1 Iff      Iff      = Just Refl
    jmEq1 (Min  a) (Min  b) = jmEq1 (sing_HOrd a) (sing_HOrd b)
    jmEq1 (Max  a) (Max  b) = jmEq1 (sing_HOrd a) (sing_HOrd b)
    jmEq1 (Sum  a) (Sum  b) = jmEq1 a b
    jmEq1 (Prod a) (Prod b) = jmEq1 a b
    jmEq1 _        _        = Nothing

-- TODO: We could optimize this like we do for 'Literal'
instance Eq1 NaryOp where
    eq1 x y = maybe False (const True) (jmEq1 x y)

instance Eq (NaryOp a) where -- This one can be derived
    (==) = eq1


----------------------------------------------------------------
-- TODO: should we define our own datakind for @([Hakaru], Hakaru)@ or perhaps for the @/\a -> ([a], Hakaru)@ part of it?

-- BUG: how to declare that these are inverses?
type family LCs (xs :: [Hakaru]) :: [([Hakaru], Hakaru)] where
    LCs '[]       = '[]
    LCs (x ': xs) = LC x ': LCs xs

type family UnLCs (xs :: [([Hakaru], Hakaru)]) :: [Hakaru] where
    UnLCs '[]                  = '[]
    UnLCs ( '( '[], x ) ': xs) = x ': UnLCs xs


-- | Simple primitive functions, and constants. N.B., nothing in
-- here should produce or consume things of 'HMeasure' or 'HArray'
-- type (except perhaps in a totally polymorphic way).
data PrimOp :: [Hakaru] -> Hakaru -> * where

    -- -- -- Here we have /monomorphic/ operators
    -- -- The Boolean operators
    -- TODO: most of these we'll want to optimize away according
    -- to some circuit-minimization procedure. But we're not
    -- committing to any particular minimal complete set of primops
    -- just yet.
    -- N.B., general circuit minimization problem is Sigma_2^P-complete,
    -- which is outside of PTIME; so we'll just have to approximate
    -- it for now, or link into something like Espresso or an
    -- implementation of Quine–McCluskey
    -- cf., <https://hackage.haskell.org/package/qm-0.1.0.0/candidate>
    -- cf., <https://github.com/pfpacket/Quine-McCluskey>
    -- cf., <https://gist.github.com/dsvictor94/8db2b399a95e301c259a>
    Not  :: PrimOp '[ HBool ] HBool
    -- And, Or, Xor, Iff
    Impl :: PrimOp '[ HBool, HBool ] HBool
    -- Impl x y == Or (Not x) y
    Diff :: PrimOp '[ HBool, HBool ] HBool
    -- Diff x y == Not (Impl x y)
    Nand :: PrimOp '[ HBool, HBool ] HBool
    -- Nand aka Alternative Denial, Sheffer stroke
    Nor  :: PrimOp '[ HBool, HBool ] HBool
    -- Nor aka Joint Denial, aka Quine dagger, aka Pierce arrow
    --
    -- The remaining eight binops are completely uninteresting:
    --   flip Impl
    --   flip Diff
    --   const
    --   flip const
    --   (Not .) . const == const . Not
    --   (Not .) . flip const
    --   const (const True)
    --   const (const False)


    -- -- Trigonometry operators
    Pi    :: PrimOp '[] 'HProb -- TODO: maybe make this HContinuous polymorphic?
    -- TODO: if we're going to bother naming the hyperbolic ones, why not also name /a?(csc|sec|cot)h?/ eh?
    -- TODO: capture more domain information in these types?
    Sin   :: PrimOp '[ 'HReal ] 'HReal
    Cos   :: PrimOp '[ 'HReal ] 'HReal
    Tan   :: PrimOp '[ 'HReal ] 'HReal
    Asin  :: PrimOp '[ 'HReal ] 'HReal
    Acos  :: PrimOp '[ 'HReal ] 'HReal
    Atan  :: PrimOp '[ 'HReal ] 'HReal
    Sinh  :: PrimOp '[ 'HReal ] 'HReal
    Cosh  :: PrimOp '[ 'HReal ] 'HReal
    Tanh  :: PrimOp '[ 'HReal ] 'HReal
    Asinh :: PrimOp '[ 'HReal ] 'HReal
    Acosh :: PrimOp '[ 'HReal ] 'HReal
    Atanh :: PrimOp '[ 'HReal ] 'HReal


    -- -- Other Real\/Prob-valued operators
    -- N.B., we only give the safe\/exact versions here. The old
    -- more lenient versions now require explicit coercions. Some
    -- of those coercions are safe, but others are not. This way
    -- we're explicit about where things can fail.
    -- N.B., we also have @NatPow{'HReal} :: 'HReal -> 'HNat -> 'HReal@,
    -- but non-integer real powers of negative reals are not real numbers!
    -- TODO: may need @SafeFrom_@ in order to branch on the input
    -- in order to provide the old unsafe behavior.
    RealPow   :: PrimOp '[ 'HProb, 'HReal ] 'HProb
    Choose    :: PrimOp '[ 'HNat, 'HNat ] 'HNat
    -- ComplexPow :: PrimOp '[ 'HProb, 'HComplex ] 'HComplex
    -- is uniquely well-defined. Though we may want to implement
    -- it via @r**z = ComplexExp (z * RealLog r)@
    -- Defining @HReal -> HComplex -> HComplex@ requires either
    -- multivalued functions, or a choice of complex logarithm and
    -- making it discontinuous.
    Exp       :: PrimOp '[ 'HReal ] 'HProb
    Log       :: PrimOp '[ 'HProb ] 'HReal
    -- TODO: Log1p, Expm1
    Infinity  :: HIntegrable a -> PrimOp '[] a
    -- TODO: add Factorial as the appropriate type restriction of GammaFunc?
    GammaFunc :: PrimOp '[ 'HReal ] 'HProb
    BetaFunc  :: PrimOp '[ 'HProb, 'HProb ] 'HProb


    -- -- -- Here we have the /polymorphic/ operators

    -- -- HEq and HOrd operators
    -- TODO: equality doesn't make constructive sense on the reals...
    -- would it be better to constructivize our notion of total ordering?
    -- TODO: should we have LessEq as a primitive, rather than treating it as a macro?
    Equal :: !(HEq  a) -> PrimOp '[ a, a ] HBool
    Less  :: !(HOrd a) -> PrimOp '[ a, a ] HBool


    -- -- HSemiring operators (the non-n-ary ones)
    NatPow :: !(HSemiring a) -> PrimOp '[ a, 'HNat ] a
    -- TODO: would it help to have a specialized version for when
    -- we happen to know that the 'HNat is a Literal? Same goes for
    -- the other powers\/roots
    --
    -- TODO: add a specialized version which returns NonNegative
    -- when the power is even? N.B., be sure not to actually constrain
    -- it to HRing (necessary for calling it \"NonNegative\")


    -- -- HRing operators
    -- TODO: break these apart into a hierarchy of classes. N.B,
    -- there are two different interpretations of "abs" and "signum".
    -- On the one hand we can think of rings as being generated
    -- from semirings closed under subtraction/negation. From this
    -- perspective we have abs as a projection into the underlying
    -- semiring, and signum as a projection giving us the residual
    -- sign lost by the abs projection. On the other hand, we have
    -- the view of "abs" as a norm (i.e., distance to the "origin
    -- point"), which is the more common perspective for complex
    -- numbers and vector spaces; and relatedly, we have "signum"
    -- as returning the value on the unit (hyper)sphere, of the
    -- normalized unit vector. In another class, if we have a notion
    -- of an "origin axis" then we can have a function Arg which
    -- returns the angle to that axis, and therefore define signum
    -- in terms of Arg.
    -- Ring: Semiring + negate, abs, signum
    -- NormedLinearSpace: LinearSpace + originPoint, norm, Arg
    -- ??: NormedLinearSpace + originAxis, angle
    Negate :: !(HRing a) -> PrimOp '[ a ] a
    Abs    :: !(HRing a) -> PrimOp '[ a ] (NonNegative a)
    -- cf., <https://mail.haskell.org/pipermail/libraries/2013-April/019694.html>
    -- cf., <https://en.wikipedia.org/wiki/Sign_function#Complex_signum>
    -- Should we have Maple5's \"csgn\" as well as the usual \"sgn\"?
    -- Also note that the \"generalized signum\" anticommutes with Dirac delta!
    Signum :: !(HRing a) -> PrimOp '[ a ] a
    -- Law: x = coerceTo_ signed (abs_ x) * signum x
    -- More strictly/exactly, the result of Signum should be either
    -- zero or an @a@-unit value. For Int and Real, the units are
    -- +1 and -1. For Complex, the units are any point on the unit
    -- circle. For vectors, the units are any unit vector. Thus,
    -- more generally:
    -- Law : x = coerceTo_ signed (abs_ x) `scaleBy` signum x
    -- TODO: would it be worth defining the associated type of unit values for @a@? Probably...
    -- TODO: are there any salient types which support abs\/norm but
    -- do not have all units and thus do not support signum\/normalize?


    -- Coecion-like operations that are computations
    -- we only implement Floor for Prob for now?
    Floor :: PrimOp '[ 'HProb ] 'HNat

    -- -- HFractional operators
    Recip :: !(HFractional a) -> PrimOp '[ a ] a
    -- generates macro: IntPow


    -- -- HRadical operators
    -- TODO: flip argument order to match our prelude's @thRootOf@?
    NatRoot :: !(HRadical a) -> PrimOp '[ a, 'HNat ] a
    -- generates macros: Sqrt, NonNegativeRationalPow, and RationalPow


    -- -- HContinuous operators
    -- TODO: what goes here, if anything? cf., <https://en.wikipedia.org/wiki/Closed-form_expression#Comparison_of_different_classes_of_expressions>
    Erf :: !(HContinuous a) -> PrimOp '[ a ] a
    -- TODO: make Pi and Infinity HContinuous-polymorphic so that we can avoid the explicit coercion? Probably more mess than benefit.


-- TODO: instance Read (PrimOp args a)
deriving instance Show (PrimOp args a)

instance JmEq2 PrimOp where
    jmEq2 Not         Not         = Just (Refl, Refl)
    jmEq2 Impl        Impl        = Just (Refl, Refl)
    jmEq2 Diff        Diff        = Just (Refl, Refl)
    jmEq2 Nand        Nand        = Just (Refl, Refl)
    jmEq2 Nor         Nor         = Just (Refl, Refl)
    jmEq2 Pi          Pi          = Just (Refl, Refl)
    jmEq2 Sin         Sin         = Just (Refl, Refl)
    jmEq2 Cos         Cos         = Just (Refl, Refl)
    jmEq2 Tan         Tan         = Just (Refl, Refl)
    jmEq2 Asin        Asin        = Just (Refl, Refl)
    jmEq2 Acos        Acos        = Just (Refl, Refl)
    jmEq2 Atan        Atan        = Just (Refl, Refl)
    jmEq2 Sinh        Sinh        = Just (Refl, Refl)
    jmEq2 Cosh        Cosh        = Just (Refl, Refl)
    jmEq2 Tanh        Tanh        = Just (Refl, Refl)
    jmEq2 Asinh       Asinh       = Just (Refl, Refl)
    jmEq2 Acosh       Acosh       = Just (Refl, Refl)
    jmEq2 Atanh       Atanh       = Just (Refl, Refl)
    jmEq2 RealPow     RealPow     = Just (Refl, Refl)
    jmEq2 Exp         Exp         = Just (Refl, Refl)
    jmEq2 Log         Log         = Just (Refl, Refl)
    jmEq2 GammaFunc   GammaFunc   = Just (Refl, Refl)
    jmEq2 BetaFunc    BetaFunc    = Just (Refl, Refl)
    jmEq2 (Equal a)   (Equal b)   =
        jmEq1 (sing_HEq a) (sing_HEq b) >>= \Refl ->
        Just (Refl, Refl)
    jmEq2 (Less a)    (Less b)    =
        jmEq1 (sing_HOrd a) (sing_HOrd b) >>= \Refl ->
        Just (Refl, Refl)
    jmEq2 (Infinity a) (Infinity b) =
        jmEq1 (sing_HIntegrable a) (sing_HIntegrable b) >>= \Refl ->
        Just (Refl, Refl)
    jmEq2 (NatPow   a) (NatPow   b) = jmEq1 a b >>= \Refl -> Just (Refl, Refl)
    jmEq2 (Negate   a) (Negate   b) = jmEq1 a b >>= \Refl -> Just (Refl, Refl)
    jmEq2 (Abs      a) (Abs      b) = jmEq1 a b >>= \Refl -> Just (Refl, Refl)
    jmEq2 (Signum   a) (Signum   b) = jmEq1 a b >>= \Refl -> Just (Refl, Refl)
    jmEq2 (Recip    a) (Recip    b) = jmEq1 a b >>= \Refl -> Just (Refl, Refl)
    jmEq2 (NatRoot  a) (NatRoot  b) = jmEq1 a b >>= \Refl -> Just (Refl, Refl)
    jmEq2 (Erf      a) (Erf      b) = jmEq1 a b >>= \Refl -> Just (Refl, Refl)
    jmEq2 _ _ = Nothing

-- TODO: We could optimize this like we do for 'Literal'
instance Eq2 PrimOp where
    eq2 x y = maybe False (const True) (jmEq2 x y)

instance Eq1 (PrimOp args) where
    eq1 = eq2

instance Eq (PrimOp args a) where -- This one can be derived
    (==) = eq1

----------------------------------------------------------------
-- | Primitive operators for consuming or transforming arrays.
--
-- TODO: we may want to replace the 'Sing' arguments with something
-- more specific in order to capture any restrictions on what can
-- be stored in an array. Or, if we can get rid of them entirely
-- while still implementing all the use sites of
-- 'Language.Hakaru.Syntax.AST.Sing.sing_ArrayOp', that'd be
-- better still.
data ArrayOp :: [Hakaru] -> Hakaru -> * where
    -- HACK: is there any way we can avoid storing the Sing values here, while still implementing 'sing_PrimOp'?
    Index  :: !(Sing a) -> ArrayOp '[ 'HArray a, 'HNat ] a
    Size   :: !(Sing a) -> ArrayOp '[ 'HArray a ] 'HNat
    -- The first argument should be a monoid, but we don't enforce
    -- that; it's the user's responsibility.
    Reduce :: !(Sing a) -> ArrayOp '[ a ':-> a ':-> a, a, 'HArray a ] a
    -- TODO: would it make sense to have a specialized version for when the first argument is some \"Op\", in order to avoid the need for lambdas?

-- TODO: instance Read (ArrayOp args a)
deriving instance Show (ArrayOp args a)

instance JmEq2 ArrayOp where
    jmEq2 (Index  a) (Index  b) = jmEq1 a b >>= \Refl -> Just (Refl, Refl)
    jmEq2 (Size   a) (Size   b) = jmEq1 a b >>= \Refl -> Just (Refl, Refl)
    jmEq2 (Reduce a) (Reduce b) = jmEq1 a b >>= \Refl -> Just (Refl, Refl)
    jmEq2 _          _          = Nothing

-- TODO: We could optimize this like we do for 'Literal'
instance Eq2 ArrayOp where
    eq2 x y = maybe False (const True) (jmEq2 x y)

instance Eq1 (ArrayOp args) where
    eq1 = eq2

instance Eq (ArrayOp args a) where -- This one can be derived
    (==) = eq1


----------------------------------------------------------------
-- | Primitive operators to produce, consume, or transform
-- distributions\/measures. This corresponds to the old @Mochastic@
-- class, except that 'MBind' and 'Superpose_' are handled elsewhere
-- since they are not simple operators. (Also 'Dirac' is handled
-- elsewhere since it naturally fits with 'MBind', even though it
-- is a siple operator.)
--
-- TODO: we may want to replace the 'Sing' arguments with something
-- more specific in order to capture any restrictions on what can
-- be a measure space (e.g., to exclude functions). Or, if we can
-- get rid of them entirely while still implementing all the use
-- sites of 'Language.Hakaru.Syntax.AST.Sing.sing_MeasureOp',
-- that'd be better still.
data MeasureOp :: [Hakaru] -> Hakaru -> * where
    -- We might consider making Lebesgue and Counting polymorphic,
    -- since their restrictions to HProb and HNat are perfectly
    -- valid primitive measures. However, there are many other
    -- restrictions on measures we may want to consider, so handling
    -- these two here would only complicate matters.
    Lebesgue    :: MeasureOp '[ 'HReal, 'HReal ] 'HReal
    Counting    :: MeasureOp '[]                 'HInt
    Categorical :: MeasureOp '[ 'HArray 'HProb ] 'HNat
    -- TODO: make Uniform polymorphic, so that if the two inputs
    -- are HProb then we know the measure must be over HProb too.
    -- More generally, if the first input is HProb (since the second
    -- input is assumed to be greater thant he first); though that
    -- would be a bit ugly IMO.
    Uniform     :: MeasureOp '[ 'HReal, 'HReal ] 'HReal
    Normal      :: MeasureOp '[ 'HReal, 'HProb ] 'HReal
    Poisson     :: MeasureOp '[ 'HProb         ] 'HNat
    Gamma       :: MeasureOp '[ 'HProb, 'HProb ] 'HProb
    Beta        :: MeasureOp '[ 'HProb, 'HProb ] 'HProb

-- TODO: instance Read (MeasureOp typs a)
deriving instance Show (MeasureOp typs a)

instance JmEq2 MeasureOp where
    jmEq2 Lebesgue    Lebesgue    = Just (Refl, Refl)
    jmEq2 Counting    Counting    = Just (Refl, Refl)
    jmEq2 Categorical Categorical = Just (Refl, Refl)
    jmEq2 Uniform     Uniform     = Just (Refl, Refl)
    jmEq2 Normal      Normal      = Just (Refl, Refl)
    jmEq2 Poisson     Poisson     = Just (Refl, Refl)
    jmEq2 Gamma       Gamma       = Just (Refl, Refl)
    jmEq2 Beta        Beta        = Just (Refl, Refl)
    jmEq2 _           _           = Nothing

-- TODO: We could optimize this like we do for 'Literal'
instance Eq2 MeasureOp where
    eq2 x y = maybe False (const True) (jmEq2 x y)

instance Eq1 (MeasureOp typs) where
    eq1 = eq2

instance Eq (MeasureOp typs a) where -- This one can be derived
    (==) = eq1


----------------------------------------------------------------
----------------------------------------------------------------
-- N.B., the precedence of (:$) must be lower than (:*).
-- N.B., if these are changed, then be sure to update the Show instances
infix  4 :$ -- Chosen to be at the same precedence as (<$>) rather than ($)

-- | The constructor of a @(':$')@ node in the 'Term'. Each of these
-- constructors denotes a \"normal\/standard\/basic\" syntactic
-- form (i.e., a generalized quantifier). In the literature, these
-- syntactic forms are sometimes called \"operators\", but we avoid
-- calling them that so as not to introduce confusion vs 'PrimOp'
-- etc. Instead we use the term \"operator\" to refer to any primitive
-- function or constant; that is, non-binding syntactic forms. Also
-- in the literature, the 'SCon' type itself is usually called the
-- \"signature\" of the term language. However, we avoid calling
-- it that since our 'Term' has constructors other than just @(:$)@,
-- so 'SCon' does not give a complete signature for our terms.
--
-- The main reason for breaking this type out and using it in
-- conjunction with @(':$')@ and 'SArgs' is so that we can easily
-- pattern match on /fully saturated/ nodes. For example, we want
-- to be able to match @MeasureOp_ Uniform :$ lo :* hi :* End@
-- without needing to deal with 'App_' nodes nor 'viewABT'.
data SCon :: [([Hakaru], Hakaru)] -> Hakaru -> * where
    -- BUG: haddock doesn't like annotations on GADT constructors
    -- <https://github.com/hakaru-dev/hakaru/issues/6>

    -- -- Standard lambda calculus stuff
    Lam_ :: SCon '[ '( '[ a ], b ) ] (a ':-> b)
    App_ :: SCon '[ LC (a ':-> b ), LC a ] b
    Let_ :: SCon '[ LC a, '( '[ a ], b ) ] b
    -- TODO: a general \"@letrec*@\" version of let-binding so we can have mutual recursion
    --
    -- TODO: if we decide to add arbitrary fixedpoints back in, we
    -- should probably prefer only recursive-functions:
    -- `SCon '[ '( '[ a ':-> b, a ], a ':-> b ) ] (a ':-> b)`
    -- over than the previous recursive-everything:
    -- `SCon '[ '( '[ a ], a ) ] a`
    -- Or, if we really want to guarantee soundness, then we should
    -- only have the inductive principles for each HData.

    -- -- Type munging
    CoerceTo_   :: !(Coercion a b) -> SCon '[ LC a ] b
    UnsafeFrom_ :: !(Coercion a b) -> SCon '[ LC b ] a
    -- TODO: add something like @SafeFrom_ :: Coercion a b -> abt b -> Term abt ('HMaybe a)@ so we can capture the safety of patterns like @if_ (0 <= x) (let x_ = unsafeFrom signed x in...) (...)@ Of course, since we're just going to do case analysis on the result; why not make it a binding form directly?
    -- TODO: we'll probably want some more general thing to capture these sorts of patterns. For example, in the default implementation of Uniform we see: @if_ (lo < x && x < hi) (... unsafeFrom_ signed (hi - lo) ...) (...)@

    -- HACK: we must add the constraints that 'LCs' and 'UnLCs' are inverses, so that we have those in scope when doing case analysis (e.g., in TypeCheck.hs).
    -- As for this file itself, we can get it to typecheck by using 'UnLCs' in the argument rather than 'LCs' in the result; trying to do things the other way results in type inference issues in the typeclass instances for 'SCon'
    PrimOp_
        :: (typs ~ UnLCs args, args ~ LCs typs)
        => !(PrimOp typs a) -> SCon args a
    ArrayOp_
        :: (typs ~ UnLCs args, args ~ LCs typs)
        => !(ArrayOp typs a) -> SCon args a
    MeasureOp_
        :: (typs ~ UnLCs args, args ~ LCs typs)
        => !(MeasureOp typs a) -> SCon args ('HMeasure a)

    Dirac :: SCon '[ LC a ] ('HMeasure a)

    MBind :: SCon
        '[ LC ('HMeasure a)
        ,  '( '[ a ], 'HMeasure b)
        ] ('HMeasure b)

    -- TODO: unify Plate and Chain as @sequence@ a~la traversable?
    Plate :: SCon 
        '[ LC 'HNat
        , '( '[ 'HNat ], 'HMeasure a)
        ] ('HMeasure ('HArray a))


    -- TODO: if we swap the order of arguments to 'Chain', we could
    -- change the functional argument to be a binding form in order
    -- to avoid the need for lambdas. It'd no longer be trivial to
    -- see 'Chain' as an instance of @sequence@, but might be worth
    -- it... Of course, we also need to handle the fact that it's
    -- an array of transition functions; i.e., we could do:
    -- > chain n s0 $ \i s -> do {...}
    Chain :: SCon
        '[ LC 'HNat, LC s
        , '( '[ s ],  'HMeasure (HPair a s))
        ] ('HMeasure (HPair ('HArray a) s))


    -- -- Continuous and discrete integration.
    -- TODO: make Integrate and Summate polymorphic, so that if the
    -- two inputs are HProb then we know the function must be over
    -- HProb\/HNat too. More generally, if the first input is HProb
    -- (since the second input is assumed to be greater than the
    -- first); though that would be a bit ugly IMO.
    Integrate
        :: SCon '[ LC 'HReal, LC 'HReal, '( '[ 'HReal ], 'HProb) ] 'HProb
    -- TODO: the high and low bounds *should* be HInt. The only reason we use HReal is so that we can have infinite summations. Once we figure out a way to handle infinite bounds here, we can make the switch

    Summate
        :: HDiscrete a
        -> HSemiring b
        -> SCon '[ LC a, LC a, '( '[ a ], b) ] b

    Product
        :: HDiscrete a
        -> HSemiring b
        -> SCon '[ LC a, LC a, '( '[ a ], b) ] b

    -- Internalized program transformations
    Transform_ :: !(Transform as x)
               -> SCon as x

deriving instance Eq   (SCon args a)
-- TODO: instance Read (SCon args a)
deriving instance Show (SCon args a)

----------------------------------------------------------------
-- | The generating functor for Hakaru ASTs. This type is given in
-- open-recursive form, where the first type argument gives the
-- recursive form. The recursive form @abt@ does not have exactly
-- the same kind as @Term abt@ because every 'Term' represents a
-- locally-closed term whereas the underlying @abt@ may bind some
-- variables.
data Term :: ([Hakaru] -> Hakaru -> *) -> Hakaru -> * where
    -- BUG: haddock doesn't like annotations on GADT constructors
    -- <https://github.com/hakaru-dev/hakaru/issues/6>

    -- Simple syntactic forms (i.e., generalized quantifiers)
    (:$) :: !(SCon args a) -> !(SArgs abt args) -> Term abt a

    -- N-ary operators
    NaryOp_ :: !(NaryOp a) -> !(Seq (abt '[] a)) -> Term abt a

    -- TODO: 'Literal_', 'Empty_', 'Array_', and 'Datum_' are generalized quantifiers (to the same extent that 'Ann_', 'CoerceTo_', and 'UnsafeFrom_' are). Should we move them into 'SCon' just for the sake of minimizing how much lives in 'Term'? Or are they unique enough to be worth keeping here?

    -- Literal\/Constant values
    Literal_ :: !(Literal a) -> Term abt a

    -- These two constructors are here rather than in 'ArrayOp' because 'Array_' is a binding form; though it also means they're together with the other intro forms like 'Literal_' and 'Datum_'.
    --
    -- TODO: should we add a @Sing a@ argument to avoid ambiguity of 'Empty_'?
    Empty_ :: !(Sing ('HArray a)) -> Term abt ('HArray a)
    Array_
        :: !(abt '[] 'HNat)
        -> !(abt '[ 'HNat ] a)
        -> Term abt ('HArray a)

    ArrayLiteral_
        :: [abt '[] a]
        -> Term abt ('HArray a)

    -- Constructor for Reducers
    Bucket
        :: !(abt '[] 'HNat)
        -> !(abt '[] 'HNat)
        -> Reducer abt '[] a
        -> Term abt a
           
    -- -- User-defined data types
    -- BUG: even though the 'Datum' type has a single constructor, we get a warning about not being able to UNPACK it in 'Datum_'... wtf?
    --
    -- A data constructor applied to some expressions. N.B., this
    -- definition only accounts for data constructors which are
    -- fully saturated. Unsaturated constructors will need to be
    -- eta-expanded.
    Datum_ :: !(Datum (abt '[]) (HData' t)) -> Term abt (HData' t)

    -- Generic case-analysis (via ABTs and Structural Focalization).
    Case_ :: !(abt '[] a) -> [Branch a abt b] -> Term abt b

    -- Linear combinations of measures.
    Superpose_
        :: L.NonEmpty (abt '[] 'HProb, abt '[] ('HMeasure a))
        -> Term abt ('HMeasure a)

    -- The zero measure
    Reject_ :: !(Sing ('HMeasure a)) -> Term abt ('HMeasure a)

----------------------------------------------------------------
-- N.B., having a @singTerm :: Term abt a -> Sing a@ doesn't make
-- sense: That's what 'inferType' is for, but not all terms can be
-- inferred; some must be checked... Similarly, we can't derive
-- Read, since that's what typechecking is all about.


-- | A newtype of @abt '[]@, because sometimes we need this in order
-- to give instances for things. In particular, this is often used
-- to derive the obvious @Foo1 (abt '[])@ instance from an underlying
-- @Foo2 abt@ instance. The primary motivating example is to give
-- the 'Datum_' branch of the @Show1 (Term abt)@ instance.
newtype LC_ (abt :: [Hakaru] -> Hakaru -> *) (a :: Hakaru) =
    LC_ { unLC_ :: abt '[] a }

instance Show2 abt => Show1 (LC_ abt) where
    showsPrec1 p = showsPrec2 p . unLC_
    show1        = show2        . unLC_

-- Alas, these two instances require importing ABT.hs
-- HACK: these instances require -XUndecidableInstances
instance ABT Term abt => Coerce (LC_ abt) where
    coerceTo   CNil e       = e
    coerceTo   c    (LC_ e) = LC_ (syn (CoerceTo_ c :$ e :* End))

    coerceFrom CNil e       = e
    coerceFrom c    (LC_ e) = LC_ (syn (UnsafeFrom_ c :$ e :* End))

instance ABT Term abt => Coerce (Term abt) where
    coerceTo   CNil e = e
    coerceTo   c    e = CoerceTo_ c :$ syn e :* End

    coerceFrom CNil e = e
    coerceFrom c    e = UnsafeFrom_ c :$ syn e :* End

instance Show2 abt => Show1 (Term abt) where
    showsPrec1 p t =
        case t of
        o :$ es ->
            showParen (p > 4)
                ( showsPrec  (p+1) o
                . showString " :$ "
                . showsPrec1 (p+1) es
                )
        NaryOp_ o es ->
            showParen (p > 9)
                ( showString "NaryOp_ "
                . showsPrec  11 o
                . showString " "
                . showParen True
                    ( showString "Seq.fromList "
                    . showList2 (F.toList es)
                    )
                )
        Literal_ v       -> showParen_0   p "Literal_" v
        Empty_ _         -> showString      "Empty_"
        Array_ e1 e2     -> showParen_22  p "Array_" e1 e2
        ArrayLiteral_ es -> showParen (p > 9) (showString "ArrayLiteral_" . showList2 es)
        Datum_ d         -> showParen_1   p "Datum_" (fmap11 LC_ d)
        Case_  e bs      ->
            showParen (p > 9)
                ( showString "Case_ "
                . showsPrec2 11 e
                . showString " "
                . showList1 bs
                )
        Bucket _ _ _   -> showString "Bucket ..."
        Superpose_ pes ->
            showParen (p > 9)
                ( showString "Superpose_ "
                . showListWith
                    (\(e1,e2) -> showTuple [shows2 e1, shows2 e2])
                    (L.toList pes)
                )
        Reject_ _     -> showString      "Reject_"

instance Show2 abt => Show (Term abt a) where
    showsPrec = showsPrec1
    show      = show1


----------------------------------------------------------------
instance Functor21 Term where
    fmap21 f (o :$ es)          = o :$ fmap21 f es
    fmap21 f (NaryOp_    o  es) = NaryOp_    o (fmap f es)
    fmap21 _ (Literal_   v)     = Literal_   v
    fmap21 _ (Empty_ t)         = Empty_ t
    fmap21 f (Array_     e1 e2) = Array_     (f e1) (f e2)
    fmap21 f (ArrayLiteral_ es) = ArrayLiteral_ (fmap f es)
    fmap21 f (Datum_     d)     = Datum_     (fmap11 f d)
    fmap21 f (Case_      e  bs) = Case_      (f e)  (map (fmap21 f) bs)
    fmap21 f (Bucket     b e r) = Bucket (f b) (f e) (fmap22 f r)
    fmap21 f (Superpose_ pes)   = Superpose_ (L.map (f *** f) pes)
    fmap21 _ (Reject_ t)        = Reject_ t


----------------------------------------------------------------
instance Foldable21 Term where
    foldMap21 f (_ :$ es)          = foldMap21 f es
    foldMap21 f (NaryOp_    _  es) = F.foldMap f es
    foldMap21 _ (Literal_   _)     = mempty
    foldMap21 _ (Empty_     _)     = mempty
    foldMap21 f (Array_     e1 e2) = f e1 `mappend` f e2
    foldMap21 f (ArrayLiteral_ es) = F.foldMap f es
    foldMap21 f (Datum_     d)     = foldMap11 f d
    foldMap21 f (Case_      e  bs) = f e `mappend` F.foldMap (foldMap21 f) bs
    foldMap21 f (Bucket     b e r) = f b `mappend` f e `mappend` foldMap22 f r
    foldMap21 f (Superpose_ pes)   = foldMapPairs f pes
    foldMap21 _ (Reject_    _)     = mempty

foldMapPairs
    :: (Monoid m, F.Foldable f)
    => (forall h i. abt h i -> m)
    -> f (abt xs a, abt ys b)
    -> m
foldMapPairs f = F.foldMap $ \(e1,e2) -> f e1 `mappend` f e2


----------------------------------------------------------------
instance Traversable21 Term where
    traverse21 f (o :$ es)          = (o :$) <$> traverse21 f es
    traverse21 f (NaryOp_    o  es) = NaryOp_  o <$> traverse f es
    traverse21 _ (Literal_   v)     = pure $ Literal_ v
    traverse21 _ (Empty_     typ)   = pure $ Empty_   typ
    traverse21 f (Array_     e1 e2) = Array_ <$> f e1 <*> f e2
    traverse21 f (ArrayLiteral_ es) = ArrayLiteral_ <$> traverse f es
    traverse21 f (Bucket b e r)     = Bucket <$> f b <*> f e <*> traverse22 f r
    traverse21 f (Datum_     d)     = Datum_ <$> traverse11 f d
    traverse21 f (Case_      e  bs) = Case_  <$> f e <*> traverse (traverse21 f) bs
    traverse21 f (Superpose_ pes)   = Superpose_ <$> traversePairs f pes
    traverse21 _ (Reject_    typ)   = pure $ Reject_  typ

traversePairs
    :: (Applicative f, Traversable t)
    => (forall h i. abt1 h i -> f (abt2 h i))
    -> t (abt1 xs a, abt1 ys b)
    -> f (t (abt2 xs a, abt2 ys b))
traversePairs f = traverse $ \(x,y) -> (,) <$> f x <*> f y

----------------------------------------------------------------
----------------------------------------------------------- fin.
