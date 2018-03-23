{-# LANGUAGE TypeOperators
           , KindSignatures
           , DataKinds
           , TypeFamilies
           , GADTs
           , FlexibleInstances
           , NoImplicitPrelude
           , ScopedTypeVariables
           , FlexibleContexts
           , Rank2Types
           #-}

{-# OPTIONS_GHC -Wall -fwarn-tabs #-}
----------------------------------------------------------------
--                                                    2016.04.22
-- |
-- Module      :  Language.Hakaru.Syntax.Prelude
-- Copyright   :  Copyright (c) 2016 the Hakaru team
-- License     :  BSD3
-- Maintainer  :  wren@community.haskell.org
-- Stability   :  experimental
-- Portability :  GHC-only
--
-- A replacement for Haskell's Prelude, using the familiar symbols
-- in order to construct 'AST's and 'ABT's. This is only necessary
-- if we want to use Hakaru as an embedded language in Haskell, but
-- it also provides some examples of how to use the infrastructure.
--
-- TODO: is there a way to get rid of the need to specify @'[]@ everywhere in here? Some sort of distinction between the Var vs the Open parts of View?
----------------------------------------------------------------
module Language.Hakaru.Syntax.Prelude
    (
    -- * Basic syntax
    -- ** Types and coercions
      ann_, triv, memo
    , coerceTo_, fromProb, nat2int, nat2prob, fromInt, nat2real
    , unsafeFrom_, unsafeProb, unsafeProbFraction, unsafeProbFraction_, unsafeProbSemiring, unsafeProbSemiring_
    -- ** Numeric literals
    , literal_, nat_, int_, prob_, real_
    , fromRational, half, third
    -- ** Booleans
    , true, false, bool_, if_
    , not, (&&), and, (||), or, nand, nor
    -- ** Equality and ordering
    , (==), (/=), (<), (<=), (>), (>=), min, minimum, max, maximum
    -- ** Semirings
    , zero, zero_, one, one_, (+), sum, (*), prod, (^), square
    , unsafeMinusNat, unsafeMinusProb, unsafeMinus, unsafeMinus_
    , unsafeDiv, unsafeDiv_
    -- ** Rings
    , (-), negate, negative, abs, abs_, signum
    -- ** Fractional
    , (/), recip, (^^)
    -- ** Radical
    , sqrt, thRootOf
    -- ** Integration
    , integrate, summate, product
    -- ** Continuous
    , RealProb(..), Integrable(..)
    , betaFunc
    , log, logBase
    , negativeInfinity
    -- *** Trig
    , sin, cos, tan, asin, acos, atan, sinh, cosh, tanh, asinh, acosh, atanh
    -- Choose
    , choose
    -- *** coercions-that-compute
    , floor
    
    -- * Measures
    -- ** Abstract nonsense
    , dirac, (<$>), (<*>), (<*), (*>), (>>=), (>>), bindx, liftM2
    -- ** Linear operators
    , superpose, (<|>)
    , weight, withWeight, weightedDirac
    , reject, guard, withGuard
    -- ** Measure operators
    -- | When two versions of the same operator are given, the one without the prime builds an AST using the built-in operator, whereas the one with the prime is a default definition in terms of more primitive measure operators.
    , lebesgue, lebesgue'
    , counting
    , densityCategorical, categorical, categorical'
    , densityUniform, uniform, uniform'
    , densityNormal, normal, normal'
    , densityPoisson, poisson, poisson'
    , densityGamma, gamma, gamma'
    , densityBeta, beta, beta', beta''
    , plateWithVar, plate, plate'
    , chain, chain'
    , invgamma
    , exponential
    , chi2
    , cauchy
    , laplace
    , studentT
    , weibull
    , bern
    , mix
    , binomial
    , negativeBinomial
    , geometric
    , multinomial
    , dirichlet

    -- * Data types (other than booleans)
    , datum_
    -- * Case and Branch
    , case_, branch
    -- ** HUnit
    , unit
    -- ** HPair
    , pair, pair_, unpair, fst, snd, swap
    -- ** HEither
    , left, right, uneither
    -- ** HMaybe
    , nothing, just, maybe, unmaybe
    -- ** HList
    , nil, cons, list

    -- * Lambda calculus
    , lam, lamWithVar, let_, letM
    , app, app2, app3

    -- * Arrays
    , empty, arrayWithVar, array, arrayLit, (!), size, reduce
    , sumV, summateV, appendV, mapV, mapWithIndex, normalizeV, constV, unitV, zipWithV

    -- * Implementation details
    , primOp0_, primOp1_, primOp2_, primOp3_
    , arrayOp0_, arrayOp1_, arrayOp2_, arrayOp3_
    , measure0_, measure1_, measure2_
    , unsafeNaryOp_, naryOp_withIdentity, naryOp2_

    -- * Reducers
    , bucket, r_fanout, r_index, r_split, r_nop, r_add

    ) where

-- TODO: implement and use Prelude's fromInteger and fromRational, so we can use numeric literals!
import Prelude (Maybe(..), Functor(..), Bool(..), Integer, Rational, ($), flip, const, error)
import qualified Prelude
import           Data.Sequence       (Seq)
import qualified Data.Sequence       as Seq
import qualified Data.Text           as Text
import           Data.List.NonEmpty  (NonEmpty(..))
import qualified Data.List.NonEmpty  as L
import           Data.Semigroup      (Semigroup(..))
import           Control.Category    (Category(..))
import           Control.Monad       (return)
import           Control.Monad.Fix

import Data.Number.Natural
import Language.Hakaru.Types.DataKind
import Language.Hakaru.Types.Sing (Sing(..), SingI(sing), sUnPair, sUnEither, sUnMaybe, sUnMeasure, sUnArray)
import Language.Hakaru.Syntax.TypeOf
import Language.Hakaru.Types.HClasses
import Language.Hakaru.Types.Coercion
import Language.Hakaru.Syntax.Reducer
import Language.Hakaru.Syntax.AST
import Language.Hakaru.Syntax.Datum
import Language.Hakaru.Syntax.ABT hiding (View(..))

----------------------------------------------------------------
----- Helper combinators for defining our EDSL
{-
Below we implement a lot of simple optimizations; however, these
optimizations only apply if the client uses the type class methods
to produce the AST. We should implement a stand-alone function which
performs these sorts of optimizations, as a program transformation.
-}
-- TODO: constant propogation

-- TODO: NBE to get rid of administrative redexes.
app :: (ABT Term abt) => abt '[] (a ':-> b) -> abt '[] a -> abt '[] b
app e1 e2 = syn (App_ :$ e1 :* e2 :* End)

app2 :: (ABT Term abt) => abt '[] (a ':-> b ':-> c) -> abt '[] a -> abt '[] b -> abt '[] c
app2 = (app .) . app

app3 :: (ABT Term abt) => abt '[] (a ':-> b ':-> c ':-> d) -> abt '[] a -> abt '[] b -> abt '[] c -> abt '[] d
app3 = (app2 .) . app

triv :: TrivialABT Term '[] a -> TrivialABT Term '[] a
triv = id

memo :: MemoizedABT Term '[] a -> MemoizedABT Term '[] a
memo = id

primOp0_ :: (ABT Term abt) => PrimOp '[] a -> abt '[] a
primOp0_ o = syn (PrimOp_ o :$ End)

primOp1_
    :: (ABT Term abt)
    => PrimOp '[ a ] b
    -> abt '[] a -> abt '[] b
primOp1_ o e1 = syn (PrimOp_ o :$ e1 :* End)

primOp2_
    :: (ABT Term abt)
    => PrimOp '[ a, b ] c
    -> abt '[] a -> abt '[] b -> abt '[] c
primOp2_ o e1 e2 = syn (PrimOp_ o :$ e1 :* e2 :* End)

primOp3_
    :: (ABT Term abt)
    => PrimOp '[ a, b, c ] d
    -> abt '[] a -> abt '[] b -> abt '[] c -> abt '[] d
primOp3_ o e1 e2 e3 = syn (PrimOp_ o :$ e1 :* e2 :* e3 :* End)

arrayOp0_ :: (ABT Term abt) => ArrayOp '[] a -> abt '[] a
arrayOp0_ o = syn (ArrayOp_ o :$ End)

arrayOp1_
    :: (ABT Term abt)
    => ArrayOp '[ a ] b
    -> abt '[] a -> abt '[] b
arrayOp1_ o e1 = syn (ArrayOp_ o :$ e1 :* End)

arrayOp2_
    :: (ABT Term abt)
    => ArrayOp '[ a, b ] c
    -> abt '[] a -> abt '[] b -> abt '[] c
arrayOp2_ o e1 e2 = syn (ArrayOp_ o :$ e1 :* e2 :* End)

arrayOp3_
    :: (ABT Term abt)
    => ArrayOp '[ a, b, c ] d
    -> abt '[] a -> abt '[] b -> abt '[] c -> abt '[] d
arrayOp3_ o e1 e2 e3 = syn (ArrayOp_ o :$ e1 :* e2 :* e3 :* End)

measure0_ :: (ABT Term abt) => MeasureOp '[] a -> abt '[] ('HMeasure a)
measure0_ o = syn (MeasureOp_ o :$ End)

measure1_
    :: (ABT Term abt)
    => MeasureOp '[ a ] b
    -> abt '[] a -> abt '[] ('HMeasure b)
measure1_ o e1 = syn (MeasureOp_ o :$ e1 :* End)

measure2_
    :: (ABT Term abt)
    => MeasureOp '[ a, b ] c
    -> abt '[] a -> abt '[] b -> abt '[] ('HMeasure c)
measure2_ o e1 e2 = syn (MeasureOp_ o :$ e1 :* e2 :* End)


-- N.B., we don't take advantage of commutativity, for more predictable
-- AST outputs. However, that means we can end up being slow...
--
-- N.B., we also don't try to eliminate the identity elements or
-- do cancellations because (a) it's undecidable in general, and
-- (b) that's prolly better handled as a post-processing simplification
-- step
--
-- TODO: generalize these two from [] to Foldable?

-- | Apply an n-ary operator to a list. This smart constructor will
-- flatten nested calls to the same operator. And if there is exactly
-- one element in the flattened sequence, then it will remove the
-- 'NaryOp_' node from the AST.
--
-- N.B., if the flattened sequence is empty, this smart constructor
-- will return an AST which applies the operator to the empty
-- sequence; which may or may not be unsafe. If the operator has
-- an identity element, then it's fine (operating on the empty
-- sequence evaluates to the identity element). However, if the
-- operator doesn't have an identity, then the generated code will
-- error whenever we attempt to run it.
unsafeNaryOp_ :: (ABT Term abt) => NaryOp a -> [abt '[] a] -> abt '[] a
unsafeNaryOp_ o = naryOp_withIdentity o (syn $ NaryOp_ o Seq.empty)


-- | A variant of 'unsafeNaryOp_' which will replace operating over
-- the empty sequence with a specified identity element. The produced
-- AST has the same semantics, we're just preemptively
-- evaluating\/simplifying the 'NaryOp_' node of the AST.
--
-- N.B., this function does not simplify away the identity element
-- if it exists in the flattened sequence! We should add that in
-- the future.
naryOp_withIdentity
    :: (ABT Term abt) => NaryOp a -> abt '[] a -> [abt '[] a] -> abt '[] a
naryOp_withIdentity o i = go Seq.empty
    where
    go es [] =
        case Seq.viewl es of
        Seq.EmptyL   -> i
        e Seq.:< es' ->
            case Seq.viewl es' of
            Seq.EmptyL -> e
            _          -> syn $ NaryOp_ o es
    go es (e:es') =
        case matchNaryOp o e of
        Nothing   -> go (es Seq.|> e)    es'
        Just es'' -> go (es Seq.>< es'') es'


-- TODO: is this actually worth breaking out, performance-wise? Or should we simply use:
-- > naryOp2_ o x y = unsafeNaryOp_ o [x,y]
naryOp2_
    :: (ABT Term abt) => NaryOp a -> abt '[] a -> abt '[] a -> abt '[] a
naryOp2_ o x y =
    case (matchNaryOp o x, matchNaryOp o y) of
    (Just xs, Just ys) -> syn . NaryOp_ o $ xs Seq.>< ys
    (Just xs, Nothing) -> syn . NaryOp_ o $ xs Seq.|> y
    (Nothing, Just ys) -> syn . NaryOp_ o $ x  Seq.<| ys
    (Nothing, Nothing) -> syn . NaryOp_ o $ x  Seq.<| Seq.singleton y


matchNaryOp
    :: (ABT Term abt) => NaryOp a -> abt '[] a -> Maybe (Seq (abt '[] a))
matchNaryOp o e =
    caseVarSyn e
        (const Nothing)
        $ \t ->
            case t of
            NaryOp_ o' xs | o' Prelude.== o -> Just xs
            _ -> Nothing


----------------------------------------------------------------
----------------------------------------------------------------
----- Now for the actual EDSL

{-
infixr 9 `pair`

infixr 1 =<<
infixr 1 <=<, >=>
infixr 9 .
infixr 0 $
-}

infixl 1 >>=, >>
infixr 2 ||
infixr 3 &&
infix  4 ==, /=, <, <=, >, >=
infixl 4 <$>, <*>, <*, *> -- <$
infixl 6 +, -
infixl 7 *, /
infixr 8 ^, ^^, **
-- infixl9 is the default when things are unspecified
infixl 9 !, `app`, `thRootOf`

-- TODO: some infix notation reminiscent of \"::\"
-- TODO: actually do something with the type argument?
ann_ :: (ABT Term abt) => Sing a -> abt '[] a -> abt '[] a
ann_ _ e = e

coerceTo_ :: (ABT Term abt) => Coercion a b -> abt '[] a -> abt '[] b
coerceTo_ CNil e = e
coerceTo_ c    e = syn (CoerceTo_ c :$ e :* End)

unsafeFrom_ :: (ABT Term abt) => Coercion a b -> abt '[] b -> abt '[] a
unsafeFrom_ CNil e = e
unsafeFrom_ c    e = syn (UnsafeFrom_ c :$ e :* End)

literal_ :: (ABT Term abt) => Literal a  -> abt '[] a
literal_ = syn . Literal_
bool_    :: (ABT Term abt) => Bool     -> abt '[] HBool
bool_    = datum_ . (\b -> if b then dTrue else dFalse)
nat_     :: (ABT Term abt) => Natural  -> abt '[] 'HNat
nat_     = literal_ . LNat
int_     :: (ABT Term abt) => Integer  -> abt '[] 'HInt
int_     = literal_ . LInt
prob_    :: (ABT Term abt) => NonNegativeRational -> abt '[] 'HProb
prob_    = literal_ . LProb
real_    :: (ABT Term abt) => Rational -> abt '[] 'HReal
real_    = literal_ . LReal

fromRational
    :: forall abt a
    . (ABT Term abt, HFractional_ a)
    => Rational
    -> abt '[] a
fromRational =
    case (hFractional :: HFractional a) of
    HFractional_Prob -> prob_ . unsafeNonNegativeRational
    HFractional_Real -> real_

half :: forall abt a
     .  (ABT Term abt, HFractional_ a) => abt '[] a
half = fromRational (1 Prelude./ 2)

third :: (ABT Term abt, HFractional_ a) => abt '[] a
third = fromRational (1 Prelude./ 3)


-- Boolean operators
true, false :: (ABT Term abt) => abt '[] HBool
true  = bool_ True
false = bool_ False

-- TODO: simplifications: distribution, constant-propogation
-- TODO: do we really want to distribute /by default/? Clearly we'll want to do that in some optimization\/partial-evaluation pass, but do note that it makes terms larger in general...
not :: (ABT Term abt) => abt '[] HBool -> abt '[] HBool
not e =
    Prelude.maybe (primOp1_ Not e) id
        $ caseVarSyn e
            (const Nothing)
            $ \t ->
                case t of
                PrimOp_ Not :$ es' ->
                    case es' of
                    e' :* End -> Just e'
                    _         -> error "not: the impossible happened"
                NaryOp_ And xs ->
                    Just . syn . NaryOp_ Or  $ Prelude.fmap not xs
                NaryOp_ Or xs ->
                    Just . syn . NaryOp_ And $ Prelude.fmap not xs
                NaryOp_ Xor xs ->
                    Just . syn . NaryOp_ Iff $ Prelude.fmap not xs
                NaryOp_ Iff xs ->
                    Just . syn . NaryOp_ Xor $ Prelude.fmap not xs
                Literal_ _ -> error "not: the impossible happened"
                _ -> Nothing

and, or :: (ABT Term abt) => [abt '[] HBool] -> abt '[] HBool
and = naryOp_withIdentity And true
or  = naryOp_withIdentity Or  false

(&&), (||),
    -- (</=>), (<==>), (==>), (<==), (\\), (//) -- TODO: better names?
    nand, nor
    :: (ABT Term abt) => abt '[] HBool -> abt '[] HBool -> abt '[] HBool
(&&) = naryOp2_ And
(||) = naryOp2_ Or
-- (</=>) = naryOp2_ Xor
-- (<==>) = naryOp2_ Iff
-- (==>)  = primOp2_ Impl
-- (<==)  = flip (==>)
-- (\\)   = primOp2_ Diff
-- (//)   = flip (\\)
nand   = primOp2_ Nand
nor    = primOp2_ Nor


-- HEq & HOrder operators
(==), (/=)
    :: (ABT Term abt, HEq_ a) => abt '[] a -> abt '[] a -> abt '[] HBool
(==) = primOp2_ $ Equal hEq
(/=) = (not .) . (==)

(<), (<=), (>), (>=)
    :: (ABT Term abt, HOrd_ a) => abt '[] a -> abt '[] a -> abt '[] HBool
(<)    = primOp2_ $ Less hOrd
x <= y = not (x > y) -- or: @(x < y) || (x == y)@
(>)    = flip (<)
(>=)   = flip (<=)

min, max :: (ABT Term abt, HOrd_ a) => abt '[] a -> abt '[] a -> abt '[] a
min = naryOp2_ $ Min hOrd
max = naryOp2_ $ Max hOrd

-- TODO: if @a@ is bounded, then we can make these safe...
minimum, maximum :: (ABT Term abt, HOrd_ a) => [abt '[] a] -> abt '[] a
minimum = unsafeNaryOp_ $ Min hOrd
maximum = unsafeNaryOp_ $ Max hOrd


-- HSemiring operators
(+), (*)
    :: (ABT Term abt, HSemiring_ a) => abt '[] a -> abt '[] a -> abt '[] a
(+) = naryOp2_ $ Sum  hSemiring
(*) = naryOp2_ $ Prod hSemiring

zero, one :: forall abt a. (ABT Term abt, HSemiring_ a) => abt '[] a
zero = zero_ (hSemiring :: HSemiring a)
one  = one_  (hSemiring :: HSemiring a)

zero_, one_ :: (ABT Term abt) => HSemiring a -> abt '[] a
zero_ HSemiring_Nat  = literal_ $ LNat  0
zero_ HSemiring_Int  = literal_ $ LInt  0
zero_ HSemiring_Prob = literal_ $ LProb 0
zero_ HSemiring_Real = literal_ $ LReal 0
one_  HSemiring_Nat  = literal_ $ LNat  1
one_  HSemiring_Int  = literal_ $ LInt  1
one_  HSemiring_Prob = literal_ $ LProb 1
one_  HSemiring_Real = literal_ $ LReal 1

-- TODO: add a smart constructor for @HSemiring_ a => Natural -> abt '[] a@ and\/or @HRing_ a => Integer -> abt '[] a@

sum, prod :: (ABT Term abt, HSemiring_ a) => [abt '[] a] -> abt '[] a
sum  = naryOp_withIdentity (Sum  hSemiring) zero
prod = naryOp_withIdentity (Prod hSemiring) one

{-
sum, product :: (ABT Term abt, HSemiring_ a) => [abt '[] a] -> abt '[] a
sum     = unsafeNaryOp_ $ Sum  hSemiring
product = unsafeNaryOp_ $ Prod hSemiring
-}


-- TODO: simplifications
(^) :: (ABT Term abt, HSemiring_ a)
    => abt '[] a -> abt '[] 'HNat -> abt '[] a
(^) = primOp2_ $ NatPow hSemiring

-- TODO: this is actually safe, how can we capture that?
-- TODO: is this type restruction actually helpful anywhere for us?
-- If so, we ought to make this function polymorphic so that we can
-- use it for non-HRing HSemirings too...
square :: (ABT Term abt, HRing_ a) => abt '[] a -> abt '[] (NonNegative a)
square e = unsafeFrom_ signed (e ^ nat_ 2)


-- HRing operators
(-) :: (ABT Term abt, HRing_ a) => abt '[] a -> abt '[] a -> abt '[] a
x - y = x + negate y


-- TODO: do we really want to distribute negation over addition /by
-- default/? Clearly we'll want to do that in some
-- optimization\/partial-evaluation pass, but do note that it makes
-- terms larger in general...
negate :: (ABT Term abt, HRing_ a) => abt '[] a -> abt '[] a
negate e =
    Prelude.maybe (primOp1_ (Negate hRing) e) id
        $ caseVarSyn e
            (const Nothing)
            $ \t ->
                case t of
                -- TODO: need we case analyze the @HSemiring@?
                NaryOp_ (Sum theSemi) xs ->
                    Just . syn . NaryOp_ (Sum theSemi) $ Prelude.fmap negate xs
                -- TODO: need we case analyze the @HRing@?
                PrimOp_ (Negate _theRing) :$ es' ->
                    case es' of
                    e' :* End -> Just e'
                    _         -> error "negate: the impossible happened"
                _ -> Nothing


-- TODO: test case: @negative . square@ simplifies away the intermediate coercions. (cf., normal')
-- BUG: this can lead to ambiguity when used with the polymorphic functions of RealProb.
-- | An occasionally helpful variant of 'negate'.
negative :: (ABT Term abt, HRing_ a) => abt '[] (NonNegative a) -> abt '[] a
negative = negate . coerceTo_ signed


abs :: (ABT Term abt, HRing_ a) => abt '[] a -> abt '[] a
abs = coerceTo_ signed . abs_

abs_ :: (ABT Term abt, HRing_ a) => abt '[] a -> abt '[] (NonNegative a)
abs_ e = 
    Prelude.maybe (primOp1_ (Abs hRing) e) id
        $ caseVarSyn e
            (const Nothing)
            $ \t ->
                case t of
                -- BUG: can't use the 'Signed' pattern synonym here, because that /requires/ the input to be (NonNegative a), instead of giving us the information that it is.
                -- TODO: need we case analyze the @HRing@?
                CoerceTo_ (CCons (Signed _theRing) CNil) :$ es' ->
                    case es' of
                    e' :* End -> Just e'
                    _         -> error "abs_: the impossible happened"
                _ -> Nothing


-- TODO: any obvious simplifications? idempotent?
signum :: (ABT Term abt, HRing_ a) => abt '[] a -> abt '[] a
signum = primOp1_ $ Signum hRing


-- HFractional operators
(/) :: (ABT Term abt, HFractional_ a) => abt '[] a -> abt '[] a -> abt '[] a
x / y = x * recip y


-- TODO: generalize this pattern so we don't have to repeat it...
--
-- TODO: do we really want to distribute reciprocal over multiplication
-- /by default/? Clearly we'll want to do that in some
-- optimization\/partial-evaluation pass, but do note that it makes
-- terms larger in general...
recip :: (ABT Term abt, HFractional_ a) => abt '[] a -> abt '[] a
recip e0 =
    Prelude.maybe (primOp1_ (Recip hFractional) e0) id
        $ caseVarSyn e0
            (const Nothing)
            $ \t0 ->
                case t0 of
                -- TODO: need we case analyze the @HSemiring@?
                NaryOp_ (Prod theSemi) xs ->
                    Just . syn . NaryOp_ (Prod theSemi) $ Prelude.fmap recip xs
                -- TODO: need we case analyze the @HFractional@?
                PrimOp_ (Recip _theFrac) :$ es' ->
                    case es' of
                    e :* End -> Just e
                    _ -> error "recip: the impossible happened"
                _ -> Nothing


-- TODO: simplifications
-- TODO: a variant of 'if_' which gives us the evidence that the argument is non-negative, so we don't need to coerce or use 'abs_'
(^^) :: (ABT Term abt, HFractional_ a)
    => abt '[] a -> abt '[] 'HInt -> abt '[] a
x ^^ y =
    if_ (y < int_ 0)
        (recip x ^ abs_ y)
        (x ^ abs_ y)


-- HRadical operators
-- N.B., HProb is the only HRadical type (for now...)
-- TODO: simplifications
thRootOf
    :: (ABT Term abt, HRadical_ a)
    => abt '[] 'HNat -> abt '[] a -> abt '[] a
n `thRootOf` x = primOp2_ (NatRoot hRadical) x n

sqrt :: (ABT Term abt, HRadical_ a) => abt '[] a -> abt '[] a
sqrt = (nat_ 2 `thRootOf`)

{-
-- TODO: simplifications
(^+) :: (ABT Term abt, HRadical_ a)
    => abt '[] a -> abt '[] 'HPositiveRational -> abt '[] a
x ^+ y = casePositiveRational y $ \n d -> d `thRootOf` (x ^ n)

(^*) :: (ABT Term abt, HRadical_ a)
    => abt '[] a -> abt '[] 'HRational -> abt '[] a
x ^* y = caseRational y $ \n d -> d `thRootOf` (x ^^ n)
-}

betaFunc
    :: (ABT Term abt) => abt '[] 'HProb -> abt '[] 'HProb -> abt '[] 'HProb
betaFunc = primOp2_ BetaFunc


integrate
    :: (ABT Term abt)
    => abt '[] 'HReal
    -> abt '[] 'HReal
    -> (abt '[] 'HReal -> abt '[] 'HProb)
    -> abt '[] 'HProb
integrate lo hi f =
    syn (Integrate :$ lo :* hi :* binder Text.empty sing f :* End)

summate
    :: (ABT Term abt, HDiscrete_ a, HSemiring_ b, SingI a)
    => abt '[] a
    -> abt '[] a
    -> (abt '[] a -> abt '[] b)
    -> abt '[] b
summate lo hi f =
    syn (Summate hDiscrete hSemiring
         :$ lo :* hi :* binder Text.empty sing f :* End)

product
    :: (ABT Term abt, HDiscrete_ a, HSemiring_ b, SingI a)
    => abt '[] a
    -> abt '[] a
    -> (abt '[] a -> abt '[] b)
    -> abt '[] b
product lo hi f =
    syn (Product hDiscrete hSemiring
         :$ lo :* hi :* binder Text.empty sing f :* End)


class Integrable (a :: Hakaru) where
    infinity :: (ABT Term abt) => abt '[] a

instance Integrable 'HNat where
    infinity = primOp0_ (Infinity HIntegrable_Nat)

instance Integrable 'HInt where
    infinity = nat2int $ primOp0_ (Infinity HIntegrable_Nat)

instance Integrable 'HProb where
    infinity = primOp0_ (Infinity HIntegrable_Prob)

instance Integrable 'HReal where
    infinity = fromProb $ primOp0_ (Infinity HIntegrable_Prob)

-- HACK: we define this class in order to gain more polymorphism;
-- but, will it cause type inferencing issues? Excepting 'log'
-- (which should be moved out of the class) these are all safe.
class RealProb (a :: Hakaru) where
    (**) :: (ABT Term abt) => abt '[] 'HProb -> abt '[] a -> abt '[] 'HProb
    exp  :: (ABT Term abt) => abt '[] a -> abt '[] 'HProb
    erf  :: (ABT Term abt) => abt '[] a -> abt '[] a
    pi   :: (ABT Term abt) => abt '[] a
    gammaFunc :: (ABT Term abt) => abt '[] a -> abt '[] 'HProb

instance RealProb 'HReal where
    (**)      = primOp2_ RealPow
    exp       = primOp1_ Exp
    erf       = primOp1_ $ Erf hContinuous
    pi        = fromProb $ primOp0_ Pi
    gammaFunc = primOp1_ GammaFunc

instance RealProb 'HProb where
    x ** y    = primOp2_ RealPow x $ fromProb y
    exp       = primOp1_ Exp . fromProb
    erf       = primOp1_ $ Erf hContinuous
    pi        = primOp0_ Pi
    gammaFunc = primOp1_ GammaFunc . fromProb

log  :: (ABT Term abt) => abt '[] 'HProb -> abt '[] 'HReal
log = primOp1_ Log

logBase
    :: (ABT Term abt)
    => abt '[] 'HProb
    -> abt '[] 'HProb
    -> abt '[] 'HReal
logBase b x = log x / log b -- undefined when b == 1

sin, cos, tan, asin, acos, atan, sinh, cosh, tanh, asinh, acosh, atanh
    :: (ABT Term abt) => abt '[] 'HReal -> abt '[] 'HReal
sin    = primOp1_ Sin
cos    = primOp1_ Cos
tan    = primOp1_ Tan
asin   = primOp1_ Asin
acos   = primOp1_ Acos
atan   = primOp1_ Atan
sinh   = primOp1_ Sinh
cosh   = primOp1_ Cosh
tanh   = primOp1_ Tanh
asinh  = primOp1_ Asinh
acosh  = primOp1_ Acosh
atanh  = primOp1_ Atanh

choose
    :: (ABT Term abt) => abt '[] 'HNat -> abt '[] 'HNat -> abt '[] 'HNat
choose = primOp2_ Choose

floor :: (ABT Term abt) => abt '[] 'HProb -> abt '[] 'HNat
floor  = primOp1_ Floor

----------------------------------------------------------------
datum_
    :: (ABT Term abt)
    => Datum (abt '[]) (HData' t)
    -> abt '[] (HData' t)
datum_ = syn . Datum_

case_
     :: (ABT Term abt)
     => abt '[] a
     -> [Branch a abt b]
     -> abt '[] b
case_ e bs = syn (Case_ e bs)

branch
    :: (ABT Term abt)
    => Pattern xs a
    -> abt xs b
    -> Branch a abt b
branch = Branch

unit :: (ABT Term abt) => abt '[] HUnit
unit = datum_ dUnit

pair
    :: (ABT Term abt, SingI a, SingI b)
    => abt '[] a -> abt '[] b -> abt '[] (HPair a b)
pair = (datum_ .) . dPair


pair_
    :: (ABT Term abt)
    => Sing a
    -> Sing b
    -> abt '[] a
    -> abt '[] b
    -> abt '[] (HPair a b)
pair_ a b = (datum_ .) . dPair_ a b


unpair
    :: forall abt a b c
    .  (ABT Term abt)
    => abt '[] (HPair a b)
    -> (abt '[] a -> abt '[] b -> abt '[] c)
    -> abt '[] c
unpair e hoas =
    let (aTyp,bTyp) = sUnPair $ typeOf e
        body        = hoas (var a) (var b)
        inc x       = 1 Prelude.+ x
        a           = Variable Text.empty (nextBind body)         aTyp
        b           = Variable Text.empty (inc . nextBind $ body) bTyp
    in case_ e
        [Branch (pPair PVar PVar)
           (bind a (bind b body))
        ]

fst :: (ABT Term abt)
    => abt '[] (HPair a b)
    -> abt '[] a
fst p = unpair p (\x _ -> x)

snd :: (ABT Term abt)
    => abt '[] (HPair a b)
    -> abt '[] b
snd p = unpair p (\_ y -> y)

swap :: (ABT Term abt, SingI a, SingI b)
    => abt '[] (HPair a b)
    -> abt '[] (HPair b a)
swap ab = unpair ab (flip pair)

left
    :: (ABT Term abt, SingI a, SingI b)
    => abt '[] a -> abt '[] (HEither a b)
left = datum_ . dLeft

right
    :: (ABT Term abt, SingI a, SingI b)
    => abt '[] b -> abt '[] (HEither a b)
right = datum_ . dRight

uneither
    :: (ABT Term abt)
    => abt '[] (HEither a b)
    -> (abt '[] a -> abt '[] c)
    -> (abt '[] b -> abt '[] c)
    -> abt '[] c
uneither e l r =
    let (a,b) = sUnEither $ typeOf e
    in case_ e
        [ Branch (pLeft  PVar) (binder Text.empty a l)
        , Branch (pRight PVar) (binder Text.empty b r)
        ]

if_ :: (ABT Term abt)
    => abt '[] HBool
    -> abt '[] a
    -> abt '[] a
    -> abt '[] a
if_ b t f =
    case_ b
     [ Branch pTrue  t
     , Branch pFalse f
     ]

nil :: (ABT Term abt, SingI a) => abt '[] (HList a)
nil = datum_ dNil

cons
    :: (ABT Term abt, SingI a)
    => abt '[] a -> abt '[] (HList a) -> abt '[] (HList a)
cons = (datum_ .) . dCons

list :: (ABT Term abt, SingI a) => [abt '[] a] -> abt '[] (HList a)
list = Prelude.foldr cons nil

nothing :: (ABT Term abt, SingI a) => abt '[] (HMaybe a)
nothing = datum_ dNothing

just :: (ABT Term abt, SingI a) => abt '[] a -> abt '[] (HMaybe a)
just = datum_ . dJust

maybe :: (ABT Term abt, SingI a) => Maybe (abt '[] a) -> abt '[] (HMaybe a)
maybe = Prelude.maybe nothing just

unmaybe
    :: (ABT Term abt)
    => abt '[] (HMaybe a)
    -> abt '[] b
    -> (abt '[] a -> abt '[] b)
    -> abt '[] b
unmaybe e n j = 
    case_ e
     [ Branch pNothing     n
     , Branch (pJust PVar) (binder Text.empty (sUnMaybe $ typeOf e) j)
     ]

unsafeProb :: (ABT Term abt) => abt '[] 'HReal -> abt '[] 'HProb
unsafeProb = unsafeFrom_ signed

fromProb   :: (ABT Term abt) => abt '[] 'HProb -> abt '[] 'HReal
fromProb   = coerceTo_ signed

nat2int    :: (ABT Term abt) => abt '[] 'HNat -> abt '[] 'HInt
nat2int    = coerceTo_ signed

fromInt    :: (ABT Term abt) => abt '[] 'HInt  -> abt '[] 'HReal
fromInt    = coerceTo_ continuous

nat2prob   :: (ABT Term abt) => abt '[] 'HNat  -> abt '[] 'HProb
nat2prob   = coerceTo_ continuous

nat2real   :: (ABT Term abt) => abt '[] 'HNat  -> abt '[] 'HReal
nat2real   = coerceTo_ (continuous . signed)

{- -- Uncomment only if we actually end up needing this anywhere
class FromNat (a :: Hakaru) where
    fromNat :: (ABT Term abt) => abt '[] 'HNat  -> abt '[] a

instance FromNat 'HNat  where fromNat = id
instance FromNat 'HInt  where fromNat = nat2int
instance FromNat 'HProb where fromNat = nat2prob
instance FromNat 'HReal where fromNat = fromProb . nat2prob
-}

unsafeProbFraction
    :: forall abt a
    .  (ABT Term abt, HFractional_ a)
    => abt '[] a
    -> abt '[] 'HProb
unsafeProbFraction e =
    unsafeProbFraction_ (hFractional :: HFractional a) e

unsafeProbFraction_
    :: (ABT Term abt)
    => HFractional a
    -> abt '[] a
    -> abt '[] 'HProb
unsafeProbFraction_ HFractional_Prob = id
unsafeProbFraction_ HFractional_Real = unsafeProb

unsafeProbSemiring
    :: forall abt a
    .  (ABT Term abt, HSemiring_ a)
    => abt '[] a
    -> abt '[] 'HProb
unsafeProbSemiring e =
    unsafeProbSemiring_ (hSemiring :: HSemiring a) e

unsafeProbSemiring_
    :: (ABT Term abt)
    => HSemiring a
    -> abt '[] a
    -> abt '[] 'HProb
unsafeProbSemiring_ HSemiring_Nat  = nat2prob
unsafeProbSemiring_ HSemiring_Int  = coerceTo_ continuous . unsafeFrom_ signed
unsafeProbSemiring_ HSemiring_Prob = id
unsafeProbSemiring_ HSemiring_Real = unsafeProb


negativeInfinity :: ( ABT Term abt
                    , HRing_ a
                    , Integrable a)
                 => abt '[] a
negativeInfinity = negate infinity

-- instance (ABT Term abt) => Lambda abt where
-- 'app' already defined

-- TODO: use 'typeOf' to remove the 'SingI' requirement somehow
-- | A variant of 'lamWithVar' for automatically computing the type
-- via 'sing'.
lam :: (ABT Term abt, SingI a)
    => (abt '[] a -> abt '[] b)
    -> abt '[] (a ':-> b)
lam = lamWithVar Text.empty sing

-- | Create a lambda abstraction. The first two arguments give the
-- hint and type of the lambda-bound variable in the result. If you
-- want to automatically fill those in, then see 'lam'.
lamWithVar
    :: (ABT Term abt)
    => Text.Text
    -> Sing a
    -> (abt '[] a -> abt '[] b)
    -> abt '[] (a ':-> b)
lamWithVar hint typ f = syn (Lam_ :$ binder hint typ f :* End)

{-
-- some test cases to make sure we tied-the-knot successfully:
> let
    lam :: (ABT Term abt)
        => String
        -> Sing a
        -> (abt '[] a -> abt '[] b)
        -> abt '[] (a ':-> b)
    lam name typ f = syn (Lam_ :$ binder name typ f :* End)
> lam "x" SInt (\x -> x) :: TrivialABT Term ('HInt ':-> 'HInt)
> lam "x" SInt (\x -> lam "y" SInt $ \y -> x < y) :: TrivialABT Term ('HInt ':-> 'HInt ':-> 'HBool)
-}

-- TODO: make this smarter so that if the @e@ is already a variable then we just plug it into @f@ instead of introducing the trivial let-binding.
let_
    :: (ABT Term abt)
    => abt '[] a
    -> (abt '[] a -> abt '[] b)
    -> abt '[] b
let_ e f = syn (Let_ :$ e :* binder Text.empty (typeOf e) f :* End)

letM :: (Functor m, MonadFix m, ABT Term abt)
     => abt '[] a
     -> (abt '[] a -> m (abt '[] b))
     -> m (abt '[] b)
letM e f = fmap (\ body -> syn $ Let_ :$ e :* body :* End) (binderM Text.empty t f)
  where t = typeOf e

----------------------------------------------------------------
array
    :: (ABT Term abt)
    => abt '[] 'HNat
    -> (abt '[] 'HNat -> abt '[] a)
    -> abt '[] ('HArray a)
array n =
    syn . Array_ n . binder Text.empty sing        

arrayWithVar
    :: (ABT Term abt)
    => abt '[] 'HNat
    -> Variable 'HNat
    -> abt '[] a
    -> abt '[] ('HArray a)
arrayWithVar n x body =
    syn $ Array_ n (bind x body)

arrayLit
    :: (ABT Term abt)
    => [abt '[] a]
    -> abt '[] ('HArray a)
arrayLit = syn . ArrayLiteral_

empty :: (ABT Term abt, SingI a) => abt '[] ('HArray a)
empty = syn (Empty_ sing)

(!) :: (ABT Term abt)
    => abt '[] ('HArray a) -> abt '[] 'HNat -> abt '[] a
(!) e = arrayOp2_ (Index . sUnArray $ typeOf e) e

size :: (ABT Term abt) => abt '[] ('HArray a) -> abt '[] 'HNat
size e = arrayOp1_ (Size . sUnArray $ typeOf e) e

reduce
    :: (ABT Term abt)
    => (abt '[] a -> abt '[] a -> abt '[] a)
    -> abt '[] a
    -> abt '[] ('HArray a)
    -> abt '[] a
reduce f e =
    let a  = typeOf e
        f' = lamWithVar Text.empty a $ \x ->
                lamWithVar Text.empty a $ \y -> f x y
    in arrayOp3_ (Reduce a) f' e

-- TODO: better names for all these. The \"V\" suffix doesn't make sense anymore since we're calling these arrays, not vectors...
-- TODO: bust these all out into their own place, since the API for arrays is gonna be huge

sumV :: (ABT Term abt, HSemiring_ a)
    => abt '[] ('HArray a) -> abt '[] a
sumV = reduce (+) zero -- equivalent to summateV if @a ~ 'HProb@

summateV :: (ABT Term abt) => abt '[] ('HArray 'HProb) -> abt '[] 'HProb
summateV x =
    summate (nat_ 0) (size x)
        (\i -> x ! i)

-- TODO: a variant of 'if_' for giving us evidence that the subtraction is sound.

unsafeMinusNat
    :: (ABT Term abt) => abt '[] 'HNat -> abt '[] 'HNat -> abt '[] 'HNat
unsafeMinusNat x y = unsafeFrom_ signed (nat2int x - nat2int y)

unsafeMinusProb
    :: (ABT Term abt) => abt '[] 'HProb -> abt '[] 'HProb -> abt '[] 'HProb
unsafeMinusProb x y = unsafeProb (fromProb x - fromProb y)

-- | For any semiring we can attempt subtraction by lifting to a
-- ring, subtracting there, and then lowering back to the semiring.
-- Of course, the lowering step may well fail.
unsafeMinus
    :: (ABT Term abt, HSemiring_ a) => abt '[] a -> abt '[] a -> abt '[] a
unsafeMinus = unsafeMinus_ hSemiring

-- | A variant of 'unsafeMinus' for explicitly passing the semiring
-- instance.
unsafeMinus_
    :: (ABT Term abt) => HSemiring a -> abt '[] a -> abt '[] a -> abt '[] a
unsafeMinus_ theSemi =
    signed_HSemiring theSemi $ \c ->
        let lift  = coerceTo_   c
            lower = unsafeFrom_ c
        in \e1 e2 -> lower (lift e1 - lift e2)

-- TODO: move to Coercion.hs?
-- | For any semiring, return a coercion to its ring completion.
-- Because this completion is existentially quantified, we must use
-- a cps trick to eliminate the existential.
signed_HSemiring
    :: HSemiring a -> (forall b. (HRing_ b) => Coercion a b -> r) -> r
signed_HSemiring c k =
    case c of
    HSemiring_Nat  -> k $ singletonCoercion (Signed HRing_Int)
    HSemiring_Int  -> k CNil
    HSemiring_Prob -> k $ singletonCoercion (Signed HRing_Real)
    HSemiring_Real -> k CNil

-- | For any semiring we can attempt division by lifting to a
-- semifield, dividing there, and then lowering back to the semiring.
-- Of course, the lowering step may well fail.
unsafeDiv
    :: (ABT Term abt, HSemiring_ a) => abt '[] a -> abt '[] a -> abt '[] a
unsafeDiv = unsafeDiv_ hSemiring

-- | A variant of 'unsafeDiv' for explicitly passing the semiring
-- instance.
unsafeDiv_
    :: (ABT Term abt) => HSemiring a -> abt '[] a -> abt '[] a -> abt '[] a
unsafeDiv_ theSemi =
    continuous_HSemiring theSemi $ \c ->
        let lift  = coerceTo_   c
            lower = unsafeFrom_ c
        in \e1 e2 -> lower (lift e1 / lift e2)

-- TODO: move to Coercion.hs?
-- | For any semiring, return a coercion to its semifield completion.
-- Because this completion is existentially quantified, we must use
-- a cps trick to eliminate the existential.
continuous_HSemiring
    :: HSemiring a -> (forall b. (HFractional_ b) => Coercion a b -> r) -> r
continuous_HSemiring c k =
    case c of
    HSemiring_Nat  -> k $ singletonCoercion (Continuous HContinuous_Prob)
    HSemiring_Int  -> k $ singletonCoercion (Continuous HContinuous_Real)
    HSemiring_Prob -> k CNil
    HSemiring_Real -> k CNil


appendV
    :: (ABT Term abt)
    => abt '[] ('HArray a) -> abt '[] ('HArray a) -> abt '[] ('HArray a)
appendV v1 v2 =
    array (size v1 + size v2) $ \i ->
        if_ (i < size v1)
            (v1 ! i)
            (v2 ! (i `unsafeMinusNat` size v1))

mapWithIndex
    :: (ABT Term abt)
    => (abt '[] 'HNat -> abt '[] a -> abt '[] b)
    -> abt '[] ('HArray a)
    -> abt '[] ('HArray b)
mapWithIndex f v = array (size v) $ \i -> f i (v ! i)

mapV
    :: (ABT Term abt)
    => (abt '[] a -> abt '[] b)
    -> abt '[] ('HArray a)
    -> abt '[] ('HArray b)
mapV f v = array (size v) $ \i -> f (v ! i)

normalizeV
    :: (ABT Term abt)
    => abt '[] ('HArray 'HProb)
    -> abt '[] ('HArray 'HProb)
normalizeV x = mapV (/ sumV x) x

constV
    :: (ABT Term abt) => abt '[] 'HNat -> abt '[] b -> abt '[] ('HArray b)
constV n c = array n (const c)

unitV
    :: (ABT Term abt)
    => abt '[] 'HNat
    -> abt '[] 'HNat
    -> abt '[] ('HArray 'HProb)
unitV s i = array s (\j -> if_ (i == j) (prob_ 1) (prob_ 0))

zipWithV
    :: (ABT Term abt)
    => (abt '[] a -> abt '[] b -> abt '[] c)
    -> abt '[] ('HArray a)
    -> abt '[] ('HArray b)
    -> abt '[] ('HArray c)
zipWithV f v1 v2 =
    array (size v1) (\i -> f (v1 ! i) (v2 ! i))

----------------------------------------------------------------

r_fanout
    :: (ABT Term abt)
    => Reducer abt xs a
    -> Reducer abt xs b
    -> Reducer abt xs (HPair a b)
r_fanout = Red_Fanout

r_index
    :: (Binders Term abt xs as)
    => (as -> abt '[] 'HNat)
    -> ((abt '[] 'HNat, as) -> abt '[] 'HNat)
    -> Reducer abt ( 'HNat ': xs) a
    -> Reducer abt xs ('HArray a)
r_index n f = Red_Index (binders n) (binders f)

r_split
    :: (Binders Term abt xs as)
    => ((abt '[] 'HNat, as) -> abt '[] HBool)
    -> Reducer abt xs a
    -> Reducer abt xs b
    -> Reducer abt xs (HPair a b)
r_split b = Red_Split (binders b)

r_nop :: (ABT Term abt) => Reducer abt xs HUnit
r_nop = Red_Nop

r_add
    :: (Binders Term abt xs as, HSemiring_ a)
    => ((abt '[] 'HNat, as) -> abt '[] a)
    -> Reducer abt xs a
r_add f = Red_Add hSemiring (binders f)

bucket
    :: (ABT Term abt)
    => abt '[] 'HNat
    -> abt '[] 'HNat
    -> Reducer abt '[] a
    -> abt '[] a
bucket i j r = syn $ Bucket i j r

----------------------------------------------------------------
(>>=)
    :: (ABT Term abt)
    => abt '[] ('HMeasure a)
    -> (abt '[] a -> abt '[] ('HMeasure b))
    -> abt '[] ('HMeasure b)
m >>= f =
    syn (MBind :$ m
               :* binder Text.empty (sUnMeasure $ typeOf m) f
               :* End)


dirac :: (ABT Term abt) => abt '[] a -> abt '[] ('HMeasure a)
dirac e1 = syn (Dirac :$ e1 :* End)


-- TODO: can we use let-binding instead of (>>=)-binding (i.e., for when the dirac is immediately (>>=)-bound again...)?
(<$>)
    :: (ABT Term abt, SingI a)
    => (abt '[] a -> abt '[] b)
    -> abt '[] ('HMeasure a)
    -> abt '[] ('HMeasure b)
f <$> m = m >>= dirac . f

-- | N.B, this function may introduce administrative redexes.
-- Moreover, it's not clear that we should even allow the type
-- @'HMeasure (a ':-> b)@!
(<*>)
    :: (ABT Term abt, SingI a, SingI b)
    => abt '[] ('HMeasure (a ':-> b))
    -> abt '[] ('HMeasure a)
    -> abt '[] ('HMeasure b)
mf <*> mx = mf >>= \f -> app f <$> mx

-- TODO: ensure that @dirac a *> n@ simplifies to just @n@, regardless of @a@ but especially when @a = unit@.
(*>), (>>)
    :: (ABT Term abt, SingI a)
    => abt '[] ('HMeasure a)
    -> abt '[] ('HMeasure b)
    -> abt '[] ('HMeasure b)
m *> n = m >>= \_ -> n
(>>) = (*>)

-- TODO: ensure that @m <* dirac a@ simplifies to just @m@, regardless of @a@ but especially when @a = unit@.
(<*)
    :: (ABT Term abt, SingI a, SingI b)
    => abt '[] ('HMeasure a)
    -> abt '[] ('HMeasure b)
    -> abt '[] ('HMeasure a)
m <* n = m >>= \a -> n *> dirac a

bindx
    :: (ABT Term abt, SingI a, SingI b)
    => abt '[] ('HMeasure a)
    -> (abt '[] a -> abt '[] ('HMeasure b))
    -> abt '[] ('HMeasure (HPair a b))
m `bindx` f = m >>= \a -> pair a <$> f a

-- Defined because using @(<$>)@ and @(<*>)@ would introduce administrative redexes
liftM2
    :: (ABT Term abt, SingI a, SingI b)
    => (abt '[] a -> abt '[] b -> abt '[] c)
    -> abt '[] ('HMeasure a)
    -> abt '[] ('HMeasure b)
    -> abt '[] ('HMeasure c)
liftM2 f m n = m >>= \x -> f x <$> n

lebesgue' :: (ABT Term abt) => abt '[] 'HReal -> abt '[] 'HReal -> abt '[] ('HMeasure 'HReal)
lebesgue' = measure2_ Lebesgue 

lebesgue :: (ABT Term abt) => abt '[] ('HMeasure 'HReal)
lebesgue = lebesgue' negativeInfinity infinity 

counting :: (ABT Term abt) => abt '[] ('HMeasure 'HInt)
counting = measure0_ Counting

-- TODO: make this smarter by collapsing nested @Superpose_@ similar to how we collapse nested NaryOps. Though beware, that could cause duplication of the computation for the probabilities\/weights; thus may want to only do it when the weights are constant values, or \"simplify\" things by generating let-bindings in order to share work.
--
-- TODO: can we make this smarter enough to handle empty lists?
superpose
    :: (ABT Term abt)
    => NonEmpty (abt '[] 'HProb, abt '[] ('HMeasure a))
    -> abt '[] ('HMeasure a)
superpose = syn . Superpose_

-- | The empty measure. Is called @fail@ in the Core Hakaru paper.
reject
    :: (ABT Term abt)
    => (Sing ('HMeasure a))
    -> abt '[] ('HMeasure a)
reject = syn . Reject_

-- | The sum of two measures. Is called @mplus@ in the Core Hakaru paper.
(<|>) :: (ABT Term abt)
      => abt '[] ('HMeasure a)
      -> abt '[] ('HMeasure a)
      -> abt '[] ('HMeasure a)
x <|> y =
    superpose $
        case (matchSuperpose x, matchSuperpose y) of
        (Just xs, Just ys) -> xs <> ys
        (Just xs, Nothing) -> (one, y) :| L.toList xs -- HACK: reordering!
        (Nothing, Just ys) -> (one, x) :| L.toList ys
        (Nothing, Nothing) -> (one, x) :| [(one, y)]

matchSuperpose
    :: (ABT Term abt) 
    => abt '[] ('HMeasure a)
    -> Maybe (NonEmpty (abt '[] 'HProb, abt '[] ('HMeasure a)))
matchSuperpose e =
    caseVarSyn e
        (const Nothing)
        $ \t ->
            case t of
            Superpose_ xs -> Just xs
            _ -> Nothing

-- TODO: we should ensure that the following reductions happen:
-- > (withWeight p m >> n) ---> withWeight p (m >> n)
-- > (m >> withWeight p n) ---> withWeight p (m >> n)
-- > withWeight 1 m ---> m
-- > withWeight p (withWeight q m) ---> withWeight (p*q) m
-- > (weight p >> m) ---> withWeight p m
--
-- | Adjust the weight of the current measure.
--
-- /N.B.,/ the name for this function is terribly inconsistent
-- across the literature, even just the Hakaru literature, let alone
-- the Hakaru code base. It is variously called \"factor\" or
-- \"weight\"; though \"factor\" is also used to mean the function
-- 'factor' or the function 'observe', and \"weight\" is also used
-- to mean the 'weight' function.
weight
    :: (ABT Term abt)
    => abt '[] 'HProb
    -> abt '[] ('HMeasure HUnit)
weight p = withWeight p (dirac unit)


-- | A variant of 'weight' which removes an administrative @(dirac
-- unit >>)@ redex.
--
-- TODO: ideally we'll be able to get rid of this function entirely,
-- and be able to trust optimization to clean up any redexes
-- introduced by 'weight'.
withWeight
    :: (ABT Term abt)
    => abt '[] 'HProb
    -> abt '[] ('HMeasure w)
    -> abt '[] ('HMeasure w)
withWeight p m = syn $ Superpose_ ((p, m) :| [])


-- | A particularly common use case of 'weight':
--
-- > weightedDirac e p
-- >     == weight p (dirac e)
-- >     == weight p *> dirac e
-- >     == dirac e <* weight p
weightedDirac
    :: (ABT Term abt, SingI a)
    => abt '[] a
    -> abt '[] 'HProb
    -> abt '[] ('HMeasure a)
weightedDirac e p = withWeight p (dirac e)


-- TODO: this taking of two arguments is as per the Core Hakaru specification; but for the EDSL, can we rephrase this as just taking the first argument, using @dirac unit@ for the else-branch, and then, making @(>>)@ work in the right way to plug the continuation measure in place of the @dirac unit@.
-- TODO: would it help inference\/simplification at all to move this into the AST as a primitive? I mean, it is a primitive of Core Hakaru afterall... Also, that would help clarify whether the (first)argument should actually be an @HBool@ or whether it should be some sort of proposition.

-- | Assert that a condition is true.
--
-- /N.B.,/ the name for this function is terribly inconsistent
-- across the literature, even just the Hakaru literature, let alone
-- the Hakaru code base. It is variously called \"factor\" or
-- \"observe\"; though \"factor\" is also used to mean the function
-- 'pose', and \"observe\" is also used to mean the backwards part
-- of Lazy.hs.
guard
    :: (ABT Term abt)
    => abt '[] HBool
    -> abt '[] ('HMeasure HUnit)
guard b = withGuard b (dirac unit)


-- | A variant of 'guard' which removes an administrative @(dirac
-- unit >>)@ redex.
--
-- TODO: ideally we'll be able to get rid of this function entirely,
-- and be able to trust optimization to clean up any redexes
-- introduced by 'guard'.
withGuard
    :: (ABT Term abt)
    => abt '[] HBool
    -> abt '[] ('HMeasure a)
    -> abt '[] ('HMeasure a)
withGuard b m = if_ b m (reject (typeOf m))


densityCategorical
    :: (ABT Term abt)
    => abt '[] ('HArray 'HProb)
    -> abt '[] 'HNat
    -> abt '[] 'HProb
densityCategorical v i = v ! i / summateV v

categorical, categorical'
    :: (ABT Term abt)
    => abt '[] ('HArray 'HProb)
    -> abt '[] ('HMeasure 'HNat)
categorical = measure1_ Categorical

-- TODO: a variant of 'if_' which gives us the evidence that the argument is non-negative, so we don't need to coerce or use 'abs_'
categorical' v =
    counting >>= \i ->
    withGuard (int_ 0 <= i && i < nat2int (size v)) $
    let_ (unsafeFrom_ signed i) $ \i_ ->
    weightedDirac i_ (densityCategorical v i_)


densityUniform
    :: (ABT Term abt)
    => abt '[] 'HReal
    -> abt '[] 'HReal
    -> abt '[] 'HReal
    -> abt '[] 'HProb
densityUniform lo hi _ = recip . unsafeProb $ hi - lo


-- TODO: make Uniform polymorphic, so that if the two inputs are
-- HProb then we know the measure must be over HProb too
uniform, uniform'
    :: (ABT Term abt)
    => abt '[] 'HReal
    -> abt '[] 'HReal
    -> abt '[] ('HMeasure 'HReal)
uniform = measure2_ Uniform

uniform' lo hi = 
    lebesgue >>= \x ->
    withGuard (lo < x && x < hi) $
        -- TODO: how can we capture that this 'unsafeProb' is safe? (and that this 'recip' isn't Infinity, for that matter)
    weightedDirac x (densityUniform lo hi x)

densityNormal
    :: (ABT Term abt)
    => abt '[] 'HReal
    -> abt '[] 'HProb
    -> abt '[] 'HReal
    -> abt '[] 'HProb
densityNormal mu sd x = 
    exp (negate ((x - mu) ^ nat_ 2)  -- TODO: use negative\/square instead of negate\/(^2)
         / fromProb (prob_ 2 * sd ^ nat_ 2)) -- TODO: use square?
     / sd / sqrt (prob_ 2 * pi)


normal, normal'
    :: (ABT Term abt)
    => abt '[] 'HReal
    -> abt '[] 'HProb
    -> abt '[] ('HMeasure 'HReal)
normal = measure2_ Normal

normal' mu sd  = 
    lebesgue >>= \x ->
    weightedDirac x (densityNormal mu sd x)


densityPoisson
    :: (ABT Term abt)
    => abt '[] 'HProb
    -> abt '[] 'HNat
    -> abt '[] 'HProb
densityPoisson l x =
     l ^ x
       / gammaFunc (nat2real (x + nat_ 1)) -- TODO: use factorial instead of gammaFunc...
       / exp l


poisson, poisson'
    :: (ABT Term abt) => abt '[] 'HProb -> abt '[] ('HMeasure 'HNat)
poisson = measure1_ Poisson

poisson' l = 
    counting >>= \x ->
    -- TODO: use 'SafeFrom_' instead of @if_ (x >= int_ 0)@ so we can prove that @unsafeFrom_ signed x@ is actually always safe.
    withGuard (int_ 0 <= x && prob_ 0 < l) $ -- N.B., @0 < l@ means simply that @l /= 0@; why phrase it the other way?
    let_ (unsafeFrom_ signed x) $ \x_ ->
        weightedDirac x_ (densityPoisson l x_)

densityGamma
    :: (ABT Term abt)
    => abt '[] 'HProb
    -> abt '[] 'HProb
    -> abt '[] 'HProb
    -> abt '[] 'HProb
densityGamma shape scale x =
    x ** (fromProb shape - real_ 1)
    * exp (negate . fromProb $ x / scale)
    / (scale ** shape * gammaFunc shape)


gamma, gamma'
    :: (ABT Term abt)
    => abt '[] 'HProb
    -> abt '[] 'HProb
    -> abt '[] ('HMeasure 'HProb)
gamma = measure2_ Gamma

gamma' shape scale =
    lebesgue >>= \x ->
    -- TODO: use 'SafeFrom_' instead of @if_ (real_ 0 < x)@ so we can prove that @unsafeProb x@ is actually always safe. Of course, then we'll need to mess around with checking (/=0) which'll get ugly... Use another SafeFrom_ with an associated NonZero type?
    withGuard (real_ 0 < x) $
    let_ (unsafeProb x) $ \ x_ ->
    weightedDirac x_ (densityGamma shape scale x_)

densityBeta
    :: (ABT Term abt)
    => abt '[] 'HProb
    -> abt '[] 'HProb
    -> abt '[] 'HProb
    -> abt '[] 'HProb
densityBeta a b x =
    x ** (fromProb a - real_ 1)
    * unsafeProb (real_ 1 - fromProb x) ** (fromProb b - real_ 1)
    / betaFunc a b

beta, beta', beta''
    :: (ABT Term abt)
    => abt '[] 'HProb
    -> abt '[] 'HProb
    -> abt '[] ('HMeasure 'HProb)
beta = measure2_ Beta

beta' a b =
    -- TODO: make Uniform polymorphic, so that if the two inputs are HProb then we know the measure must be over HProb too, and hence @unsafeProb x@ must always be safe. Alas, capturing the safety of @unsafeProb (1-x)@ would take a lot more work...
    unsafeProb <$> uniform (real_ 0) (real_ 1) >>= \x ->
    weightedDirac x (densityBeta a b x)

beta'' a b =
    gamma a (prob_ 1) >>= \x ->
    gamma b (prob_ 1) >>= \y ->
    dirac (x / (x+y))

plateWithVar
    :: (ABT Term abt)
    => abt '[] 'HNat
    -> Variable 'HNat
    -> abt '[] ('HMeasure a)
    -> abt '[] ('HMeasure ('HArray a))
plateWithVar e1 x e2 = syn (Plate :$ e1 :* bind x e2 :* End)
        
plate :: (ABT Term abt)
      => abt '[] 'HNat
      -> (abt '[] 'HNat -> abt '[] ('HMeasure a))
      -> abt '[] ('HMeasure ('HArray a))
plate e f = syn (Plate :$ e :* binder Text.empty sing f :* End)

plate'
    :: (ABT Term abt, SingI a)
    => abt '[] ('HArray ('HMeasure          a))
    -> abt '[] (         'HMeasure ('HArray a))

plate' v = reduce r z (mapV m v)
    where
    r   = liftM2 appendV
    z   = dirac empty
    m a = (array (nat_ 1) . const) <$> a


-- BUG: remove the 'SingI' requirement!
chain :: (ABT Term abt, SingI s)
      => abt '[] 'HNat
      -> abt '[] s
      -> (abt '[] s -> abt '[] ('HMeasure (HPair a s)))
      -> abt '[] ('HMeasure (HPair ('HArray a) s))
chain n s f = syn (Chain :$ n :* s :* binder Text.empty sing f :* End)

chain'
    :: (ABT Term abt, SingI s, SingI a)
    => abt '[] ('HArray (s ':-> 'HMeasure (HPair a s)))
    -> abt '[] s
    -> abt '[] ('HMeasure (HPair ('HArray a) s))

chain' v s0 = reduce r z (mapV m v) `app` s0
    where
    r x y = lam $ \s ->
            app x s >>= \v1s1 ->
            v1s1 `unpair` \v1 s1 ->
            app y s1 >>= \v2s2 ->
            v2s2 `unpair` \v2 s2 ->
            dirac $ pair (appendV v1 v2) s2
    z     = lam $ \s -> dirac (pair empty s)
    m a   = lam $ \s -> (`unpair` pair . array (nat_ 1) . const) <$> app a s


invgamma
    :: (ABT Term abt)
    => abt '[] 'HProb
    -> abt '[] 'HProb
    -> abt '[] ('HMeasure 'HProb)
invgamma k t = recip <$> gamma k (recip t)

exponential
    :: (ABT Term abt) => abt '[] 'HProb -> abt '[] ('HMeasure 'HProb)
exponential = gamma (prob_ 1)

chi2 :: (ABT Term abt) => abt '[] 'HProb -> abt '[] ('HMeasure 'HProb)
chi2 v = gamma (v / prob_ 2) (prob_ 2)

cauchy
    :: (ABT Term abt)
    => abt '[] 'HReal
    -> abt '[] 'HProb
    -> abt '[] ('HMeasure 'HReal)
cauchy loc scale =
    normal (real_ 0) (prob_ 1) >>= \x ->
    normal (real_ 0) (prob_ 1) >>= \y ->
    dirac $ loc + fromProb scale * x / y

laplace
    :: (ABT Term abt)
    => abt '[] 'HReal
    -> abt '[] 'HProb
    -> abt '[] ('HMeasure 'HReal)
laplace loc scale =
    exponential (prob_ 1) >>= \v ->
    normal (real_ 0) (prob_ 1) >>= \z ->
    dirac $ loc + z * fromProb (scale * sqrt (prob_ 2 * v))

studentT
    :: (ABT Term abt)
    => abt '[] 'HReal
    -> abt '[] 'HProb
    -> abt '[] 'HProb
    -> abt '[] ('HMeasure 'HReal)
studentT loc scale v =
    normal loc scale >>= \z ->
    chi2 v >>= \df ->
    dirac $ z * fromProb (sqrt (v / df))

weibull
    :: (ABT Term abt)
    => abt '[] 'HProb
    -> abt '[] 'HProb
    -> abt '[] ('HMeasure 'HProb)
weibull b k =
    exponential (prob_ 1) >>= \x ->
    dirac $ b * x ** recip k

bern :: (ABT Term abt) => abt '[] 'HProb -> abt '[] ('HMeasure HBool)
bern p = categorical (arrayLit [p, prob_ 1 `unsafeMinusProb` p]) >>= \i ->
         dirac (arrayLit [true, false] ! i)

mix :: (ABT Term abt)
    => abt '[] ('HArray 'HProb) -> abt '[] ('HMeasure 'HNat)
mix v = withWeight (sumV v) (categorical v)

binomial
    :: (ABT Term abt)
    => abt '[] 'HNat
    -> abt '[] 'HProb
    -> abt '[] ('HMeasure 'HInt)
binomial n p =
    sumV <$> plate n (const $ ((\b -> if_ b (int_ 1) (int_ 0)) <$> bern p))

-- BUG: would it be better to 'observe' that @p >= 1@ before doing everything? At least that way things would be /defined/ for all inputs...
negativeBinomial
    :: (ABT Term abt)
    => abt '[] 'HNat
    -> abt '[] 'HProb -- N.B., must actually be between 0 and 1
    -> abt '[] ('HMeasure 'HNat)
negativeBinomial r p =
    gamma (nat2prob r) (recip (recip p `unsafeMinusProb` prob_ 1)) >>= poisson

geometric :: (ABT Term abt) => abt '[] 'HProb -> abt '[] ('HMeasure 'HNat)
geometric = negativeBinomial (nat_ 1)


multinomial
    :: (ABT Term abt)
    => abt '[] 'HNat
    -> abt '[] ('HArray 'HProb)
    -> abt '[] ('HMeasure ('HArray 'HProb))
multinomial n v =
    reduce (liftM2 (zipWithV (+)))
        (dirac (constV (size v) (prob_ 0)))
        (constV n (unitV (size v) <$> categorical v))

dirichlet
    :: (ABT Term abt)
    => abt '[] ('HArray 'HProb)
    -> abt '[] ('HMeasure ('HArray 'HProb))
dirichlet a = normalizeV <$> plate (size a) (\ i -> a ! i  `gamma` prob_ 1)

----------------------------------------------------------------
----------------------------------------------------------- fin.
