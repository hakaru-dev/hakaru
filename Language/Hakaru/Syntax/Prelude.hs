{-# LANGUAGE TypeOperators
           , KindSignatures
           , DataKinds
           , TypeFamilies
           , GADTs
           , FlexibleInstances
           , NoImplicitPrelude
           #-}

{-# OPTIONS_GHC -Wall -fwarn-tabs #-}
----------------------------------------------------------------
--                                                    2015.06.30
-- |
-- Module      :  Language.Hakaru.Syntax.Prelude
-- Copyright   :  Copyright (c) 2015 the Hakaru team
-- License     :  BSD3
-- Maintainer  :  wren@community.haskell.org
-- Stability   :  experimental
-- Portability :  GHC-only
--
-- A replacement for Haskell's Prelude, using the familiar symbols
-- in order to construct 'AST's and 'ABT's. This is only necessary
-- if we want to use Hakaru as an embedded language in Haskell, but
-- it also provides some examples of how to use the infrastructure.
----------------------------------------------------------------
module Language.Hakaru.Syntax.Prelude where

-- TODO: implement and use Prelude's fromInteger and fromRational, so we can use numeric literals!
import Prelude (Maybe(..), Bool(..), Int, Double, Functor(..), ($), flip, error, otherwise)
import qualified Prelude
import           Data.Sequence        (Seq)
import qualified Data.Sequence        as Seq
import           Data.Proxy
import           Control.Category     (Category(..))
import           Data.Number.LogFloat (LogFloat)

import Language.Hakaru.Syntax.Nat
import Language.Hakaru.Syntax.DataKind
import Language.Hakaru.Syntax.TypeEq (Sing, SingI(sing))
import Language.Hakaru.Syntax.HClasses
import Language.Hakaru.Syntax.Coercion
import Language.Hakaru.Syntax.AST
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

app :: (ABT abt) => abt (a ':-> b) -> abt a -> abt b
app = (syn .) . App_

app2 :: (ABT abt) => abt (a ':-> b ':-> c) -> abt a -> abt b -> abt c
app2 = (app .) . app

app3 :: (ABT abt) => abt (a ':-> b ':-> c ':-> d) -> abt a -> abt b -> abt c -> abt d
app3 = (app2 .) . app

primOp0_ :: (ABT abt) => PrimOp a -> abt a
primOp0_ = syn . PrimOp_

primOp1_ :: (ABT abt) => PrimOp (a ':-> b) -> abt a -> abt b
primOp1_ = app . primOp0_

primOp2_ :: (ABT abt) => PrimOp (a ':-> b ':-> c) -> abt a -> abt b -> abt c
primOp2_ = app2 . primOp0_

primOp3_ :: (ABT abt) => PrimOp (a ':-> b ':-> c ':-> d) -> abt a -> abt b -> abt c -> abt d
primOp3_ = app3 . primOp0_

measure0_ :: (ABT abt) => Measure a -> abt a
measure0_ = syn . Measure_

measure1_ :: (ABT abt) => Measure (a ':-> b) -> abt a -> abt b
measure1_ = app . measure0_

measure2_ :: (ABT abt) => Measure (a ':-> b ':-> c) -> abt a -> abt b -> abt c
measure2_ = app2 . measure0_




-- N.B., we don't take advantage of commutativity, for more predictable
-- AST outputs. However, that means we can end up being slow...
--
-- N.B., we also don't try to eliminate the identity elements or
-- do cancellations because (a) it's undecidable in general, and
-- (b) that's prolly better handled as a post-processing simplification
-- step
--
-- TODO: generalize these two from [] to Foldable?

unsafeNaryOp_ :: (ABT abt) => NaryOp a -> [abt a] -> abt a
unsafeNaryOp_ o = go Seq.empty
    where
    go es []      = syn $ NaryOp_ o es -- N.B., @es@ may be empty!
    go es (e:es') =
        case matchNaryOp o e of
        Nothing   -> go (es Seq.|> e)    es'
        Just es'' -> go (es Seq.>< es'') es'

naryOp_withIdentity :: (ABT abt) => NaryOp a -> abt a -> [abt a] -> abt a
naryOp_withIdentity o i = go Seq.empty
    where
    go es []
        | Seq.null es = i
        | otherwise   = syn $ NaryOp_ o es
    go es (e:es') =
        case matchNaryOp o e of
        Nothing   -> go (es Seq.|> e)    es'
        Just es'' -> go (es Seq.>< es'') es'

naryOp2_ :: (ABT abt) => NaryOp a -> abt a -> abt a -> abt a
naryOp2_ o x y =
    case (matchNaryOp o x, matchNaryOp o y) of
    (Just xs, Just ys) -> syn $ NaryOp_ o (xs Seq.>< ys)
    (Just xs, Nothing) -> syn $ NaryOp_ o (xs Seq.|> y)
    (Nothing, Just ys) -> syn $ NaryOp_ o (x  Seq.<| ys)
    (Nothing, Nothing) -> syn $ NaryOp_ o (x  Seq.<| Seq.singleton y)

matchNaryOp :: (ABT abt) => NaryOp a -> abt a -> Maybe (Seq (abt a))
matchNaryOp o e =
    caseVarSynABT e
        (\_ _ -> Nothing)
        $ \t  ->
            case t of
            NaryOp_ o' xs | o' Prelude.== o -> Just xs
            _ -> Nothing

--- TODO: give @k@ an actual @Var@ instead of the @Variable@ name? If we try that, then be sure to check 'uneither'
freshVar :: (ABT abt) => (Variable -> abt a) -> abt a
freshVar k = k $ error "TODO: figure out how to implement freshVar in terms of binder"


----------------------------------------------------------------
----- Now for the actual EDSL

{-
infixl 1 `bind`, `bind_`, `bindx`
infix  4 `less`, `equal`, `less_`, `equal_`
infixl 9 `app`
infixr 9 `pair`

infixl 1 >>=, >>
infixr 1 =<<
infixr 1 <=<, >=>
infixr 9 .
infixr 0 $
infixl 4 <$>, <$, <*>, <*, *>
-}

infixr 2 ||
infixr 3 &&
infix  4 ==, /=, <, <=, >, >=
infixl 6 +, -
infixl 7 *, /
infixr 8 ^, ^^, ** -- ^+, ^*

-- TODO: some infix notation reminiscent of \"::\"
ann_ :: (ABT abt) => Sing a -> abt a -> abt a
ann_ = (syn .) . Ann_

coerceTo_ :: (ABT abt) => Coercion a b -> abt a -> abt b
coerceTo_ = (syn .) . CoerceTo_

unsafeFrom_ :: (ABT abt) => Coercion a b -> abt b -> abt a
unsafeFrom_ = (syn .) . UnsafeFrom_

value_ :: (ABT abt) => Value a  -> abt a
value_ = syn . Value_
bool_  :: (ABT abt) => Bool     -> abt HBool
bool_  = syn . Value_ . VDatum . (\b -> if b then dTrue else dFalse)
nat_   :: (ABT abt) => Nat      -> abt 'HNat
nat_   = value_ . VNat
int_   :: (ABT abt) => Int      -> abt 'HInt
int_   = value_ . VInt
prob_  :: (ABT abt) => LogFloat -> abt 'HProb
prob_  = value_ . VProb
real_  :: (ABT abt) => Double   -> abt 'HReal
real_  = value_ . VReal

-- Boolean operators
true, false :: (ABT abt) => abt HBool
true  = bool_ True
false = bool_ False

-- TODO: simplifications: involution, distribution, constant-propogation
not :: (ABT abt) => abt HBool -> abt HBool
not = primOp1_ Not

and, or :: (ABT abt) => [abt HBool] -> abt HBool
and = naryOp_withIdentity And true
or  = naryOp_withIdentity Or  false

(&&), (||),
    -- (</=>), (<==>), (==>), (<==), (\\), (//) -- TODO: better names?
    nand, nor
    :: (ABT abt) => abt HBool -> abt HBool -> abt HBool
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
(==), (/=) :: (ABT abt, HOrder a) => abt a -> abt a -> abt HBool
(==) = primOp2_ Equal
(/=) = (not .) . (==)

(<), (<=), (>), (>=) :: (ABT abt, HOrder a) => abt a -> abt a -> abt HBool
(<)    = primOp2_ Less
x <= y = (x < y) || (x == y)
(>)    = flip (<)
x >= y = not (x < y) -- or: @flip (<=)@

min, max :: (ABT abt, HOrder a) => abt a -> abt a -> abt a
min = naryOp2_ Min
max = naryOp2_ Max

-- TODO: if @a@ is bounded, then we can make these safe...
minimum, maximum :: (ABT abt, HOrder a) => [abt a] -> abt a
minimum = unsafeNaryOp_ Min
maximum = unsafeNaryOp_ Max


-- HSemiring operators
(+), (*) :: (ABT abt, HSemiring a) => abt a -> abt a -> abt a
(+) = naryOp2_ Sum
(*) = naryOp2_ Prod

{-
-- TODO
zero, one :: (ABT abt, HSemiring a) => abt a

sum, product :: (ABT abt, HSemiring a) => [abt a] -> abt a
sum     = naryOp_withIdentity Sum  zero
product = naryOp_withIdentity Prod one
-}

-- TODO: simplifications
(^) :: (ABT abt, HSemiring a) => abt a -> abt 'HNat -> abt a
(^) = primOp2_ (NatPow {- at type @a@ -})

-- TODO: this is actually safe, how can we capture that?
-- TODO: is this type restruction actually helpful anywhere for us?
-- If so, we ought to make this function polymorphic so that we can
-- use it for HSemirings which are not HRings too...
square :: (ABT abt, HRing a) => abt a -> abt (NonNegative a)
square e = unsafeFrom_ signed (e ^ nat_ 2)


-- HRing operators
(-) :: (ABT abt, HRing a) => abt a -> abt a -> abt a
x - y = x + negate y

-- BUG: can't just pattern match on (App_ (PrimOp_ Negate) e)
-- anymore; can't even match on (App_ (Syn (PrimOp_ Negate)) e).
-- We need to implement our AST-pattern matching stuff in order to
-- clean this up...
--
-- TODO: do we really want to distribute negation over addition /by
-- default/? Clearly we'll want to do that in some
-- optimization\/partial-evaluation pass, but do note that it makes
-- terms larger in general...
negate :: (ABT abt, HRing a) => abt a -> abt a
negate e0 =
    Prelude.maybe (primOp1_ Negate e0) id
        $ caseVarSynABT e0
            (\_ _ -> Nothing)
            $ \t0 ->
                case t0 of
                NaryOp_ Sum xs ->
                    Just . syn $ NaryOp_ Sum (fmap negate xs)
                App_ f e ->
                    caseVarSynABT f
                        (\_ _ -> Nothing)
                        (\ft  ->
                            case ft of
                            PrimOp_ Negate -> Just e
                            _              -> Nothing)
                _ -> Nothing


-- TODO: test case: @negative . square@ simplifies away the intermediate coercions. (cf., normal')
-- BUG: this can lead to ambiguity when used with the polymorphic functions of RealProb.
-- | An occasionally helpful variant of 'negate'.
negative :: (ABT abt, HRing a) => abt (NonNegative a) -> abt a
negative = negate . coerceTo_ signed


abs :: (ABT abt, HRing a) => abt a -> abt a
abs = coerceTo_ signed . abs_

abs_ :: (ABT abt, HRing a) => abt a -> abt (NonNegative a)
abs_ e =
    Prelude.maybe (primOp1_ Abs e) id
        $ caseVarSynABT e
            (\_ _ -> Nothing)
            $ \t  ->
                case t of
                -- BUG: can't use the 'Signed' pattern synonym, because that /requires/ the input to be (NonNegative a), instead of giving us the information that it is.
                CoerceTo_ (ConsCoercion PrimSigned IdCoercion) e' -> Just e'
                _ -> Nothing


-- TODO: any obvious simplifications? idempotent?
signum :: (ABT abt, HRing a) => abt a -> abt a
signum = primOp1_ Signum


-- HFractional operators
(/) :: (ABT abt, HFractional a) => abt a -> abt a -> abt a
x / y = x * recip y


-- TODO: generalize this pattern so we don't have to repeat it...
--
-- TODO: do we really want to distribute reciprocal over multiplication
-- /by default/? Clearly we'll want to do that in some
-- optimization\/partial-evaluation pass, but do note that it makes
-- terms larger in general...
recip :: (ABT abt, HFractional a) => abt a -> abt a
recip e0 =
    Prelude.maybe (primOp1_ Recip e0) id
        $ caseVarSynABT e0
            (\_ _ -> Nothing)
            $ \t0 ->
                case t0 of
                NaryOp_ Prod xs ->
                    Just . syn $ NaryOp_ Prod (fmap recip xs)
                App_ f e ->
                    caseVarSynABT f
                        (\_ _ -> Nothing)
                        (\ft  ->
                            case ft of
                            PrimOp_ Recip -> Just e
                            _             -> Nothing)
                _ -> Nothing


-- TODO: simplifications
(^^) :: (ABT abt, HFractional a) => abt a -> abt 'HInt -> abt a
x ^^ y =
    if_ (y < int_ 0)
        (recip x ^ abs_ y)
        (x ^ abs_ y)


-- HRadical operators
-- TODO: simplifications
thRootOf :: (ABT abt, HRadical a) => abt 'HNat -> abt a -> abt a
n `thRootOf` x = primOp2_ NatRoot x n

-- N.B., HProb is the only HRadical type (for now...)
sqrt :: (ABT abt, HRadical a) => abt a -> abt a
sqrt = (nat_ 2 `thRootOf`)

betaFunc :: (ABT abt) => abt 'HProb -> abt 'HProb -> abt 'HProb
betaFunc = primOp2_ BetaFunc

{-
-- TODO: simplifications
(^+) :: (ABT abt, HRadical a) => abt a -> abt 'HPositiveRational -> abt a
x ^+ y = casePositiveRational y $ \n d -> d `thRootOf` (x ^ n)

(^*) :: (ABT abt, HRadical a) => abt a -> abt 'HRational -> abt a
x ^* y = caseRational y $ \n d -> d `thRootOf` (x ^^ n)
-}

-- HACK: we define this class in order to gain more polymorphism;
-- but, will it cause type inferencing issues? Excepting 'log'
-- (which should be moved out of the class) these are all safe.
class RealProb (a :: Hakaru) where
    (**) :: (ABT abt) => abt 'HProb -> abt a -> abt 'HProb
    exp  :: (ABT abt) => abt a -> abt 'HProb
    log  :: (ABT abt) => abt 'HProb -> abt a -- HACK
    erf  :: (ABT abt) => abt a -> abt a
    pi   :: (ABT abt) => abt a
    infinity :: (ABT abt) => abt a
    gammaFunc :: (ABT abt) => abt a -> abt 'HProb

instance RealProb 'HReal where
    (**)      = primOp2_ RealPow
    exp       = primOp1_ Exp
    log       = primOp1_ Log
    erf       = primOp1_ (Erf {- 'HReal -})
    pi        = coerceTo_ signed $ primOp0_ Pi
    infinity  = coerceTo_ signed $ primOp0_ Infinity
    gammaFunc = primOp1_ GammaFunc

instance RealProb 'HProb where
    x ** y    = primOp2_ RealPow x (coerceTo_ signed y)
    exp       = primOp1_ Exp . coerceTo_ signed
    log       = unsafeFrom_ signed . primOp1_ Log -- error for inputs in [0,1)
    erf       = primOp1_ (Erf {- 'HProb -})
    pi        = primOp0_ Pi
    infinity  = primOp0_ Infinity
    gammaFunc = primOp1_ GammaFunc . coerceTo_ signed

logBase
    :: (ABT abt, RealProb a, HFractional a)
    => abt 'HProb
    -> abt 'HProb
    -> abt a
logBase b x = log x / log b -- undefined when b == 1

sin, cos, tan, asin, acos, atan, sinh, cosh, tanh, asinh, acosh, atanh
    :: (ABT abt) => abt 'HReal -> abt 'HReal
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

-- instance (ABT abt) => Base abt where not already defined above

datum_
    :: (ABT abt)
    => Datum abt ('HData t (Code t))
    -> abt ('HData t (Code t))
datum_ = syn . Datum_

unit   :: (ABT abt) => abt HUnit
unit   = datum_ dUnit

pair   :: (ABT abt) => abt a -> abt b -> abt (HPair a b)
pair   = (datum_ .) . dPair

unpair
    :: (ABT abt, SingI a, SingI b)
    => abt (HPair a b)
    -> (abt a -> abt b -> abt c)
    -> abt c
unpair e f = 
    freshVar $ \x ->
    freshVar $ \y ->
    syn $ Case_ e
        [Branch (PDatum $ dPair PVar PVar)
            (open x . open y $ f (var x sing) (var y sing))]

inl :: (ABT abt) => abt a -> abt (HEither a b)
inl = datum_ . dInl

inr :: (ABT abt) => abt b -> abt (HEither a b)
inr = datum_ . dInr

uneither
    :: (ABT abt, SingI a, SingI b)
    => abt (HEither a b)
    -> (abt a -> abt c)
    -> (abt b -> abt c)
    -> abt c
uneither e l r = 
    freshVar $ \x ->
    syn $ Case_ e
        [ Branch (PDatum $ dInl PVar) (open x $ l (var x sing))
        , Branch (PDatum $ dInr PVar) (open x $ r (var x sing))
        ]

if_ :: (ABT abt) => abt HBool -> abt a -> abt a -> abt a
if_ b t f =
    syn $ Case_ b
        [ Branch (PDatum dTrue)  t
        , Branch (PDatum dFalse) f
        ]

nil_      :: ABT abt => abt (HList a)
nil_      = datum_ dNil

cons_     :: ABT abt => abt a -> abt (HList a) -> abt (HList a)
cons_     = (datum_ .) . dCons

list_     :: ABT abt => [abt a] -> abt (HList a)
list_     = Prelude.foldr cons_ nil_

nothing_  :: ABT abt => abt (HMaybe a)
nothing_  = datum_ dNothing

just_     :: ABT abt => abt a -> abt (HMaybe a)
just_     = datum_ . dJust

maybe_    :: ABT abt => Maybe (abt a) -> abt (HMaybe a)
maybe_    = Prelude.maybe nothing_ just_


unsafeProb :: (ABT abt) => abt 'HReal -> abt 'HProb
unsafeProb = unsafeFrom_ signed

fromProb   :: (ABT abt) => abt 'HProb -> abt 'HReal
fromProb   = coerceTo_ signed

fromInt    :: (ABT abt) => abt 'HInt  -> abt 'HReal
fromInt    = coerceTo_ continuous

negativeInfinity :: (ABT abt) => abt 'HReal
negativeInfinity = primOp0_ NegativeInfinity

fix :: (ABT abt, SingI a) => (abt a -> abt a) -> abt a
fix f = 
    freshVar $ \x ->
    syn . Fix_ . open x $ f (var x sing)

-- TODO: rename to @array@
vector
    :: (ABT abt)
    => abt 'HInt
    -> (abt 'HInt -> abt a)
    -> abt ('HArray a)
vector n f =
    freshVar $ \x ->
    syn . Array_ (unsafeFrom_ signed n) . open x $ f (var x sing)

empty :: (ABT abt) => abt ('HArray a)
empty = primOp0_ Empty

-- TODO: rename to @(!)@
index :: (ABT abt) => abt ('HArray a) -> abt 'HInt -> abt a
index xs i = primOp2_ Index xs (unsafeFrom_ signed i)

size :: (ABT abt) => abt ('HArray a) -> abt 'HInt
size = coerceTo_ signed . primOp1_ Size

reduce
    :: (ABT abt, Bindable abt, SingI a)
    => (abt a -> abt a -> abt a)
    -> abt a
    -> abt ('HArray a)
    -> abt a
reduce f = primOp3_ Reduce (lam $ \x -> lam $ \y -> f x y)


-- instance (ABT abt) => Mochastic (abt) where
bind
    :: (ABT abt, SingI a)
    => abt ('HMeasure a)
    -> (abt a -> abt ('HMeasure b))
    -> abt ('HMeasure b)
bind e f = 
    freshVar $ \x ->
    syn . Bind_ e . open x $ f (var x sing)

dirac    :: (ABT abt) => abt a -> abt ('HMeasure a)
dirac    = measure1_ Dirac

lebesgue :: (ABT abt) => abt ('HMeasure 'HReal)
lebesgue = measure0_  Lebesgue

counting :: (ABT abt) => abt ('HMeasure 'HInt)
counting = measure0_  Counting

superpose
    :: (ABT abt)
    => [(abt 'HProb, abt ('HMeasure a))]
    -> abt ('HMeasure a)
superpose = syn . Superpose_

categorical
    :: (ABT abt)
    => abt ('HArray 'HProb)
    -> abt ('HMeasure 'HNat)
categorical = measure1_ Categorical
{-
-- TODO: need to insert the coercion in the right place... Also, implement 'weight' and 'sumV'
categorical' v =
    counting `bind` \i ->
    if_ (i >= 0 && i < size v)
        (weight (index v i / sumV v) (dirac i))
        (superpose [])
-}


-- TODO: make Uniform polymorphic, so that if the two inputs are
-- HProb then we know the measure must be over HProb too
uniform, uniform'
    :: (ABT abt)
    => abt 'HReal
    -> abt 'HReal
    -> abt ('HMeasure 'HReal)
uniform = measure2_ Uniform

uniform' lo hi = 
    lebesgue `bind` \x ->
    if_ (lo < x && x < hi)
        -- TODO: how can we capture that this 'unsafeProb' is safe? (and that this 'recip' isn't Infinity, for that matter)
        (superpose [(recip (unsafeProb (hi - lo)), dirac x)])
        (superpose [])


normal, normal'
    :: (ABT abt)
    => abt 'HReal
    -> abt 'HProb
    -> abt ('HMeasure 'HReal)
normal = measure2_ Normal

normal' mu sd  = 
    lebesgue `bind` \x ->
    superpose
        -- alas, we loose syntactic negation...
        [( exp (negate ((x - mu) ^ nat_ 2)  -- TODO: use negative\/square instead of negate\/(^2)
            / fromProb (prob_ 2 * sd ** real_ 2)) -- TODO: use square instead of (**2) ?
            / sd / sqrt (prob_ 2 * pi)
        , dirac x
        )]


poisson, poisson' :: (ABT abt) => abt 'HProb -> abt ('HMeasure 'HNat)
poisson = measure1_ Poisson

poisson' l = 
    counting `bind` \x ->
    -- TODO: use 'SafeFrom_' instead of @if_ (x >= int_ 0)@ so we can prove that @unsafeFrom_ signed x@ is actually always safe.
    if_ (x >= int_ 0 && prob_ 0 < l) -- BUG: do you mean @l /= 0@? why use (>=) instead of (<=)?
        (superpose
            [( l ** fromInt x -- BUG: why do you use (**) instead of (^^)?
                / gammaFunc (fromInt x + real_ 1) -- TODO: use factorial instead of gammaFunc...
                / exp l
            , dirac (unsafeFrom_ signed x)
            )])
        (superpose [])


gamma, gamma'
    :: (ABT abt)
    => abt 'HProb
    -> abt 'HProb
    -> abt ('HMeasure 'HProb)
gamma = measure2_ Gamma

gamma' shape scale =
    lebesgue `bind` \x ->
    -- TODO: use 'SafeFrom_' instead of @if_ (real_ 0 < x)@ so we can prove that @unsafeProb x@ is actually always safe. Of course, then we'll need to mess around with checking (/=0) which'll get ugly... Use another SafeFrom_ with an associated NonZero type?
    if_ (real_ 0 < x)
        (let x_ = unsafeProb x in
         superpose
            [( x_ ** (fromProb shape - real_ 1)
                * exp (negate . fromProb $ x_ / scale)
                / (scale ** shape * gammaFunc shape)
            , dirac x_
            )])
        (superpose [])


beta, beta'
    :: (ABT abt)
    => abt 'HProb
    -> abt 'HProb
    -> abt ('HMeasure 'HProb)
beta = measure2_ Beta

beta' a b =
    -- TODO: make Uniform polymorphic, so that if the two inputs are HProb then we know the measure must be over HProb too, and hence @unsafeProb x@ must always be safe. Alas, capturing the safety of @unsafeProb (1-x)@ would take a lot more work...
    uniform (real_ 0) (real_ 1) `bind` \x ->
    let x_ = unsafeProb x in
    superpose
        [( x_ ** (fromProb a - real_ 1)
            * unsafeProb (real_ 1 - x) ** (fromProb b - real_ 1)
            / betaFunc a b
        , dirac x_
        )]


dp  :: (ABT abt)
    => abt 'HProb
    -> abt ('HMeasure a)
    -> abt ('HMeasure ('HMeasure a))
dp = measure2_ DirichletProcess


plate
    :: (ABT abt)
    => abt ('HArray ('HMeasure          a))
    -> abt (         'HMeasure ('HArray a))
plate = measure1_ Plate
{-
-- TODO: the array stuff...
plate' v = reduce r z (mapV m v)
    where
    r   = liftM2 concatV
    z   = dirac empty
    m a = liftM (vector 1 . const) a
-}


chain
    :: (ABT abt)
    => abt ('HArray (s ':-> 'HMeasure (HPair          a  s)))
    -> abt (         s ':-> 'HMeasure (HPair ('HArray a) s))
chain = measure1_ Chain
{-
-- TODO: the array stuff...
chain' v = reduce r z (mapV m v)
    where
    r x y = lam $ \s ->
            app x s `bind` \v1s1 ->
            unpair v1s1 $ \v1 s1 ->
            app y s1 `bind` \v2s2 ->
            unpair v2s2 $ \v2 s2 ->
            dirac (pair (concatV v1 v2) s2)
    z     = lam $ \s -> dirac (pair empty s)
    m a   = lam $ \s -> liftM (`unpair` pair . vector 1 . const) (app a s)
-}


-- instance (ABT abt) => Integrate abt where
integrate
    :: (ABT abt, Bindable abt)
    => abt 'HReal
    -> abt 'HReal
    -> (abt 'HReal -> abt 'HProb)
    -> abt 'HProb
integrate lo hi f =
    primOp3_ Integrate lo hi (lam f)

summate
    :: (ABT abt, Bindable abt)
    => abt 'HReal
    -> abt 'HReal
    -> (abt 'HInt -> abt 'HProb)
    -> abt 'HProb
summate lo hi f =
    primOp3_ Summate lo hi (lam f)


-- instance (ABT abt) => Lambda abt where
-- 'app' already defined

lam :: (ABT abt, Bindable abt, SingI a)
    => (abt a -> abt b)
    -> abt (a ':-> b)
lam = binder (\x e -> syn . Lam_ Proxy $ open x e) "_" sing

{-
-- some test cases to make sure we tied-the-knot successfully:
> let
    lam :: (ABT abt, Bindable abt)
        => String
        -> Sing a
        -> (abt a -> abt b)
        -> abt (a ':-> b)
    lam name typ = binder (\x e -> syn . Lam_ Proxy $ open x e) name typ
> lam "x" SInt (\x -> x) :: TrivialABT ('HInt ':-> 'HInt)
> lam "x" SInt (\x -> lam "y" SInt $ \y -> x < y) :: TrivialABT ('HInt ':-> 'HInt ':-> 'HBool)
-}

let_
    :: (ABT abt, Bindable abt, SingI a)
    => abt a
    -> (abt a -> abt b)
    -> abt b
let_ e = binder (\x f -> syn . Let_ e $ open x f) "_" sing


-- instance (ABT abt) => Lub abt where
lub :: (ABT abt) => abt a -> abt a -> abt a
lub = (syn .) . Lub_

bot :: (ABT abt) => abt a
bot = syn Bot_

----------------------------------------------------------------
----------------------------------------------------------- fin.
