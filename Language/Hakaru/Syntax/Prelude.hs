{-# LANGUAGE KindSignatures
           , DataKinds
           , TypeFamilies
           , GADTs
           , FlexibleInstances
           , NoImplicitPrelude
           #-}

{-# OPTIONS_GHC -Wall -fwarn-tabs #-}
----------------------------------------------------------------
--                                                    2015.06.24
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

-- import Prelude hiding (id, (.), Ord(..), Num(..), Integral(..), Fractional(..), Floating(..), Real(..), RealFrac(..), RealFloat(..), (^), (^^),.......)
import Prelude (Maybe(..), Bool(..), Int, Double, Functor(..), flip, ($), error, otherwise)
import qualified Prelude
import           Data.Sequence        (Seq)
import qualified Data.Sequence        as Seq
import           Data.Proxy
import           Control.Category     (Category(..))
import           Data.Number.LogFloat (LogFloat)

import Language.Hakaru.Syntax.Nat
import Language.Hakaru.Syntax.DataKind
import Language.Hakaru.Syntax.TypeEq (SingI(sing))
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

app :: (ABT abt) => abt ('HFun a b) -> abt a -> abt b
app = (syn .) . App_

app2 :: (ABT abt) => abt ('HFun a ('HFun b c)) -> abt a -> abt b -> abt c
app2 = (app .) . app

app3 :: (ABT abt) => abt ('HFun a ('HFun b ('HFun c d))) -> abt a -> abt b -> abt c -> abt d
app3 = (app2 .) . app

primOp0_ :: (ABT abt) => PrimOp a -> abt a
primOp0_ = syn . PrimOp_

primOp1_ :: (ABT abt) => PrimOp ('HFun a b) -> abt a -> abt b
primOp1_ = app . primOp0_

primOp2_ :: (ABT abt) => PrimOp ('HFun a ('HFun b c)) -> abt a -> abt b -> abt c
primOp2_ = app2 . primOp0_

primOp3_ :: (ABT abt) => PrimOp ('HFun a ('HFun b ('HFun c d))) -> abt a -> abt b -> abt c -> abt d
primOp3_ = app3 . primOp0_

-- TODO: generalize from [] to Foldable?
unsafeNaryOp_ :: (ABT abt) => NaryOp a -> [abt a] -> abt a
unsafeNaryOp_ o = go Seq.empty
    where
    go es []      = syn $ NaryOp_ o es -- N.B., @es@ may be empty!
    go es (e:es') =
        case matchNaryOp o e of
        Nothing   -> go (es Seq.|> e)    es'
        Just es'' -> go (es Seq.>< es'') es'

-- TODO: generalize from [] to Foldable?
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


-- TODO: give @k@ an actual @Var@ instead of the @Variable@ name? If we try that, then be sure to check 'uneither'
-- TODO: how can we generate fresh names? Should we have @abt@ be a monad?
freshVar :: (ABT abt) => (Variable -> abt a) -> abt a
freshVar k = k $ error "TODO"


----------------------------------------------------------------
----- Now for the actual EDSL

coerceTo_ :: (ABT abt) => Coercion a b -> abt a -> abt b
coerceTo_ = (syn .) . CoerceTo_

unsafeFrom_ :: (ABT abt) => Coercion a b -> abt b -> abt a
unsafeFrom_ = (syn .) . UnsafeFrom_

value_ :: (ABT abt) => Value a  -> abt a
value_ = syn . Value_
bool_  :: (ABT abt) => Bool     -> abt 'HBool
bool_  = value_ . Bool_
nat_   :: (ABT abt) => Nat      -> abt 'HNat
nat_   = value_ . Nat_
int_   :: (ABT abt) => Int      -> abt 'HInt
int_   = value_ . Int_
prob_  :: (ABT abt) => LogFloat -> abt 'HProb
prob_  = value_ . Prob_
real_  :: (ABT abt) => Double   -> abt 'HReal
real_  = value_ . Real_


-- Boolean operators
true, false :: (ABT abt) => abt 'HBool
true  = bool_ True
false = bool_ False

-- TODO: simplifications: involution, distribution, constant-propogation
not :: (ABT abt) => abt 'HBool -> abt 'HBool
not = primOp1_ Not

and, or :: (ABT abt) => [abt 'HBool] -> abt 'HBool
and = naryOp_withIdentity And true
or  = naryOp_withIdentity Or  false

(&&), (||),
    -- (</=>), (<==>), (==>), (<==), (\\), (//)
    nand, nor
    :: (ABT abt) => abt 'HBool -> abt 'HBool -> abt 'HBool
(&&) = naryOp2_ And
(||) = naryOp2_ Or
-- (</=>) = primOp2_ Xor
-- (<==>) = primOp2_ Iff
-- (==>)  = primOp2_ Impl
-- (<==)  = flip (==>)
-- (\\)   = primOp2_ Diff
-- (//)   = flip (\\)
nand   = primOp2_ Nand
nor    = primOp2_ Nor


-- HEq & HOrder operators
(==), (/=) :: (ABT abt, HOrder a) => abt a -> abt a -> abt 'HBool
(==) = primOp2_ Equal
(/=) = (not .) . (==)

(<), (<=), (>), (>=) :: (ABT abt, HOrder a) => abt a -> abt a -> abt 'HBool
(<)    = primOp2_ Less
x <= y = (x < y) || (x == y)
(>)    = flip (<)
(>=)   = flip (<=)

min, max :: (ABT abt, HOrder a) => abt a -> abt a -> abt a
min = naryOp2_ Min
max = naryOp2_ Max

-- TODO: if @a@ is bounded, then we can make these safe...
minimum, maximum :: (ABT abt, HOrder a) => [abt a] -> abt a
minimum = unsafeNaryOp_ Min
maximum = unsafeNaryOp_ Max

-- N.B., we don't take advantage of commutativity, for more predictable AST outputs. However, that means we can end up being really slow;
-- N.B., we also don't try to eliminate the identity elements or do cancellations because (a) it's undecidable in general, and (b) that's prolly better handled as a post-processing simplification step

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


-- HRing operators
(-) :: (ABT abt, HRing a) => abt a -> abt a -> abt a
x - y = x + negate y

-- BUG: can't just pattern match on (App_ (PrimOp_ Negate) e) anymore; can't even match on (App_ (Syn (PrimOp_ Negate)) e). We need to implement our AST-pattern matching stuff in order to clean this up...
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


abs :: (ABT abt, HRing a) => abt a -> abt a
abs = coerceTo_ signed . abs_

abs_ :: (ABT abt, HRing a) => abt a -> abt (NonNegative a)
abs_ e =
    Prelude.maybe (primOp1_ Abs e) id
        $ caseVarSynABT e
            (\_ _ -> Nothing)
            $ \t  ->
                case t of
                CoerceTo_ (ConsCoercion Signed IdCoercion) e' -> Just e'
                _ -> Nothing


-- TODO: any obvious simplifications? idempotent?
signum :: (ABT abt, HRing a) => abt a -> abt a
signum = primOp1_ Signum


-- HFractional operators
(/) :: (ABT abt, HFractional a) => abt a -> abt a -> abt a
x / y = x * recip y

-- TODO: generalize this pattern so we don't have to repeat it...
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

sqrt :: (ABT abt, HRadical a) => abt a -> abt a
sqrt = (nat_ 2 `thRootOf`)

{-
-- TODO: simplifications
(^+) :: (ABT abt, HRadical a) => abt a -> abt 'HPositiveRational -> abt a
x ^+ y = casePositiveRational y $ \n d -> d `thRootOf` (x ^ n)

(^*) :: (ABT abt, HRadical a) => abt a -> abt 'HRational -> abt a
x ^* y = caseRational y $ \n d -> d `thRootOf` (x ^^ n)
-}


class RealProb (a :: Hakaru *) where
    (**) :: (ABT abt) => abt 'HProb -> abt a -> abt 'HProb
    exp  :: (ABT abt) => abt a -> abt 'HProb
    log  :: (ABT abt) => abt 'HProb -> abt a -- HACK
    erf  :: (ABT abt) => abt a -> abt a
    pi   :: (ABT abt) => abt a
    infinity :: (ABT abt) => abt a

instance RealProb 'HReal where
    (**)     = primOp2_ RealPow
    exp      = primOp1_ Exp
    log      = primOp1_ Log
    erf      = primOp1_ (Erf {- 'HReal -})
    pi       = coerceTo_ signed $ primOp0_ Pi
    infinity = coerceTo_ signed $ primOp0_ Infinity

instance RealProb 'HProb where
    x ** y   = primOp2_ RealPow x (coerceTo_ signed y)
    exp      = primOp1_ Exp . coerceTo_ signed
    log      = unsafeFrom_ signed . primOp1_ Log -- error for inputs in [0,1)
    erf      = primOp1_ (Erf {- 'HProb -})
    pi       = primOp0_ Pi
    infinity = primOp0_ Infinity

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
unit :: (ABT abt) => abt 'HUnit
unit = primOp0_ Unit

pair :: (ABT abt) => abt a -> abt b -> abt ('HPair a b)
pair = primOp2_ Pair

unpair
    :: (ABT abt, SingI a, SingI b)
    => abt ('HPair a b)
    -> (abt a -> abt b -> abt c)
    -> abt c
unpair e f =
    freshVar $ \x ->
    freshVar $ \y ->
    syn $ Case_ e
        [(PPair PVar PVar, open x . open y $ f (var x sing) (var y sing))]

inl :: (ABT abt) => abt a -> abt ('HEither a b)
inl = primOp1_ Inl

inr :: (ABT abt) => abt b -> abt ('HEither a b)
inr = primOp1_ Inr

uneither
    :: (ABT abt, SingI a, SingI b)
    => abt ('HEither a b)
    -> (abt a -> abt c)
    -> (abt b -> abt c)
    -> abt c
uneither e l r =
    freshVar $ \x ->
    syn $ Case_ e
        [ (PInl PVar, open x $ l (var x sing))
        , (PInr PVar, open x $ r (var x sing))
        ]

if_ :: (ABT abt) => abt 'HBool -> abt a -> abt a -> abt a
if_ b t f = syn $ Case_ b [(PTrue, t), (PFalse, f)]

unsafeProb :: (ABT abt) => abt 'HReal -> abt 'HProb
unsafeProb = unsafeFrom_ signed

fromProb   :: (ABT abt) => abt 'HProb -> abt 'HReal
fromProb   = coerceTo_ signed

fromInt    :: (ABT abt) => abt 'HInt  -> abt 'HReal
fromInt    = coerceTo_ continuous

negativeInfinity :: (ABT abt) => abt 'HReal
negativeInfinity = primOp0_ NegativeInfinity

gammaFunc :: (ABT abt) => abt 'HReal -> abt 'HProb
gammaFunc = primOp1_ GammaFunc

betaFunc :: (ABT abt) => abt 'HProb -> abt 'HProb -> abt 'HProb
betaFunc = primOp2_ BetaFunc

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
    :: (ABT abt, SingI a)
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
dirac    = primOp1_ Dirac
lebesgue :: (ABT abt) => abt ('HMeasure 'HReal)
lebesgue = primOp0_  Lebesgue
counting :: (ABT abt) => abt ('HMeasure 'HInt)
counting = primOp0_  Counting

superpose
    :: (ABT abt)
    => [(abt 'HProb, abt ('HMeasure a))]
    -> abt ('HMeasure a)
superpose = syn . Superpose_

{-
-- BUG: need to (a) fix the type, or (b) coerce @'HMeasure 'HNat@ to @'HMeasure 'HInt@
categorical
    :: (ABT abt)
    => abt ('HArray 'HProb)
    -> abt ('HMeasure 'HInt)
categorical = primOp1_ Categorical
{-
categorical v = 
    counting `bind` \i ->
    if_ (and_ [not_ (less i 0), less i (size v)])
        (weight (index v i / sumV v) (dirac i))
        (superpose [])
-}
-}

uniform
    :: (ABT abt)
    => abt 'HReal
    -> abt 'HReal
    -> abt ('HMeasure 'HReal)
uniform = primOp2_ Uniform
{-
uniform lo hi = 
    lebesgue `bind` \x ->
    if_ (and_ [less lo x, less x hi])
        (superpose [(recip (unsafeProb (hi - lo)), dirac x)])
        (superpose [])
-}

normal
    :: (ABT abt)
    => abt 'HReal
    -> abt 'HProb
    -> abt ('HMeasure 'HReal)
normal = primOp2_ Normal
{-
normal mu sd  = 
    lebesgue `bind` \x ->
    superpose
        [( exp_ (- (x - mu)^(2::Int)
            / fromProb (2 * pow_ sd 2))
            / sd / sqrt_ (2 * pi_)
        , dirac x
        )]
-}

{-
-- BUG: need to (a) fix the type, or (b) coerce @'HMeasure 'HNat@ to @'HMeasure 'HInt@
poisson :: (ABT abt) => abt 'HProb -> abt ('HMeasure 'HInt)
poisson = primOp1_ Poisson
{-
poisson l = 
    counting `bind` \x ->
    if_ (and_ [not_ (less x 0), less 0 l])
        (superpose
            [( pow_ l (fromInt x)
                / gammaFunc (fromInt x + 1)
                / exp_ (fromProb l)
            , dirac x
            )])
        (superpose [])
-}
-}

gamma
    :: (ABT abt)
    => abt 'HProb
    -> abt 'HProb
    -> abt ('HMeasure 'HProb)
gamma = primOp2_ Gamma
{-
gamma shape scale =
    lebesgue `bind` \x ->
    if_ (less 0 x)
        (let x_     = unsafeProb x
             shape_ = fromProb shape in
         superpose [(pow_ x_ (fromProb (shape - 1))
                    * exp_ (- fromProb (x_ / scale))
                    / (pow_ scale shape_ * gammaFunc shape_),
                    dirac (unsafeProb x))])
        (superpose [])
-}

beta
    :: (ABT abt)
    => abt 'HProb
    -> abt 'HProb
    -> abt ('HMeasure 'HProb)
beta = primOp2_ Beta
{-
beta a b =
    uniform 0 1 `bind` \x ->
    superpose
        [( pow_ (unsafeProb x    ) (fromProb a - 1)
            * pow_ (unsafeProb (1-x)) (fromProb b - 1)
            / betaFunc a b
        , dirac (unsafeProb x)
        )]
-}

dp  :: (ABT abt)
    => abt 'HProb
    -> abt ('HMeasure a)
    -> abt ('HMeasure ('HMeasure a))
dp = (syn .) . Dp_

plate
    :: (ABT abt)
    => abt ('HArray ('HMeasure          a))
    -> abt (         'HMeasure ('HArray a))
plate = syn . Plate_
{-
plate v = reduce r z (mapV m v)
    where r   = liftM2 concatV
          z   = dirac empty
          m a = liftM (vector 1 . const) a
-}

chain
    :: (ABT abt)
    => abt ('HArray ('HFun s ('HMeasure         ('HPair a s))))
    -> abt (         'HFun s ('HMeasure ('HPair ('HArray a) s)))
chain = syn . Chain_
{-
chain v = reduce r z (mapV m v)
    where r x y = lam (\s -> app x s `bind` \v1s1 ->
                             unpair v1s1 $ \v1 s1 ->
                             app y s1 `bind` \v2s2 ->
                             unpair v2s2 $ \v2 s2 ->
                             dirac (pair (concatV v1 v2) s2))
          z     = lam (\s -> dirac (pair empty s))
          m a   = lam (\s -> liftM (`unpair` pair . vector 1 . const)
                                   (app a s))
-}

-- instance (ABT abt) => Integrate abt where
integrate
    :: (ABT abt)
    => abt 'HReal
    -> abt 'HReal
    -> (abt 'HReal -> abt 'HProb)
    -> abt 'HProb
integrate lo hi f =
    freshVar $ \x ->
    syn . Integrate_ lo hi . open x $ f (var x sing)

summate
    :: (ABT abt)
    => abt 'HReal
    -> abt 'HReal
    -> (abt 'HInt -> abt 'HProb)
    -> abt 'HProb
summate lo hi f =
    freshVar $ \x ->
    syn . Summate_ lo hi . open x $ f (var x sing)


-- instance (ABT abt) => Lambda abt where
-- 'app' already defined

lam :: (ABT abt, SingI a) => (abt a -> abt b) -> abt ('HFun a b)
lam f = 
    freshVar $ \x ->
    syn . Lam_ Proxy . open x $ f (var x sing)

let_ :: (ABT abt, SingI a) => abt a -> (abt a -> abt b) -> abt b
let_ e f = 
    freshVar $ \x ->
    syn . Let_ e . open x $ f (var x sing)

-- instance (ABT abt) => Lub abt where
lub :: (ABT abt) => abt a -> abt a -> abt a
lub = (syn .) . Lub_

bot :: (ABT abt) => abt a
bot = syn Bot_
