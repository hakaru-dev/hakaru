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
import Prelude (Maybe(..), Bool(..), Int, Double, Functor(..), flip, ($), undefined)
import qualified Prelude
import           Data.Sequence        (Seq)
import qualified Data.Sequence        as Seq
-- import           Data.Proxy
import           Control.Category     (Category(..))
import           Data.Number.LogFloat (LogFloat)

import Language.Hakaru.Syntax.Nat
import Language.Hakaru.Syntax.DataKind
import Language.Hakaru.Syntax.AST
import Language.Hakaru.Syntax.ABT hiding (View(..))

----------------------------------------------------------------
{-
Below we implement a lot of simple optimizations; however, these
optimizations only apply if the client uses the type class methods
to produce the AST. We should implement a stand-alone function which
performs these sorts of optimizations, as a program transformation.
-}

app :: (ABT abt) => abt ('HFun a b) -> abt a -> abt b
app f x = syn $ App_ f x

app2 :: (ABT abt) => abt ('HFun a ('HFun b c)) -> abt a -> abt b -> abt c
app2 f x y = syn $ App_ (app f x) y

app3 :: (ABT abt) => abt ('HFun a ('HFun b ('HFun c d))) -> abt a -> abt b -> abt c -> abt d
app3 f x y z = syn $ App_ (app2 f x y) z

primOp0_ :: (ABT abt) => PrimOp a -> abt a
primOp0_ = syn . PrimOp_

primOp1_ :: (ABT abt) => PrimOp ('HFun a b) -> abt a -> abt b
primOp1_ = app . primOp0_

primOp2_ :: (ABT abt) => PrimOp ('HFun a ('HFun b c)) -> abt a -> abt b -> abt c
primOp2_ = app2 . primOp0_

primOp3_ :: (ABT abt) => PrimOp ('HFun a ('HFun b ('HFun c d))) -> abt a -> abt b -> abt c -> abt d
primOp3_ = app3 . primOp0_

naryOp_ :: (ABT abt) => NaryOp a -> AST abt a -> AST abt a -> AST abt a
naryOp_ o x y =
    case (matchNaryOp o x, matchNaryOp o y) of
    (Just xs, Just ys) -> NaryOp_ o (xs    Seq.>< ys)
    (Just xs, Nothing) -> NaryOp_ o (xs    Seq.|> syn y)
    (Nothing, Just ys) -> NaryOp_ o (syn x Seq.<| ys)
    (Nothing, Nothing) -> NaryOp_ o (syn x Seq.<| Seq.singleton (syn y))

matchNaryOp :: NaryOp a -> AST abt a -> Maybe (Seq (abt a))
matchNaryOp o (NaryOp_ o' xs) | o Prelude.== o' = Just xs
matchNaryOp _ _                                 = Nothing

coerceTo_ :: (ABT abt) => Coercion a b -> abt a -> abt b
coerceTo_ c = syn . CoerceTo_ c

unsafeFrom_ :: (ABT abt) => Coercion a b -> abt b -> abt a
unsafeFrom_ c = syn . UnsafeFrom_ c

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

not :: (ABT abt) => abt 'HBool -> abt 'HBool
not = primOp1_ Not


(&&), (||),
    -- (</=>), (<==>), (==>), (<==), (\\), (//)
    nand, nor
    :: (ABT abt) => abt 'HBool -> abt 'HBool -> abt 'HBool
(&&) = undefined -- TODO: naryOp_ And
(||) = undefined -- TODO: naryOp_ Or
-- (</=>) = primOp2_ Xor
-- (<==>) = primOp2_ Iff
-- (==>)  = primOp2_ Impl
-- (<==)  = flip (==>)
-- (\\)   = primOp2_ Diff
-- (//)   = flip (\\)
nand   = primOp2_ Nand
nor    = primOp2_ Nor


-- HEq & HOrder operators
(==), (/=)
    :: (ABT abt, HOrder a) => abt a -> abt a -> abt 'HBool
(==) = primOp2_ Equal
(/=) = (not .) . (==)

(<), (<=), (>), (>=)
    :: (ABT abt, HOrder a) => abt a -> abt a -> abt 'HBool
(<)    = primOp2_ Less
x <= y = (x < y) || (x == y)
(>)    = flip (<)
(>=)   = flip (<=)

min, max
    :: (ABT abt, HOrder a) => abt a -> abt a -> abt a
min = undefined -- TODO: naryOp_ Min
max = undefined -- TODO: naryOp_ Max

-- N.B., we don't take advantage of commutativity, for more predictable AST outputs. However, that means we can end up being really slow;
-- N.B., we also don't try to eliminate the identity elements or do cancellations because (a) it's undecidable in general, and (b) that's prolly better handled as a post-processing simplification step

-- HSemiring operators
(+), (*)
    :: (ABT abt, HSemiring a) => abt a -> abt a -> abt a
(+) = undefined -- TODO: naryOp_ Sum
(*) = undefined -- TODO: naryOp_ Prod

-- TODO: simplifications
(^) :: (ABT abt, HSemiring a) => abt a -> abt 'HNat -> abt a
(^) = primOp2_ (NatPow {- at type @a@ -})


-- HRing operators
(-) :: (ABT abt, HRing a) => abt a -> abt a -> abt a
x - y = x + negate y

-- BUG: can't just pattern match on (App_ (PrimOp_ Negate) e) anymore; can't even match on (App_ (Syn (PrimOp_ Negate)) e). We need to implement our AST-pattern matching stuff in order to clean this up...
negate :: (ABT abt, HRing a) => abt a -> abt a
negate e0 =
    case me' of
    Just e' -> e'
    Nothing -> primOp1_ Negate e0 -- default case
    where
    me' =
        caseVarSynABT e0
            (\_ _ -> Nothing)
            $ \t0 ->
                case t0 of
                NaryOp_ Sum xs -> Just . syn $ NaryOp_ Sum (fmap negate xs)
                App_ f e       ->
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
-- abs_ (CoerceTo_ (ConsCoercion Signed IdCoercion) e) = e -- BUG: we want to just return the @e@, but it's not AST...
abs_ = primOp1_ Abs

-- TODO: any obvious simplifications? idempotent?
signum :: (ABT abt, HRing a) => abt a -> abt a
signum = primOp1_ Signum


-- HFractional operators
(/) :: (ABT abt, HFractional a) => abt a -> abt a -> abt a
x / y = x * recip y

-- TODO: generalize this pattern so we don't have to repeat it...
recip :: (ABT abt, HFractional a) => abt a -> abt a
recip e0 =
    case me' of
    Just e' -> e'
    Nothing -> primOp1_ Recip e0 -- default case
    where
    me' =
        caseVarSynABT e0
            (\_ _ -> Nothing)
            $ \t0 ->
                case t0 of
                NaryOp_ Prod xs -> Just . syn $ NaryOp_ Prod (fmap recip xs)
                App_ f e        ->
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
-- TODO: simplify
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
    :: (ABT abt)
    => abt ('HPair a b)
    -> (abt a -> abt b -> abt c)
    -> abt c
unpair = undefined
{-
unpair e f = do
    x <- freshVar
    y <- freshVar
    return $ Case_ (syn e)
        [(PPair PVar PVar,
            open x (open y (syn $ f (var x sing) (var y sing)))]
-}

inl :: (ABT abt) => abt a -> abt ('HEither a b)
inl = primOp1_ Inl

inr :: (ABT abt) => abt b -> abt ('HEither a b)
inr = primOp1_ Inr

uneither
    :: (ABT abt)
    => abt ('HEither a b)
    -> (abt a -> abt c)
    -> (abt b -> abt c)
    -> abt c
uneither = undefined
{-
uneither e l r = do
    x <- freshVar
    return $ Case_ (syn e)
        [ (PInl PVar, open x (syn $ l (var x sing)))
        , (PInr PVar, open x (syn $ r (var x sing)))
        ]
-}

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

fix :: (ABT abt) => (abt a -> abt a) -> abt a
fix = undefined
{-
fix f = do
    x <- freshVar
    return $ Fix_ (open x (f (var x sing)))
-}

-- TODO: rename @array@
vector
    :: (ABT abt)
    => abt 'HInt
    -> (abt 'HInt -> abt a)
    -> abt ('HArray a)
vector = undefined
{-
vector n f = do
    x <- freshVar
    return $ Array_ (syn $ unsafeFrom_ signed n) (open x (f (var x sing)))
-}

empty :: (ABT abt) => abt ('HArray a)
empty = primOp0_ Empty

-- TODO: rename @(!)@
index :: (ABT abt) => abt ('HArray a) -> abt 'HInt -> abt a
index xs i = primOp2_ Index xs (unsafeFrom_ signed i)

size :: (ABT abt) => abt ('HArray a) -> abt 'HInt
size = coerceTo_ signed . primOp1_ Size

reduce
    :: (ABT abt)
    => (abt a -> abt a -> abt a)
    -> abt a
    -> abt ('HArray a)
    -> abt a
reduce f = primOp3_ Reduce (lam $ \x -> lam $ \y -> f x y)


-- instance (ABT abt) => Mochastic (abt) where
bind
    :: (ABT abt)
    => abt ('HMeasure a)
    -> (abt a -> abt ('HMeasure b))
    -> abt ('HMeasure b)
bind = undefined
{-
bind e f = do
    x <- freshVar
    return $ Bind_ (syn e) (open x (f (var x sing)))
-}

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
integrate = undefined
{-
integrate lo hi f = do
    x <- freshVar
    return $ Integrate_ (syn lo) (syn hi) (open x $ f (var x sing))
-}

summate
    :: (ABT abt)
    => abt 'HReal
    -> abt 'HReal
    -> (abt 'HInt -> abt 'HProb)
    -> abt 'HProb
summate = undefined
{-
summate lo hi f = do
    x <- freshVar
    return $ Summate_ (syn lo) (syn hi) (open x $ f (var x sing))
-}


-- instance (ABT abt) => Lambda abt where
-- 'app' already defined

lam :: (ABT abt) => (abt a -> abt b) -> abt ('HFun a b)
lam = undefined
{-
lam f = do
    x <- freshVar
    return $ Lam_ Proxy (open x (f (var x sing)))
-}

let_ :: (ABT abt) => abt a -> (abt a -> abt b) -> abt b
let_ = undefined
{-
let_ e f = 
    x <- freshVar
    return $ Let_ (syn e) (open x (f (var x sing)))
-}

-- instance (ABT abt) => Lub abt where
lub :: (ABT abt) => abt a -> abt a -> abt a
lub = (syn .) . Lub_

bot :: (ABT abt) => abt a
bot = syn Bot_
