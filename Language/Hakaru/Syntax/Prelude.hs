-- TODO: <https://git-scm.com/book/en/v2/Git-Branching-Basic-Branching-and-Merging>
{-# LANGUAGE KindSignatures
           , DataKinds
           , TypeFamilies
           , GADTs
           , FlexibleInstances
           , NoImplicitPrelude
           #-}

module Language.Hakaru.Syntax.Prelude where

-- import Prelude hiding (id, (.), Ord(..), Num(..), Integral(..), Fractional(..), Floating(..), Real(..), RealFrac(..), RealFloat(..), (^), (^^),.......)
import Prelude (Maybe(..), Either(..), Bool(..), Int, Double, Functor(..), flip, ($), undefined)
import qualified Prelude
import           Data.Sequence (Seq)
import qualified Data.Sequence as Seq
import           Data.Proxy
import           Control.Category (Category(..))
import           Data.Number.LogFloat (LogFloat)

import Language.Hakaru.Syntax.Nat
import Language.Hakaru.Syntax.DataKind
import Language.Hakaru.Syntax.AST
import Language.Hakaru.Syntax.ABT

----------------------------------------------------------------
{-
Below we implement a lot of simple optimizations; however, these
optimizations only apply if the client uses the type class methods
to produce the AST. We should implement a stand-alone function which
performs these sorts of optimizations, as a program transformation.
-}

app :: (ABT abt) => AST abt ('HFun a b) -> AST abt a -> AST abt b
app f x = App_ (syn f) (syn x)

app2 :: (ABT abt) => AST abt ('HFun a ('HFun b c)) -> AST abt a -> AST abt b -> AST abt c
app2 f x y = app (app f x) y

primOp1_ :: (ABT abt) => PrimOp ('HFun a b) -> AST abt a -> AST abt b
primOp1_ = app . PrimOp_

primOp2_ :: (ABT abt) => PrimOp ('HFun a ('HFun b c)) -> AST abt a -> AST abt b -> AST abt c
primOp2_ = app2 . PrimOp_

naryOp_ :: (ABT abt) => NaryOp a -> AST abt a -> AST abt a -> AST abt a
naryOp_ o x y =
    case (matchNaryOp o x, matchNaryOp o y) of
    (Just xs, Just ys) -> NaryOp_ o (xs    Seq.>< ys)
    (Just xs, Nothing) -> NaryOp_ o (xs    Seq.|> syn y)
    (Nothing, Just ys) -> NaryOp_ o (syn x Seq.<| ys)
    (Nothing, Nothing) -> NaryOp_ o (syn x Seq.<| Seq.singleton (syn y))
    where
    matchNaryOp :: NaryOp a -> AST abt a -> Maybe (Seq (abt a))
    matchNaryOp o (NaryOp_ o' xs) | o Prelude.== o' = Just xs
    matchNaryOp _ _                                 = Nothing

coerceTo_ :: (ABT abt) => Coercion a b -> AST abt a -> AST abt b
coerceTo_ c = CoerceTo_ c . syn

unsafeFrom_ :: (ABT abt) => Coercion a b -> AST abt b -> AST abt a
unsafeFrom_ c = UnsafeFrom_ c . syn

bool_ :: Bool     -> AST abt 'HBool
bool_ = Value_ . Bool_
nat_  :: Nat      -> AST abt 'HNat
nat_  = Value_ . Nat_
int_  :: Int      -> AST abt 'HInt
int_  = Value_ . Int_
prob_ :: LogFloat -> AST abt 'HProb
prob_ = Value_ . Prob_
real_ :: Double   -> AST abt 'HReal
real_ = Value_ . Real_

-- Boolean operators
true, false :: AST abt 'HBool
true  = bool_ True
false = bool_ False

not :: (ABT abt) => AST abt 'HBool -> AST abt 'HBool
not = primOp1_ Not


(&&), (||),
    -- (</=>), (<==>), (==>), (<==), (\\), (//)
    nand, nor
    :: (ABT abt) => AST abt 'HBool -> AST abt 'HBool -> AST abt 'HBool
(&&) = naryOp_ And
(||) = naryOp_ Or
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
    :: (ABT abt, HOrder a) => AST abt a -> AST abt a -> AST abt 'HBool
(==) = primOp2_ Equal
(/=) = (not .) . (==)

(<), (<=), (>), (>=)
    :: (ABT abt, HOrder a) => AST abt a -> AST abt a -> AST abt 'HBool
(<)    = primOp2_ Less
x <= y = (x < y) || (x == y)
(>)    = flip (<)
(>=)   = flip (<=)

min, max
    :: (ABT abt, HOrder a) => AST abt a -> AST abt a -> AST abt a
min = naryOp_ Min
max = naryOp_ Max

-- N.B., we don't take advantage of commutativity, for more predictable AST outputs. However, that means we can end up being really slow;
-- N.B., we also don't try to eliminate the identity elements or do cancellations because (a) it's undecidable in general, and (b) that's prolly better handled as a post-processing simplification step

-- HSemiring operators
(+), (*)
    :: (ABT abt, HSemiring a) => AST abt a -> AST abt a -> AST abt a
(+) = naryOp_ Sum
(*) = naryOp_ Prod

-- TODO: simplifications
(^) :: (ABT abt, HSemiring a) => AST abt a -> AST abt 'HNat -> AST abt a
(^) = primOp2_ (NatPow {- at type @a@ -})


-- HRing operators
(-) :: (ABT abt, HRing a) => AST abt a -> AST abt a -> AST abt a
x - y = naryOp_ Sum x (negate y)

-- BUG: can't just pattern match on (App_ (PrimOp_ Negate) e) anymore; can't even match on (App_ (Syn (PrimOp_ Negate)) e). We need to implement our AST-pattern matching stuff in order to clean this up...
negate :: (ABT abt, HRing a) => AST abt a -> AST abt a
negate (NaryOp_ Sum xs) = NaryOp_ Sum (fmap negate_ABT xs)
negate t0@(App_ f e) =
    case unVarSyn f of
    Left _ -> primOp1_ Negate t0 -- Var falls through to the default case...
    Right (PrimOp_ Negate) ->
        case unVarSyn e of
        Left (x,p) -> undefined (Var x p) -- BUG: we want to just return the variable, but it's not AST...
        Right t    -> t
negate t = primOp1_ Negate t

negate_ABT :: (ABT abt, HRing a) => abt a -> abt a
negate_ABT e =
    case unVarSyn e of
    Left  _ -> syn $ App_ (syn $ PrimOp_ Negate) e
    Right t -> syn $ negate t
    

abs :: (ABT abt, HRing a) => AST abt a -> AST abt a
abs = coerceTo_ signed . abs_

abs_ :: (ABT abt, HRing a) => AST abt a -> AST abt (NonNegative a)
-- abs_ (CoerceTo_ (ConsCoercion Signed IdCoercion) e) = e -- BUG: we want to just return the @e@, but it's not AST...
abs_ = primOp1_ Abs

-- TODO: any obvious simplifications? idempotent?
signum :: (ABT abt, HRing a) => AST abt a -> AST abt a
signum = primOp1_ Signum


-- HFractional operators
(/) :: (ABT abt, HFractional a) => AST abt a -> AST abt a -> AST abt a
x / y = naryOp_ Prod x (recip y)

-- TODO: generalize this pattern so we don't have to repeat it...
recip :: (ABT abt, HFractional a) => AST abt a -> AST abt a
recip (NaryOp_ Prod xs) = NaryOp_ Prod (fmap recip_ABT xs)
recip t0@(App_ f e) =
    case unVarSyn f of
    Left _ -> primOp1_ Recip t0 -- Var falls through to the default case...
    Right (PrimOp_ Recip) ->
        case unVarSyn e of
        Left (x,p) -> undefined (Var x p) -- BUG: we want to just return the variable, but it's not AST...
        Right t    -> t
recip t = primOp1_ Recip t

recip_ABT :: (ABT abt, HFractional a) => abt a -> abt a
recip_ABT e =
    case unVarSyn e of
    Left  _ -> syn $ App_ (syn $ PrimOp_ Recip) e
    Right t -> syn $ recip t


-- TODO: simplifications
(^^) :: (ABT abt, HFractional a) => AST abt a -> AST abt 'HInt -> AST abt a
x ^^ y =
    if_ (y < int_ 0)
        (recip x ^ abs_ y)
        (x ^ abs_ y)


-- HRadical operators
-- TODO: simplifications
thRootOf :: (ABT abt, HRadical a) => AST abt 'HNat -> AST abt a -> AST abt a
n `thRootOf` x = primOp2_ NatRoot x n

sqrt :: (ABT abt, HRadical a) => AST abt a -> AST abt a
sqrt = (nat_ 2 `thRootOf`)

{-
-- TODO: simplify
(^+) :: (ABT abt, HRadical a) => AST abt a -> AST abt 'HPositiveRational -> AST abt a
x ^+ y = casePositiveRational y $ \n d -> d `thRootOf` (x ^ n)

(^*) :: (ABT abt, HRadical a) => AST abt a -> AST abt 'HRational -> AST abt a
x ^* y = caseRational y $ \n d -> d `thRootOf` (x ^^ n)
-}


class RealProb (a :: Hakaru *) where
    (**) :: (ABT abt) => AST abt 'HProb -> AST abt a -> AST abt 'HProb
    exp  :: (ABT abt) => AST abt a -> AST abt 'HProb
    log  :: (ABT abt) => AST abt 'HProb -> AST abt a -- HACK
    erf  :: (ABT abt) => AST abt a -> AST abt a
    pi   :: (ABT abt) => AST abt a
    infinity :: (ABT abt) => AST abt a

instance RealProb 'HReal where
    (**)     = primOp2_ RealPow
    exp      = primOp1_ Exp
    log      = primOp1_ Log
    erf      = primOp1_ (Erf {- 'HReal -})
    pi       = coerceTo_ signed $ PrimOp_ Pi
    infinity = coerceTo_ signed $ PrimOp_ Infinity

instance RealProb 'HProb where
    x ** y   = primOp2_ RealPow x (coerceTo_ signed y)
    exp      = primOp1_ Exp . coerceTo_ signed
    log      = unsafeFrom_ signed . primOp1_ Log -- error for inputs in [0,1)
    erf      = primOp1_ (Erf {- 'HProb -})
    pi       = PrimOp_ Pi
    infinity = PrimOp_ Infinity

logBase
    :: (ABT abt, RealProb a, HFractional a)
    => AST abt 'HProb
    -> AST abt 'HProb
    -> AST abt a
logBase b x = log x / log b -- undefined when b == 1

sin, cos, tan, asin, acos, atan, sinh, cosh, tanh, asinh, acosh, atanh
    :: (ABT abt) => AST abt 'HReal -> AST abt 'HReal
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


-- instance (ABT abt) => Base (AST abt) where not already defined above
unit :: AST abt 'HUnit
unit = Unit_

pair :: (ABT abt) => AST abt a -> AST abt b -> AST abt ('HPair a b)
pair x y = Pair_ (syn x) (syn y)

unpair
    :: (ABT abt)
    => AST abt ('HPair a b)
    -> (AST abt a -> AST abt b -> AST abt c)
    -> AST abt c
unpair = undefined
{-
unpair e f = do
    x <- freshVar
    y <- freshVar
    return $ Case_ (syn e)
        [(PPair PVar PVar,
            open x (open y (syn $ f (var x Proxy) (var y Proxy)))]
-}

inl :: (ABT abt) => AST abt a -> AST abt ('HEither a b)
inl = Inl_ . syn

inr :: (ABT abt) => AST abt b -> AST abt ('HEither a b)
inr = Inr_ . syn

uneither
    :: (ABT abt)
    => AST abt ('HEither a b)
    -> (AST abt a -> AST abt c)
    -> (AST abt b -> AST abt c)
    -> AST abt c
uneither = undefined
{-
uneither e l r = do
    x <- freshVar
    return $ Case_ (syn e)
        [ (PInl PVar, open x (syn $ l (var x Proxy)))
        , (PInr PVar, open x (syn $ r (var x Proxy)))
        ]
-}

if_ :: (ABT abt) => AST abt 'HBool -> AST abt a -> AST abt a -> AST abt a
if_ b t f = Case_ (syn b) [(PTrue, syn t), (PFalse, syn f)]

unsafeProb :: (ABT abt) => AST abt 'HReal -> AST abt 'HProb
unsafeProb = unsafeFrom_ signed

fromProb   :: (ABT abt) => AST abt 'HProb -> AST abt 'HReal
fromProb   = coerceTo_ signed

fromInt    :: (ABT abt) => AST abt 'HInt  -> AST abt 'HReal
fromInt    = coerceTo_ continuous

negativeInfinity :: AST abt 'HReal
negativeInfinity = PrimOp_ NegativeInfinity

gammaFunc :: (ABT abt) => AST abt 'HReal -> AST abt 'HProb
gammaFunc = primOp1_ GammaFunc

betaFunc :: (ABT abt) => AST abt 'HProb -> AST abt 'HProb -> AST abt 'HProb
betaFunc = primOp2_ BetaFunc

fix :: (ABT abt) => (AST abt a -> AST abt a) -> AST abt a
fix = undefined
{-
fix f = do
    x <- freshVar
    return $ Fix_ (open x (f (Var x Proxy)))
-}

-- TODO: rename @array@
vector
    :: (ABT abt)
    => AST abt 'HInt
    -> (AST abt 'HInt -> AST abt a)
    -> AST abt ('HArray a)
vector = undefined
{-
vector n f = do
    x <- freshVar
    return $ Array_ (syn $ unsafeFrom_ signed n) (open x (f (Var x Proxy)))
-}

empty :: AST abt ('HArray a)
empty = Empty_

-- TODO: rename @(!)@
index :: (ABT abt) => AST abt ('HArray a) -> AST abt 'HInt -> AST abt a
index xs i = Index_ (syn xs) (syn $ unsafeFrom_ signed i)

size :: (ABT abt) => AST abt ('HArray a) -> AST abt 'HInt
size = coerceTo_ signed . Size_ . syn

reduce
    :: (ABT abt)
    => (AST abt a -> AST abt a -> AST abt a)
    -> AST abt a
    -> AST abt ('HArray a)
    -> AST abt a
reduce f z xs = do
    Reduce_ (syn (lam $ \x -> lam $ \y -> f x y)) (syn z) (syn xs)


-- instance (ABT abt) => Mochastic (AST abt) where
dirac       = primOp1_ Dirac
bind        = Bind_
lebesgue    = PrimOp_  Lebesgue
counting    = PrimOp_  Counting
superpose   = Superpose_
categorical = PrimOp_  Categorical
uniform     = primOp2_ Uniform
normal      = primOp2_ Normal
poisson     = primOp1_ Poisson
gamma       = primOp2_ Gamma
beta        = primOp2_ Beta
dp          = Dp_
plate       = Plate_
chain       = Chain_

-- instance (ABT abt) => Integrate (AST abt) where
integrate
    :: (ABT abt)
    => AST abt 'HReal
    -> AST abt 'HReal
    -> (AST abt 'HReal -> AST abt 'HProb)
    -> AST abt 'HProb
integrate = undefined
{-
integrate lo hi f = do
    x <- freshVar
    return $ Integrate_ (syn lo) (syn hi) (open x $ f (Var x Proxy))
-}

summate
    :: (ABT abt)
    => AST abt 'HReal
    -> AST abt 'HReal
    -> (AST abt 'HInt -> AST abt 'HProb)
    -> AST abt 'HProb
summate = undefined
{-
summate lo hi f = do
    x <- freshVar
    return $ Summate_ (syn lo) (syn hi) (open x $ f (Var x Proxy))
-}


-- instance (ABT abt) => Lambda (AST abt) where
-- 'app' already defined

lam :: (ABT abt) => (AST abt a -> AST abt b) -> AST abt ('HFun a b)
lam = undefined
{-
lam f = do
    x <- freshVar
    return $ Lam_ Proxy (open x (f (Var x Proxy)))
-}

let_ :: (ABT abt) => AST abt a -> (AST abt a -> AST abt b) -> AST abt b
let_ = undefined
{-
let_ e f = 
    x <- freshVar
    return $ Let_ (syn e) (open x (f (Var x Proxy)))
-}

-- instance (ABT abt) => Lub (AST abt) where
lub x y = Lub_ (syn x) (syn y)
bot = Bot_
