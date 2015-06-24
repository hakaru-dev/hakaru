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
import Control.Category (Category(..))
import Data.Number.LogFloat (LogFloat)
import Language.Hakaru.Syntax.DataKind
import Language.Hakaru.Syntax.Nat

----------------------------------------------------------------

app2 :: AST ('HFun a ('HFun b c)) -> AST a -> AST b -> AST c
app2 f x y = App (App f x) y

primOp1_ :: PrimOp ('HFun a b) -> AST a -> AST b
primOp1_ = App . PrimOp_
primOp2_ :: PrimOp ('HFun a ('HFun b c)) -> AST a -> AST b -> AST c
primOp2_ = app2 . PrimOp_

naryOp_ :: NaryOp a -> AST a -> AST a -> AST a
naryOp_ o x y =
    case (match o x, match o y) of
    (Just xs, Just ys) -> NaryOp_ o (xs Seq.>< ys)
    (Just xs, Nothing) -> NaryOp_ o (xs Seq.|> y)
    (Nothing, Just ys) -> NaryOp_ o (x  Seq.<| ys)
    (Nothing, Nothing) -> NaryOp_ o (x  Seq.<| Seq.singleton y)
    where
    match :: NaryOp a -> AST a -> Maybe (Seq (AST a))
    match o (NaryOp_ o' xs) | o == o' = Just xs
    match _ _                         = Nothing


bool_ :: Bool     -> AST 'HBool
bool_ = Value_ . Bool_
nat_  :: Nat      -> AST 'HNat
nat_  = Value_ . Nat_
int_  :: Int      -> AST 'HInt
int_  = Value_ . Int_
prob_ :: LogFloat -> AST 'HProb
prob_ = Value_ . Prob_
real_ :: Double   -> AST 'HReal
real_ = Value_ . Real_

-- Boolean operators
true, false :: AST 'HBool
true  = bool_ True
false = bool_ False

not :: AST 'HBool -> AST 'HBool
not = primOp1_ Not

(&&)     :: AST 'HBool -> AST 'HBool -> AST 'HBool
(&&)     = naryOp_ And
(||)     :: AST 'HBool -> AST 'HBool -> AST 'HBool
(||)     = naryOp_ Or
-- (</=>) :: AST 'HBool -> AST 'HBool -> AST 'HBool
-- (</=>) = primOp2_ Xor
-- (<==>) :: AST 'HBool -> AST 'HBool -> AST 'HBool
-- (<==>) = primOp2_ Iff
-- (==>) :: AST 'HBool -> AST 'HBool -> AST 'HBool
-- (==>) = primOp2_ Impl
-- (<==) :: AST 'HBool -> AST 'HBool -> AST 'HBool
-- (<==) = flip (==>)
-- (\\) :: AST 'HBool -> AST 'HBool -> AST 'HBool
-- (\\) = primOp2_ Diff
-- (//) :: AST 'HBool -> AST 'HBool -> AST 'HBool
-- (//) = flip (\\)
-- nand :: AST 'HBool -> AST 'HBool -> AST 'HBool
-- nand = primOp2_ Nand
-- nor :: AST 'HBool -> AST 'HBool -> AST 'HBool
-- nor = primOp2_ Nor


-- HEq & HOrder operators
(==) :: HOrder a => AST a -> AST a -> AST 'HBool
(==) = primOp2_ Equal
(/=) :: HOrder a => AST a -> AST a -> AST 'HBool
(/=) = (not .) . (==)

(<)    :: HOrder a => AST a -> AST a -> AST 'HBool
(<)    = primOp2_ Less
(<=)   :: HOrder a => AST a -> AST a -> AST 'HBool
x <= y = (x < y) || (x == y)
(>)    :: HOrder a => AST a -> AST a -> AST 'HBool
(>)    = flip (<)
(>=)   :: HOrder a => AST a -> AST a -> AST 'HBool
(>=)   = flip (<=)

min :: HOrder a => AST a -> AST a -> AST a
min = naryOp_ Min
max :: HOrder a => AST a -> AST a -> AST a
max = naryOp_ Max


-- HSemiring operators
(+) :: HSemiring a => AST a -> AST a -> AST a
(+) = naryOp_ Sum
(*) :: HSemiring a => AST a -> AST a -> AST a
(*) = naryOp_ Prod

-- TODO: simplifications
(^) :: (HSemiring a) => AST a -> AST 'HNat -> AST a
(^) = primOp2_ (NatPow {- at type @a@ -})


-- HRing operators
(-) :: (HRing a) => AST a -> AST a -> AST a
x - y = naryOp_ Sum x (negate y)

negate :: (HRing a) => AST a -> AST a
negate (NaryOp_ Sum xs)         = NaryOp_ Sum (fmap negate xs)
negate (App (PrimOp_ Negate) x) = x
negate x                        = App (PrimOp_ Negate) x

abs :: (HRing a) => AST a -> AST a
abs = CoerceTo_ signed . abs_

abs_ :: (HRing a) => AST a -> AST (NonNegative a)
abs_ (CoerceTo_ (ConsCoercion Signed IdCoercion) x) = x
abs_ x = primOp1_ Abs x

-- TODO: any obvious simplifications? idempotent?
signum :: (HRing a) => AST a -> AST a
signum = primOp1_ Signum


-- HFractional operators
(/) :: HFractional a => AST a -> AST a -> AST a
x / y = naryOp_ Prod x (recip y)

recip :: (HFractional a) => AST a -> AST a
recip (NaryOp_ Prod xs)       = NaryOp_ Prod (fmap recip xs)
recip (App (PrimOp_ Recip) x) = x
recip x                       = App (PrimOp_ Recip) x

-- TODO: simplifications
(^^) :: (HFractional a) => AST a -> AST 'HInt -> AST a
x ^^ y =
    if_ (y < int_ 0)
        (recip x ^ abs_ y)
        (x ^ abs_ y)

if_ :: AST 'HBool -> AST a -> AST a -> AST a
if_ b t f = Case_ (syn b) [(PTrue, syn t), (PFalse, syn f)]


-- HRadical operators
-- TODO: simplifications
thRootOf :: (HRadical a) => AST 'HNat -> AST a -> AST a
n `thRootOf` x = primOp2_ NatRoot x n

sqrt :: (HRadical a) => AST a -> AST a
sqrt = (nat_ 2 `thRootOf`)

{-
-- TODO: simplify
(^+) :: (HRadical a) => AST a -> AST 'HPositiveRational -> AST a
x ^+ y = casePositiveRational y $ \n d -> d `thRootOf` (x ^ n)

(^*) :: (HRadical a) => AST a -> AST 'HRational -> AST a
x ^* y = caseRational y $ \n d -> d `thRootOf` (x ^^ n)
-}


class RealProb (a :: Hakaru *) where
    (**) :: AST 'HProb -> AST a -> AST 'HProb
    exp  :: AST a -> AST 'HProb
    log  :: AST 'HProb -> AST a -- HACK
    erf  :: AST a -> AST a
    pi   :: AST a
    infinity :: AST a

instance RealProb 'HReal where
    (**)     = primOp2_ RealPow
    exp      = primOp1_ Exp
    log      = primOp1_ Log
    erf      = primOp1_ (Erf {- 'HReal -})
    pi       = CoerceTo_ signed $ PrimOp_ Pi
    infinity = CoerceTo_ signed $ PrimOp_ Infinity

instance RealProb 'HProb where
    x ** y   = primOp2_ RealPow x (CoerceTo_ signed y)
    exp      = primOp1_ Exp . CoerceTo_ signed
    log      = UnsafeFrom_ signed . primOp1_ Log -- error for inputs in [0,1)
    erf      = primOp1_ (Erf {- 'HProb -})
    pi       = PrimOp_ Pi
    infinity = PrimOp_ Infinity

logBase :: RealProb a => AST a -> AST a -> AST a
logBase b x = log x / log b -- undefined when b == 1

sin, cos, tan, asin, acos, atan, sinh, cosh, tanh, asinh, acosh, atanh
    :: AST 'HReal -> AST 'HReal
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

-- instance Mochastic AST where
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

-- instance Integrate AST where
integrate = Integrate_
summate   = Summate_

-- instance Lambda AST where
app      = App_
lam f    = let x = ... in Lam_ Proxy   (open x (f (Var x Proxy)))
let_ e f = let x = ... in Let_ (syn e) (open x (f (Var x Proxy)))

-- instance Lub AST where
lub = Lub_
bot = Bot_
