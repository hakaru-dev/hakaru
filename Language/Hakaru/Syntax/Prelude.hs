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
(&&)     = primOp2_ And
(||)     :: AST 'HBool -> AST 'HBool -> AST 'HBool
(||)     = primOp2_ Or
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


-- HOrder operators
(==)   :: HOrder a => AST a -> AST a -> AST 'HBool
(==)   = Equal_
(/=)   :: HOrder a => AST a -> AST a -> AST 'HBool
x /= y = not (x == y)

(<)    :: HOrder a => AST a -> AST a -> AST 'HBool
(<)    = Less_
(<=)   :: HOrder a => AST a -> AST a -> AST 'HBool
x <= y = (x < y) || (x == y)
(>)    :: HOrder a => AST a -> AST a -> AST 'HBool
(>)    = flip Less_
(>=)   :: HOrder a => AST a -> AST a -> AST 'HBool
(>=)   = flip (<=)


-- HSemiring operators
(+) :: HSemiring a => AST a -> AST a -> AST a
Sum_ xs  + Sum_ ys  = Sum_ (xs Seq.>< ys)
Sum_ xs  + y        = Sum_ (xs Seq.|> y)
x        + Sum_ ys  = Sum_ (x  Seq.<| ys)
x        + y        = Sum_ (x  Seq.<| Seq.singleton y)
    
(*) :: HSemiring a => AST a -> AST a -> AST a
Prod_ xs * Prod_ ys = Prod_ (xs Seq.>< ys)
Prod_ xs * y        = Prod_ (xs Seq.|> y)
x        * Prod_ ys = Prod_ (x  Seq.<| ys)
x        * y        = Prod_ (x  Seq.<| Seq.singleton y)

-- TODO: simplify
(^) :: (HSemiring a) => AST a -> AST 'HNat -> AST a
(^) = NatPow_


-- HRing operators
(-) :: (HRing a) => AST a -> AST a -> AST a
Sum_ xs  - Sum_ ys  = Sum_ (xs Seq.>< map negate ys)
Sum_ xs  - y        = Sum_ (xs Seq.|> negate y)
x        - Sum_ ys  = Sum_ (x  Seq.<| map negate ys)
x        - y        = Sum_ (x  Seq.<| Seq.singleton (negate y))
    
negate :: (HRing a) => AST a -> AST a
negate (Negate_ x)  = x
negate x            = Negate_ x

abs :: (HRing a) => AST a -> AST a
abs = CoerceTo_ signed . abs_

abs_ :: (HRing a) => AST a -> AST (NonNegative a)
abs_ (CoerceTo_ (ConsCoercion Signed IdCoercion) x) = x
abs_ x = Abs_ x
    
-- TODO: any obvious simplifications? idempotent?
signum :: (HRing a) => AST a -> AST a
signum = Signum_


-- HFractional operators
(/) :: HFractional a => AST a -> AST a -> AST a
Prod_ xs / Prod_ ys = Prod_ (xs Seq.>< map recip ys)
Prod_ xs / y        = Prod_ (xs Seq.|> recip y)
x        / Prod_ ys = Prod_ (x  Seq.<| map recip ys)
x        / y        = Prod_ (x  Seq.<| Seq.singleton (recip y))

recip :: (HFractional a) => AST a -> AST a
recip (Recip_ x) = x
recip x          = Recip_ x

-- TODO: simplify
(^^) :: (HFractional a) => AST a -> AST 'HInt -> AST a
x ^^ y =
    if_ (y < int_ 0)
        (recip x ^ abs_ y)
        (x ^ abs_ y)

if_ b t f = Case_ (syn b) [(PTrue, syn t), (PFalse, syn f)]

-- HRadical operators
sqrt :: (HRadical a) => AST a -> AST a
sqrt x = NatRoot_ x (nat_ 2)

{-
-- TODO: simplify
(^+) :: (HRadical a) => AST a -> AST 'HPositiveRational -> AST a
x ^+ y = casePositiveRational y $ \n d -> NatRoot_ (x ^ n) d

(^*) :: (HRadical a) => AST a -> AST 'HRational -> AST a
x ^* y = caseRational y $ \n d -> NatRoot_ (x ^^ n) d
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
    erf      = Erf_ -- monomorphic at 'HReal
    pi       = CoerceTo_ signed $ PrimOp_ Pi
    infinity = CoerceTo_ signed $ PrimOp_ Infinity
    
instance RealProb 'HProb where
    x ** y   = primOp2_ RealPow x (CoerceTo_ signed y)
    exp      = primOp1_ Exp . CoerceTo_ signed
    log      = UnsafeFrom_ signed . primOp1_ Log -- error for inputs in [0,1)
    erf      = Erf_ -- monomorphic at 'HProb
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
dirac       = Measure_ . Dirac
bind        = Bind_
lebesgue    = Measure_ Lebesgue
counting    = Measure_ Counting
superpose   = Measure_ . Superpose
categorical = Measure_ Categorical
uniform     = (Measure_ .) . Uniform
normal      = (Measure_ .) . Normal
poisson     = Measure_ . Poisson
gamma       = (Measure_ .) . Gamma
beta        = (Measure_ .) . Beta
dp          = Dp_
plate       = Plate_
chain       = Chain_