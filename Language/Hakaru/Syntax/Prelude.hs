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
-- Boolean operators
true, false :: AST 'HBool
true  = Constant_ (Bool_ True)
false = Constant_ (Bool_ False)

not :: AST 'HBool -> AST 'HBool
not = Not_

(&&)     :: AST 'HBool -> AST 'HBool -> AST 'HBool
(&&)     = BoolOp_ And
(||)     :: AST 'HBool -> AST 'HBool -> AST 'HBool
(||)     = BoolOp_ Or
-- (/=)  :: AST 'HBool -> AST 'HBool -> AST 'HBool
-- (/=)  = BoolOp_ Xor
-- (==)  :: AST 'HBool -> AST 'HBool -> AST 'HBool
-- (==)  = BoolOp_ Iff
-- (==>) :: AST 'HBool -> AST 'HBool -> AST 'HBool
-- (==>) = BoolOp_ Impl
-- (<==) :: AST 'HBool -> AST 'HBool -> AST 'HBool
-- (<==) = flip (==>)
-- (\\) :: AST 'HBool -> AST 'HBool -> AST 'HBool
-- (\\) = BoolOp_ Diff
-- (//) :: AST 'HBool -> AST 'HBool -> AST 'HBool
-- (//) = flip (\\)
-- nand :: AST 'HBool -> AST 'HBool -> AST 'HBool
-- nand = BoolOp_ Nand
-- nor :: AST 'HBool -> AST 'HBool -> AST 'HBool
-- nor = BoolOp_ Nor


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
Sum_ xs  + Sum_ ys  = Sum_ (xs ++ ys)
Sum_ xs  + y        = Sum_ (xs ++ [y])
x        + Sum_ ys  = Sum_ (x : ys)
x        + y        = Sum_ [x,y]
    
(*) :: HSemiring a => AST a -> AST a -> AST a
Prod_ xs * Prod_ ys = Prod_ (xs ++ ys)
Prod_ xs * y        = Prod_ (xs ++ [y])
x        * Prod_ ys = Prod_ (x : ys)
x        * y        = Prod_ [x,y]

-- TODO: simplify
(^) :: (HSemiring a) => AST a -> AST 'HNat -> AST a
(^) = NatPow_


-- HRing operators
(-) :: (HRing a) => AST a -> AST a -> AST a
Sum_ xs  - Sum_ ys  = Sum_ (xs ++ map negate ys)
Sum_ xs  - y        = Sum_ (xs ++ [negate y])
x        - Sum_ ys  = Sum_ (x : map negate ys)
x        - y        = Sum_ [x, negate y]
    
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
Prod_ xs / Prod_ ys = Prod_ (xs ++ map recip ys)
Prod_ xs / y        = Prod_ (xs ++ [recip y])
x        / Prod_ ys = Prod_ (x : map recip ys)
x        / y        = Prod_ [x, recip y]

recip :: (HFractional a) => AST a -> AST a
recip (Recip_ x) = x
recip x          = Recip_ x

-- TODO: simplify
(^^) :: (HFractional a) => AST a -> AST 'HInt -> AST a
x ^^ y =
    If_ (y < Constant_ (Int_ 0))
        (recip x ^ abs_ y)
        (x ^ abs_ y)


-- HRadical operators
sqrt :: (HRadical a) => AST a -> AST a
sqrt x = NatRoot_ x (Constant_ (Nat_ 2))

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
    (**)     = RealPow_
    exp      = Exp_
    log      = Log_
    erf      = Erf_ -- monomorphic at 'HReal
    pi       = CoerceTo_ signed Pi_
    infinity = CoerceTo_ signed Infinity_
    
instance RealProb 'HProb where
    x ** y   = RealPow_ x (CoerceTo_ signed y)
    exp x    = Exp_ (CoerceTo_ signed x)
    log x    = UnsafeFrom_ signed (Log_ x) -- error for inputs in [0,1)
    erf      = Erf_ -- monomorphic at 'HProb
    pi       = Pi_
    infinity = Infinity_

logBase :: RealProb a => AST a -> AST a -> AST a
logBase b x = log x / log b -- undefined when b == 1

sin, cos, tan, asin, acos, atan, sinh, cosh, tanh, asinh, acosh, atanh
    :: AST 'HReal -> AST 'HReal
sin    = TrigOp_ Sin
cos    = TrigOp_ Cos
tan    = TrigOp_ Tan
asin   = TrigOp_ Asin
acos   = TrigOp_ Acos
atan   = TrigOp_ Atan
sinh   = TrigOp_ Sinh
cosh   = TrigOp_ Cosh
tanh   = TrigOp_ Tanh
asinh  = TrigOp_ Asinh
acosh  = TrigOp_ Acosh
atanh  = TrigOp_ Atanh


dirac       = Measure_ Dirac
lebesgue    = Measure_ Lebesgue
counting    = Measure_ Counting
superpose   = Measure_ Superpose
categorical = Measure_ Categorical
uniform     = Measure_ Uniform
normal      = Measure_ Normal
poisson     = Measure_ Poisson
gamma       = Measure_ Gamma
beta        = Measure_ Beta
