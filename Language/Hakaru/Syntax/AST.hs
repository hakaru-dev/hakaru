-- TODO: <https://git-scm.com/book/en/v2/Git-Branching-Basic-Branching-and-Merging>
{-# LANGUAGE KindSignatures
           , DataKinds
           , TypeFamilies
           , GADTs
           , FlexibleInstances
           , StandaloneDeriving
           #-}

{-# OPTIONS_GHC -Wall -fwarn-tabs #-}
----------------------------------------------------------------
--                                                    2015.06.24
-- |
-- Module      :  Language.Hakaru.Syntax.AST
-- Copyright   :  Copyright (c) 2015 the Hakaru team
-- License     :  BSD3
-- Maintainer  :  wren@community.haskell.org
-- Stability   :  experimental
-- Portability :  GHC-only
--
-- The generating functor for the raw syntax, along with various
-- helper types.
----------------------------------------------------------------
module Language.Hakaru.Syntax.AST where

import Prelude hiding (id, (.), Ord(..), Num(..), Integral(..), Fractional(..), Floating(..), Real(..), RealFrac(..), RealFloat(..), (^), (^^))
import Data.Sequence        (Seq)
import Data.Proxy
import Control.Category     (Category(..))
import Data.Number.LogFloat (LogFloat)
import Language.Hakaru.Syntax.DataKind
import Language.Hakaru.Syntax.Nat
{-
import Language.Hakaru.Lazy (Backward, runDisintegrate, density)
import Language.Hakaru.Expect (Expect')
import Language.Hakaru.Simplify (simplify)
import Language.Hakaru.Any (Any)
import Language.Hakaru.Sample
-}

----------------------------------------------------------------
{- TODO: break the HEq class out from HOrder
-- TODO: allow lifting of equality to work on HPair, HEither,...?
class HEq (a :: Hakaru *)
instance HEq 'HBool
instance HEq 'HNat
instance HEq 'HInt
instance HEq 'HProb
instance HEq 'HReal
-}

-- TODO: class HPER (a :: Hakaru *) -- ?
-- TODO: class HPartialOrder (a :: Hakaru *)

{-
-- TODO: replace the open type class with a closed equivalent, e.g.:
data HOrder :: Hakaru * -> * where
    HOrder_HNat  :: HOrder 'HNat
    HOrder_HInt  :: HOrder 'HInt
    HOrder_HProb :: HOrder 'HProb
    HOrder_HReal :: HOrder 'HReal
-- The problem is, how to we handle things like the HRing type class?
-}
class    HOrder (a :: Hakaru *)
instance HOrder 'HNat
instance HOrder 'HInt
instance HOrder 'HProb
instance HOrder 'HReal


-- N.B., even though these ones are commutative, we don't assume that!
class    HSemiring (a :: Hakaru *)
instance HSemiring 'HNat
instance HSemiring 'HInt
instance HSemiring 'HProb
instance HSemiring 'HReal


-- N.B., even though these ones are commutative, we don't assume that!
-- N.B., the NonNegative associated type is (a) actually the semiring
-- that generates this ring, but (b) is also used for the result
-- of calling the absolute value. For Int and Real that's fine; but
-- for Complex and Vector these two notions diverge
-- TODO: Can we specify that the @HSemiring (NonNegative a)@
-- constraint coincides with the @HSemiring a@ constraint on the
-- appropriate subset of @a@? Or should that just be assumed...?
class (HSemiring (NonNegative a), HSemiring a)
    => HRing (a :: Hakaru *) where type NonNegative a :: Hakaru *
instance HRing 'HInt  where type NonNegative 'HInt  = 'HNat 
instance HRing 'HReal where type NonNegative 'HReal = 'HProb 

{-
data HRing_ :: Hakaru * -> * where
    HRing_Int  :: HRing_ 'HInt
    HRing_Real :: HRing_ 'HReal

type family   NonNegative (a :: Hakaru *) :: Hakaru *
type instance NonNegative 'HInt  = 'HNat 
type instance NonNegative 'HReal = 'HProb 

data HRing :: Hakaru * -> * where
    HRing
        :: !(HRing_ a)
        -> !(HSemiring a)
        -> !(HSemiring (NonNegative a))
        -> HRing a
-}


-- N.B., We're assuming two-sided inverses here. That doesn't entail
-- commutativity, though it does strongly suggest it... (cf.,
-- Wedderburn's little theorem)
-- N.B., the (Nat,"+"=lcm,"*"=gcd) semiring is sometimes called "the division semiring"
-- HACK: tracking carriers here wouldn't be quite right b/c we get
-- more than just the (non-negative)rationals generated from
-- HNat/HInt! However, we should have some sort of associated type
-- so we can add rationals and non-negative rationals...
-- | A division-semiring. (Not quite a field nor quite a division-ring...)
class (HSemiring a) => HFractional (a :: Hakaru *)
instance HFractional 'HProb
instance HFractional 'HReal

-- type HDivisionRing a = (HFractional a, HRing a)
-- type HField a = (HDivisionRing a, HCommutativeSemiring a)


-- Numbers formed by finitely many uses of integer addition,
-- subtraction, multiplication, division, and nat-roots are all
-- algebraic; however, N.B., not all algebraic numbers can be formed
-- this way (cf., Abel–Ruffini theorem)
-- TODO: ought we require HRing or HFractional rather than HSemiring?
-- TODO: any special associated type?
-- N.B., we /assume/ closure under the semiring operations, thus
-- we get things like @sqrt 2 + sqrt 3@ which cannot be expressed
-- as a single root. Thus, solving the HRadical class means we need
-- solutions to more general polynomials (than just @x^n - a@) in
-- order to express the results as roots. However, the Galois groups
-- of these are all solvable, so this shouldn't be too bad.
class (HSemiring a) => HRadical (a :: Hakaru *)
instance HRadical 'HProb
instance HRadical 'HReal

-- TODO: class (HDivisionRing a, HRadical a) => HAlgebraic a where...


-- TODO: find a better name than HIntegral
-- TODO: how to require that "if HRing a, then HRing b too"?
class (HSemiring (HIntegral a), HFractional a)
    => HContinuous (a :: Hakaru *) where type HIntegral a :: Hakaru *
instance HContinuous 'HProb where type HIntegral 'HProb = 'HNat 
instance HContinuous 'HReal where type HIntegral 'HReal = 'HInt 



----------------------------------------------------------------
----------------------------------------------------------------
-- TODO: (?) coercing HMeasure by coercing the underlying measure space.

-- | Primitive proofs of the inclusions in our numeric hierarchy.
data PrimCoercion :: Hakaru * -> Hakaru * -> * where
    Signed     :: HRing a       => PrimCoercion (NonNegative a) a
    Continuous :: HContinuous a => PrimCoercion (HIntegral   a) a

deriving instance Eq   (PrimCoercion a b)
-- BUG: deriving instance Read (PrimCoercion a b)
deriving instance Show (PrimCoercion a b)


-- | General proofs of the inclusions in our numeric hierarchy.
data Coercion :: Hakaru * -> Hakaru * -> * where
    -- | Added the trivial coercion so we get the Category instance.
    -- This may/should make program transformations easier to write
    -- by allowing more intermediate ASTs, but will require a cleanup
    -- pass afterwards to remove the trivial coercions.
    IdCoercion :: Coercion a a

    -- TODO: but sometimes we need the snoc-based inductive hypothesis...
    -- | We use a cons-based approach rather than append-based in
    -- order to get a better inductive hypothesis.
    ConsCoercion :: !(PrimCoercion a b) -> !(Coercion b c) -> Coercion a c

-- BUG: deriving instance Eq   (Coercion a b)
-- BUG: deriving instance Read (Coercion a b)
deriving instance Show (Coercion a b)


-- | A smart constructor for 'Signed'.
signed :: HRing a => Coercion (NonNegative a) a
signed = ConsCoercion Signed IdCoercion

-- | A smart constructor for 'Continuous'.
continuous :: HContinuous a => Coercion (HIntegral a) a
continuous = ConsCoercion Continuous IdCoercion

instance Category Coercion where
    id = IdCoercion
    xs . IdCoercion        = xs
    xs . ConsCoercion y ys = ConsCoercion y (xs . ys)

{-
-- TODO: make these rules for coalescing things work
data UnsafeFrom_CoerceTo :: Hakaru * -> Hakaru * -> * where
    UnsafeFrom_CoerceTo
        :: !(Coercion c b)
        -> !(Coercion a b)
        -> UnsafeFrom_CoerceTo a c

unsafeFrom_coerceTo
    :: Coercion c b
    -> Coercion a b
    -> UnsafeFrom_CoerceTo a c
unsafeFrom_coerceTo xs ys =
    case xs of
    IdCoercion          -> UnsafeFrom_CoerceTo IdCoercion ys
    ConsCoercion x xs'  ->
        case ys of
        IdCoercion      -> UnsafeFrom_CoerceTo xs IdCoercion
        ConsCoercion y ys' ->
            -- TODO: use a variant of jmEq instead
            case (x,y) of
            (Signed,    Signed)     -> unsafeFrom_coerceTo xs' ys'
            (Continuous,Continuous) -> unsafeFrom_coerceTo xs' ys'
            _                       -> UnsafeFrom_CoerceTo xs  ys

data CoerceTo_UnsafeFrom :: Hakaru * -> Hakaru * -> * where
    CoerceTo_UnsafeFrom
        :: !(Coercion c b)
        -> !(Coercion a b)
        -> CoerceTo_UnsafeFrom a c

coerceTo_unsafeFrom
    :: Coercion a b
    -> Coercion c b
    -> CoerceTo_UnsafeFrom a c
coerceTo_unsafeFrom xs ys = ...
-}

-- TODO: implement a simplifying pass for pushing/gathering coersions over other things (e.g., Less/Equal)


----------------------------------------------------------------
----------------------------------------------------------------
-- TODO: use 'Integer' instead of 'Int', and 'Natural' instead of 'Nat'.
-- | Constant values for primitive types.
data Value :: Hakaru * -> * where
    Bool_ :: !Bool     -> Value 'HBool
    Nat_  :: !Nat      -> Value 'HNat
    Int_  :: !Int      -> Value 'HInt
    Prob_ :: !LogFloat -> Value 'HProb
    Real_ :: !Double   -> Value 'HReal

    -- TODO: add constructors for constants of datatypes?
    {-
    Nil_     :: Value ('HList a)
    Cons_    :: !(Value a) -> !(Value ('HList a)) -> Value ('HList a)
    Nothing_ :: Value ('HMaybe a)
    Just_    :: !(Value a) -> Value ('HMaybe a)
    Unit_    :: Value 'HUnit
    Pair_    :: !(Value a) -> !(Value b) -> Value ('HPair a b)
    Inl_     :: !(Value a) -> Value ('HEither a b)
    Inr_     :: !(Value b) -> Value ('HEither a b)
    -}


----------------------------------------------------------------
-- TODO: helper functions for splitting NaryOp_ into components to group up like things.

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
data NaryOp :: Hakaru * -> * where
    And  :: NaryOp 'HBool
    Or   :: NaryOp 'HBool

    -- These two don't necessarily have identity elements; thus,
    -- @NaryOp_ Min []@ and @NaryOp_ Max []@ may not be well-defined...
    -- TODO: check for those cases!
    Min  :: (HOrder a) => NaryOp a
    Max  :: (HOrder a) => NaryOp a

    Sum  :: (HSemiring a) => NaryOp a
    Prod :: (HSemiring a) => NaryOp a

    {-
    GCD  :: (GCD_Domain a) => NaryOp a
    LCM  :: (GCD_Domain a) => NaryOp a
    -}

deriving instance Eq   (NaryOp a)
-- BUG: deriving instance Read (NaryOp a)
deriving instance Show (NaryOp a)


----------------------------------------------------------------
-- | Simple primitive functions, constants, and measures.
data PrimOp :: Hakaru * -> * where

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
    Not  :: PrimOp ('HFun 'HBool 'HBool)
    -- And
    -- Or
    Xor  :: PrimOp ('HFun 'HBool ('HFun 'HBool 'HBool)) -- == Not (Iff x y)
    Iff  :: PrimOp ('HFun 'HBool ('HFun 'HBool 'HBool)) -- == Not (Xor x y)
    Impl :: PrimOp ('HFun 'HBool ('HFun 'HBool 'HBool)) -- == Or (Not x) y
    Diff :: PrimOp ('HFun 'HBool ('HFun 'HBool 'HBool)) -- == Not (Impl x y)
    Nand :: PrimOp ('HFun 'HBool ('HFun 'HBool 'HBool)) -- aka Alternative Denial, Sheffer stroke
    Nor  :: PrimOp ('HFun 'HBool ('HFun 'HBool 'HBool)) -- aka Joint Denial, aka Quine dagger, aka Pierce arrow
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
    Pi    :: PrimOp 'HProb
    -- TODO: if we're going to bother naming the hyperbolic ones, why not also name /a?(csc|sec|cot)h?/ eh?
    -- TODO: capture more domain information in these types?
    Sin   :: PrimOp ('HFun 'HReal 'HReal)
    Cos   :: PrimOp ('HFun 'HReal 'HReal)
    Tan   :: PrimOp ('HFun 'HReal 'HReal)
    Asin  :: PrimOp ('HFun 'HReal 'HReal)
    Acos  :: PrimOp ('HFun 'HReal 'HReal)
    Atan  :: PrimOp ('HFun 'HReal 'HReal)
    Sinh  :: PrimOp ('HFun 'HReal 'HReal)
    Cosh  :: PrimOp ('HFun 'HReal 'HReal)
    Tanh  :: PrimOp ('HFun 'HReal 'HReal)
    Asinh :: PrimOp ('HFun 'HReal 'HReal)
    Acosh :: PrimOp ('HFun 'HReal 'HReal)
    Atanh :: PrimOp ('HFun 'HReal 'HReal)


    -- -- Other Real/Prob-valued operators
    -- N.B., we only give the safe/exact versions here. The old
    -- more lenient versions now require explicit coercions. Some
    -- of those coercions are safe, but others are not. This way
    -- we're explicit about where things can fail.
    -- N.B., we also have @NatPow{'HReal} :: 'HReal -> 'HNat -> 'HReal@,
    -- but non-integer real powers of negative reals are not real numbers!
    -- TODO: may need @SafeFrom_@ in order to branch on the input
    -- in order to provide the old unsafe behavior.
    RealPow   :: PrimOp ('HFun 'HProb ('HFun 'HReal 'HProb))
    -- ComplexPow :: PrimOp ('HFun 'HProb ('HFun 'HComplex 'HComplex))
    -- is uniquely well-defined. Though we may want to implement
    -- it via @r**z = ComplexExp (z * RealLog r)@
    -- Defining @HReal -> HComplex -> HComplex@ requires either
    -- multivalued functions, or a choice of complex logarithm and
    -- making it discontinuous.
    Exp       :: PrimOp ('HFun 'HReal 'HProb)
    Log       :: PrimOp ('HFun 'HProb 'HReal)
    Infinity  :: PrimOp 'HProb
    NegativeInfinity :: PrimOp 'HReal -- TODO: maybe replace this by @negate (CoerceTo signed (PrimOp_ Infinity))@ ?
    GammaFunc :: PrimOp ('HFun 'HReal 'HProb)
    BetaFunc  :: PrimOp ('HFun 'HProb ('HFun 'HProb 'HProb))



    -- -- Primitive distributions/measures a~la Mochastic (including the polymorphic 'Dirac')
    -- TODO: should we put Dirac back into the main AST?
    -- TODO: could we move Dp_, Plate_, or Chain_ to here?
    Dirac       :: PrimOp ('HFun a ('HMeasure a))
    Lebesgue    :: PrimOp ('HMeasure 'HReal)
    Counting    :: PrimOp ('HMeasure 'HInt)
    Categorical :: PrimOp ('HFun ('HArray 'HProb) ('HMeasure 'HNat))
    Uniform     :: PrimOp ('HFun 'HReal ('HFun 'HReal ('HMeasure 'HReal)))
    Normal      :: PrimOp ('HFun 'HReal ('HFun 'HProb ('HMeasure 'HReal)))
    Poisson     :: PrimOp ('HFun 'HProb ('HMeasure 'HNat))
    Gamma       :: PrimOp ('HFun 'HProb ('HFun 'HProb ('HMeasure 'HProb)))
    Beta        :: PrimOp ('HFun 'HProb ('HFun 'HProb ('HMeasure 'HProb)))
    -- binomial, mix, geometric, multinomial,... should also be HNat


    -- -- -- Here we have the /polymorphic/ operators
    -- TODO: \"monomorphize\" these by passing explicit dictionary proxies

    -- TODO: do these really belong here (as PrimOps), or in AST?
    -- -- Data constructors (including the monomorphic 'Unit')
    Unit :: PrimOp 'HUnit
    Pair :: PrimOp ('HFun a ('HFun b ('HPair a b)))
    Inl  :: PrimOp ('HFun a ('HEither a b))
    Inr  :: PrimOp ('HFun b ('HEither a b))

    -- -- Array stuff
    Empty  :: PrimOp ('HArray a)
    Index  :: PrimOp ('HFun ('HArray a) ('HFun 'HNat a))
    Size   :: PrimOp ('HFun ('HArray a) 'HNat)
    -- TODO: is that the right type for the first argument? or was it a binder of some sort?
    Reduce :: PrimOp
        ('HFun ('HFun a ('HFun a a))
        ('HFun a
        ('HFun ('HArray a)
        a)))


    -- -- HOrder operators
    -- TODO: equality doesn't make constructive sense on the reals...
    -- would it be better to constructivize our notion of total ordering?
    -- TODO: what about posets?
    Less  :: (HOrder a) => PrimOp ('HFun a ('HFun a 'HBool))
    Equal :: (HOrder a) => PrimOp ('HFun a ('HFun a 'HBool))


    -- -- HSemiring operators (the non-n-ary ones)
    NatPow :: (HSemiring a) => PrimOp ('HFun a ('HFun 'HNat a))
    -- TODO: would it help to have a specialized version for when
    -- we happen to know that the 'HNat is a Value? Same goes for
    -- the other powers/roots


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
    Negate :: (HRing a) => PrimOp ('HFun a a)
    Abs    :: (HRing a) => PrimOp ('HFun a (NonNegative a))
    -- cf., <https://mail.haskell.org/pipermail/libraries/2013-April/019694.html>
    -- cf., <https://en.wikipedia.org/wiki/Sign_function#Complex_signum>
    -- Should we have Maple5's \"csgn\" as well as the usual \"sgn\"?
    -- Also note that the \"generalized signum\" anticommutes with Dirac delta!
    Signum :: (HRing a) => PrimOp ('HFun a a)
    -- Law: x = coerceTo_ signed (abs_ x) * signum x
    -- More strictly/exactly, the result of Signum should be either
    -- zero or an @a@-unit value. For Int and Real, the units are
    -- +1 and -1. For Complex, the units are any point on the unit
    -- circle. For vectors, the units are any unit vector. Thus,
    -- more generally:
    -- Law : x = coerceTo_ signed (abs_ x) `scaleBy` signum x
    -- TODO: would it be worth defining the associated type of unit values for @a@? Probably...
    -- TODO: are there any salient types which support abs/norm but
    -- do not have all units and thus do not support signum/normalize?


    -- -- HFractional operators
    Recip :: (HFractional a) => PrimOp ('HFun a a)
    -- generates macro: IntPow


    -- -- HRadical operators
    NatRoot :: (HRadical a) => PrimOp ('HFun a ('HFun 'HNat a))
    -- generates macros: Sqrt, NonNegativeRationalPow, and RationalPow


    -- -- HContinuous operators
    -- TODO: what goes here, if anything? cf., <https://en.wikipedia.org/wiki/Closed-form_expression#Comparison_of_different_classes_of_expressions>
    Erf :: (HContinuous a) => PrimOp ('HFun a a)
    -- TODO: make Pi and Infinity HContinuous-polymorphic so that we can avoid the explicit coercion? Probably more mess than benefit.


deriving instance Eq   (PrimOp a)
-- BUG: deriving instance Read (PrimOp a)
deriving instance Show (PrimOp a)


----------------------------------------------------------------
----------------------------------------------------------------
-- TODO: extend our patterns to include the embed/SOP stuff
-- TODO: negative patterns? (to facilitate reordering of case branches)
-- TODO: exhaustiveness, non-overlap, dead-branch checking
--
-- We index patterns by the type they scrutinize. This requires the
-- parser to be smart enough to build these patterns up, but then
-- it guarantees that we can't have 'Case_' of patterns which can't
-- possibly match according to our type system. If we wanted to go
-- really crazy, we could also index patterns by the type of what
-- variables they bind, like we'll do for ASTPattern... But that's
-- prolly overkill since we can just run the type checker over our
-- AST.
data Pattern :: Hakaru * -> * where
    PWild  :: Pattern a
    PVar   :: Pattern a
    PTrue  :: Pattern 'HBool
    PFalse :: Pattern 'HBool
    PUnit  :: Pattern 'HUnit
    PPair  :: !(Pattern a) -> !(Pattern b) -> Pattern ('HPair a b)
    PInl   :: !(Pattern a) -> Pattern ('HEither a b)
    PInr   :: !(Pattern b) -> Pattern ('HEither a b)

deriving instance Eq   (Pattern a)
-- BUG: deriving instance Read (Pattern a)
deriving instance Show (Pattern a)


----------------------------------------------------------------
-- TODO: finish switching from HOAS to ABT
-- TODO: define a well-formedness check for the ABT structure, since
-- we don't encode it into the Haskell types themselves. For clarity,
-- we do note the typing environments for the open terms via comments.
-- TODO: should we tag the @abt@ type to capture whether the use
-- sites must/must-not be 'Open' terms? Or is the well-formedness
-- check sufficient?
data AST :: (Hakaru * -> *) -> Hakaru * -> * where

    -- -- Standard lambda calculus stuff
    -- We store a Proxy in Lam_, so we needn't infer @a@ in the result.
    Lam_    :: !(Proxy a) -> ast {-a-} b -> AST ast ('HFun a b)
    App_    :: ast ('HFun a b) -> ast a -> AST ast b
    Let_    :: ast a -> ast {-a-} b -> AST ast b
    -- TODO: a general \"@let*@\" version of let-binding so we can have mutual recursion
    Fix_    :: ast {-a-} a -> AST ast a


    -- -- Primitive operators
    PrimOp_ :: !(PrimOp a) -> AST ast a
    NaryOp_ :: !(NaryOp a) -> !(Seq (ast a)) -> AST ast a

    -- -- Binding forms for integration (both continuous and discrete)
    Integrate_
        :: ast 'HReal
        -> ast 'HReal
        -> ast {-'HReal-} 'HProb
        -> AST ast 'HProb
    Summate_
        :: ast 'HReal -- TODO: should that really be 'HReal ?!
        -> ast 'HReal -- TODO: should that really be 'HReal ?!
        -> ast {-'HInt-} 'HProb
        -> AST ast 'HProb


    -- -- Primitive atomic types: their values and coercions
    Value_      :: !(Value a)               -> AST ast a
    CoerceTo_   :: !(Coercion a b) -> ast a -> AST ast b
    UnsafeFrom_ :: !(Coercion a b) -> ast b -> AST ast a
    -- TODO: add @SafeFrom_ :: Coercion a b -> ast b -> AST ast ('HMaybe a)@ or something similar?


    -- -- Primitive data types (which aren't PrimOps)
    -- TODO: add the embed stuff...
    -- TODO: replace 'HList and 'HMaybe by the embed stuff...
    -- TODO: replace 'HUnit, 'HPair, and 'HEither by the embed stuff...
    List_  :: [ast a]       -> AST ast ('HList a)
    Maybe_ :: Maybe (ast a) -> AST ast ('HMaybe a)
    -- | Generic case-analysis (via ABTs and Structural Focalization).
    Case_
        :: ast a
        -> [{-exists Γ.-} (Pattern a {-Γ-}, ast {-Γ-} b)]
        -> AST ast b
    -- TODO: do we really need this to be a binding form, or could it take a Hakaru function (HFun) for the second argument?
    Array_ :: ast 'HNat -> ast {-'HNat-} a -> AST ast ('HArray a)


    -- -- Mochastic stuff (which isn't PrimOps)
    -- TODO: should Dirac move back here?
    Bind_
        :: ast ('HMeasure a)
        -> ast {-a-} ('HMeasure b)
        -> AST ast ('HMeasure b)
    Superpose_
        :: [(ast 'HProb, ast ('HMeasure a))]
        -> AST ast ('HMeasure a)
    Dp_ -- Dirichlet process
        :: ast 'HProb
        -> ast ('HMeasure a)
        -> AST ast ('HMeasure ('HMeasure a))
    Plate_
        :: ast ('HArray ('HMeasure a))
        -> AST ast ('HMeasure ('HArray a))
    Chain_
        :: ast ('HArray ('HFun s ('HMeasure ('HPair a s))))
        -> AST ast ('HFun s ('HMeasure ('HPair ('HArray a) s)))


    -- Lub
    -- TODO: should this really be part of the AST?
    Lub_ :: ast a -> ast a -> AST ast a
    Bot_ :: AST ast a


----------------------------------------------------------------
----------------------------------------------------------------
{-
instance (Number a) => Order AST (a :: Hakaru *) where
    less  = app2 $ PrimOp_ (Less  {- at type @a@ -})
    equal = app2 $ PrimOp_ (Equal {- at type @a@ -})


{- TODO:
class (Order_ a) => Number (a :: Hakaru *) where
  numberCase :: f 'HInt -> f 'HReal -> f 'HProb -> f a
  numberRepr :: (Base repr) =>
                ((Order repr a, Num (repr a)) => f repr a) -> f repr a

class (Number a) => Fraction (a :: Hakaru *) where
  fractionCase :: f 'HReal -> f 'HProb -> f a
  fractionRepr :: (Base repr) =>
                  ((Order repr a, Fractional (repr a)) => f repr a) -> f repr a
  unsafeProbFraction = fromBaseAST . UnsafeFrom_ signed . baseToAST
  piFraction         = fromBaseAST $ PrimOp Pi
  expFraction        = fromBaseAST . App (PrimOp_ Exp) . baseToAST
  logFraction        = fromBaseAST . App (PrimOp_ Log) . baseToAST
  erfFraction        = fromBaseAST . App (PrimOp_ Erf) . baseToAST
-}

instance
    ( Order AST 'HInt , Num        (AST 'HInt )
    , Order AST 'HReal, Floating   (AST 'HReal)
    , Order AST 'HProb, Fractional (AST 'HProb)
    ) => Base AST where
    unit       = PrimOp_ Unit
    pair       = primOp2_ Pair
    unpair e f = do
        x <- freshVar
        y <- freshVar
        return $ Case_ (syn e)
            [(PPair PVar PVar,
                open x (open y (syn $ f (var x Proxy) (var y Proxy)))]
    inl        = primOp1_ Inl
    inr        = primOp1_ Inr
    uneither e l r = do
        x <- freshVar
        return $ Case_ (syn e)
            [ (PInl PVar, open x (syn $ l (var x Proxy)))
            , (PInr PVar, open x (syn $ r (var x Proxy)))
            ]
    true       = Value_ (Bool_ True)
    false      = Value_ (Bool_ False)
    if_ b t f  = Case_ (syn b) [(PTrue, syn t), (PFalse, syn f)]
    unsafeProb = UnsafeFrom_ signed
    fromProb   = CoerceTo_ signed
    fromInt    = CoerceTo_ continuous
    pi_        = PrimOp_ Pi
    exp_       = App $ PrimOp_ Exp
    erf        = App $ PrimOp_ (Erf {- 'HReal -})
    erf_       = App $ PrimOp_ (Erf {- 'HProb -})
    log_       = App $ PrimOp_ Log
    sqrt_ x    = app2 (PrimOp_ NatRoot) x (Value_ (Nat_ 2))
    pow_       = app2 $ PrimOp_ RealPow
    infinity   = CoerceTo_ signed $ PrimOp_ Infinity
    negativeInfinity = PrimOp_ NegativeInfinity
    gammaFunc = App  $ PrimOp_ GammaFunc
    betaFunc  = app2 $ PrimOp_ BetaFunc
    vector    = Array_
    empty     = PrimOp_  Empty
    index     = primOp2_ Index
    size      = primOp1_ Size
    reduce    = primOp3_ Reduce
    fix       = Fix_


----------------------------------------------------------------
easierRoadmapProg3'out
    :: (Mochastic repr)
    => repr ('HPair 'HReal 'HReal)
    -> repr ('HMeasure ('HPair 'HProb 'HProb))
easierRoadmapProg3'out m1m2 =
    weight 5 $
    uniform 3 8 `bind` \noiseT' ->
    uniform 1 4 `bind` \noiseE' ->
    weight (recip pi_
	    * exp_ (((fst_ m1m2) * (fst_ m1m2) * (noiseT' * noiseT') * 2
		     + noiseT' * noiseT' * (fst_ m1m2) * (snd_ m1m2) * (-2)
		     + (snd_ m1m2) * (snd_ m1m2) * (noiseT' * noiseT')
		     + noiseE' * noiseE' * ((fst_ m1m2) * (fst_ m1m2))
		     + noiseE' * noiseE' * ((snd_ m1m2) * (snd_ m1m2)))
		    * recip (noiseT' * noiseT' * (noiseT' * noiseT') + noiseE' * noiseE' * (noiseT' * noiseT') * 3 + noiseE' * noiseE' * (noiseE' * noiseE'))
		    * (-1/2))
	    * pow_ (unsafeProb (noiseT' ** 4 + noiseE' ** 2 * noiseT' ** 2 * 3 + noiseE' ** 4)) (-1/2)
	    * (1/10)) $
    dirac (pair (unsafeProb noiseT') (unsafeProb noiseE'))


-- This should be given by the client, not auto-generated by Hakaru.
proposal
    :: (Mochastic repr)
    => repr ('HPair 'HReal 'HReal)
    -> repr ('HPair 'HProb 'HProb)
    -> repr ('HMeasure ('HPair 'HProb 'HProb))
proposal _m1m2 ntne =
  unpair ntne $ \noiseTOld noiseEOld ->
  superpose [(1/2, uniform 3 8 `bind` \noiseT' ->
                   dirac (pair (unsafeProb noiseT') noiseEOld)),
             (1/2, uniform 1 4 `bind` \noiseE' ->
                   dirac (pair noiseTOld (unsafeProb noiseE')))]


-- This should be in a library somewhere, not auto-generated by Hakaru.
mh  :: (Mochastic repr, Integrate repr, Lambda repr,
        env ~ Expect' env, a ~ Expect' a, Backward a a)
    => (forall r'. (Mochastic r') => r' env -> r' a -> r' ('HMeasure a))
    -> (forall r'. (Mochastic r') => r' env -> r' ('HMeasure a))
    -> repr ('HFun env ('HFun a ('HMeasure ('HPair a 'HProb))))
mh prop target =
  lam $ \env ->
  let_ (lam (d env)) $ \mu ->
  lam $ \old ->
    prop env old `bind` \new ->
    dirac (pair new (mu `app` {-pair-} new {-old-} / mu `app` {-pair-} old {-new-}))
  where d:_ = density (\env -> {-bindx-} (target env) {-(prop env)-})
-}
