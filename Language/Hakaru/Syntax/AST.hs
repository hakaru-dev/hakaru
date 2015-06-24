-- TODO: <https://git-scm.com/book/en/v2/Git-Branching-Basic-Branching-and-Merging>
{-# LANGUAGE KindSignatures
           , DataKinds
           , TypeFamilies
           , GADTs
           , FlexibleInstances
           #-}

module Language.Hakaru.Syntax.AST where

import Prelude hiding (id, (.), Ord(..), Num(..), Integral(..), Fractional(..), Floating(..), Real(..), RealFrac(..), RealFloat(..), (^), (^^))
import           Data.Sequence (Seq)
import qualified Data.Sequence as Seq

import Control.Category (Category(..))
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
-- TODO: class HEq (a :: Hakaru *)
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
-- TODO: Can we specify that the @HSemiring (NonNegative a)@ constraint coincides with the @HSemiring a@ constraint on the appropriate subset of @a@? Or should that just be assumed...?
class (HSemiring (NonNegative a), HSemiring a)
    => HRing (a :: Hakaru *) where type NonNegative a :: Hakaru *
instance HRing 'HInt  where type NonNegative 'HInt  = 'HNat 
instance HRing 'HReal where type NonNegative 'HReal = 'HProb 


-- N.B., We're assuming two-sided inverses here. That doesn't entail commutativity, though it does strongly suggest it... (cf., Wedderburn's little theorem)
-- A division-semiring; Not quite a field nor a division-ring...
-- N.B., the (Nat,"+"=lcm,"*"=gcd) semiring is sometimes called "the division semiring"
-- HACK: tracking carriers here wouldn't be quite right b/c we get more than just the (non-negative)rationals generated from HNat/HInt! However, we should have some sort of associated type so we can add rationals and non-negative rationals...
class (HSemiring a) => HFractional (a :: Hakaru *)
instance HFractional 'HProb
instance HFractional 'HReal

-- type HDivisionRing a = (HFractional a, HRing a)
-- type HField a = (HDivisionRing a, HCommutativeSemiring a)


-- Numbers formed by finitely many uses of integer addition, subtraction, multiplication, division, and nat-roots are all algebraic; however, N.B., not all algebraic numbers can be formed this way (cf., Abel–Ruffini theorem)
-- TODO: ought we require HRing or HFractional rather than HSemiring?
-- TODO: any special associated type?
-- N.B., we /assume/ closure under the semiring operations, thus we get things like @sqrt 2 + sqrt 3@ which cannot be expressed as a single root. Thus, solving the HRadical class means we need solutions to more general polynomials (than just @x^n - a@) in order to express the results as roots. However, the Galois groups of these are all solvable, so this shouldn't be too bad.
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
-- | Primitive proofs of the inclusions in our numeric hierarchy.
data PrimCoercion :: Hakaru * -> Hakaru * -> * where
    Signed     :: HRing a       => PrimCoercion (NonNegative a) a
    Continuous :: HContinuous a => PrimCoercion (HIntegral   a) a

-- | General proofs of the inclusions in our numeric hierarchy.
data Coercion :: Hakaru * -> Hakaru * -> * where
    -- | Added the trivial coercion so we get the Category instance.
    -- This may/should make program transformations easier to write
    -- by allowing more intermediate ASTs, but will require a cleanup
    -- pass afterwards to remove the trivial coercions.
    IdCoercion :: Coercion a a

    -- | We use a cons-based approach rather than append-based in
    -- order to get a better inductive hypothesis.
    ConsCoercion :: !(PrimCoercion a b) -> !(Coercion b c) -> Coercion a c

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

-- TODO: implement a simplifying pass for pushing/gathering coersions over other things (e.g., Less_/Equal_)


----------------------------------------------------------------
-- TODO: add constructors for constants of datatypes?
-- | Constant values for primitive types (with concrete interpretation a~la Sample')
data Value :: Hakaru * -> * where
    Bool_ :: Bool     -> Value 'HBool
    Nat_  :: Nat      -> Value 'HNat
    Int_  :: Int      -> Value 'HInt
    Prob_ :: LogFloat -> Value 'HProb
    Real_ :: Double   -> Value 'HReal

----------------------------------------------------------------
-- TODO: move these into 'PrimOp'? Hve to deal with the two polymorphic ones first... Of course, those two are kinda special anyways...
-- | Primitive distributions/measures, a~la Mochastic.
data Measure :: Hakaru * -> * where
    Dirac       :: AST a -> Measure a
    Lebesgue    :: Measure 'HReal
    Counting    :: Measure 'HInt
    Superpose   :: [(AST 'HProb, Measure a)] -> Measure a
    Categorical :: AST ('HArray 'HProb) -> Measure 'HNat
    Uniform     :: AST 'HReal -> AST 'HReal -> Measure 'HReal
    Normal      :: AST 'HReal -> AST 'HProb -> Measure 'HReal
    Poisson     :: AST 'HProb -> Measure 'HNat
    Gamma       :: AST 'HProb -> AST 'HProb -> Measure 'HProb
    Beta        :: AST 'HProb -> AST 'HProb -> Measure 'HProb
    -- binomial, mix, geometric, multinomial,... should also be HNat

----------------------------------------------------------------
-- TODO: figure out how to fit the simple polymorphic functions (e.g., Less_/Equal_) into this framework. In general, will be some Haskell function from a type/dictionary to the PrimOp.
-- | Primitive /monomorphic/ functions, constants, and measures.
data PrimOp :: Hakaru * -> * where
    -- The Boolean operators
    -- TODO: we'll want n-ary And & Or, for the same reason as Plus_/Prod_
    -- TODO: most of these we'll want to optimize away according to some circuit-minimization procedure. But we're not committing to any particular minimal complete set of primops just yet.
    -- N.B., general circuit minimization problem is Sigma_2^P-complete, which is outside of PTIME; so we'll just have to approximate it for now, or link into something like Espresso or an implementation of Quine–McCluskey
    -- cf., <https://hackage.haskell.org/package/qm-0.1.0.0/candidate>
    -- cf., <https://github.com/pfpacket/Quine-McCluskey>
    -- cf., <https://gist.github.com/dsvictor94/8db2b399a95e301c259a>
    Not  :: PrimOp ('HFun 'HBool 'HBool)
    And  :: PrimOp ('HFun 'HBool ('HFun 'HBool 'HBool))
    Or   :: PrimOp ('HFun 'HBool ('HFun 'HBool 'HBool))
    Xor  :: PrimOp ('HFun 'HBool ('HFun 'HBool 'HBool))
    Iff  :: PrimOp ('HFun 'HBool ('HFun 'HBool 'HBool))
    Impl :: PrimOp ('HFun 'HBool ('HFun 'HBool 'HBool)) -- == Or (Not x) y
    -- ConverseImpl = flip Impl
    Diff :: PrimOp ('HFun 'HBool ('HFun 'HBool 'HBool)) -- == Not (Impl x y)
    -- ConverseDiff = flip Diff
    Nand :: PrimOp ('HFun 'HBool ('HFun 'HBool 'HBool)) -- aka Alternative Denial, Sheffer stroke
    Nor  :: PrimOp ('HFun 'HBool ('HFun 'HBool 'HBool)) -- aka Joint Denial, aka Quine dagger, aka Pierce arrow
    -- The other six binops are trivial
    
    
    -- Trigonometry operators
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
    
    
    -- Other Real/Prob-valued ops
    -- N.B., we only give the safe/exact versions here. The old more lenient versions now require explicit coercions. Some of those coercions are safe, but others are not. This way we're explicit about where things can fail.
    -- N.B., we also have @NatPow_ :: 'HReal -> 'HNat -> 'HReal@, but non-integer real powers of negative reals are not real numbers!
    -- TODO: may need @SafeFrom_@ in order to branch on the input in order to provide the old unsafe behavior.
    RealPow          :: PrimOp ('HFun 'HProb ('HFun 'HReal 'HProb))
    -- ComplexPow :: PrimOp ('HFun 'HProb ('HFun 'HComplex 'HComplex))
    -- is uniquely well-defined. Though we may want to implement it via @r**z = ComplexExp_ (z * RealLog_ r)@
    -- Defining @HReal -> HComplex -> HComplex@ requires either multivalued functions, or a choice of complex logarithm and making it discontinuous.
    Exp              :: PrimOp ('HFun 'HReal 'HProb)
    Log              :: PrimOp ('HFun 'HProb 'HReal)
    Infinity         :: PrimOp 'HProb
    NegativeInfinity :: PrimOp 'HReal -- TODO: maybe replace this by @negate (CoerceTo signed (PrimOp_ Infinity))@ ?
    Pi               :: PrimOp 'HProb
    GammaFunc        :: PrimOp ('HFun 'HReal 'HProb)
    BetaFunc         :: PrimOp ('HFun 'HProb ('HFun 'HProb 'HProb))

----------------------------------------------------------------
-- TODO: extend our patterns to include the embed/SOP stuff
-- TODO: negative patterns? (to facilitate reordering of case branches)
-- We index patterns by the type they scrutinize. This requires the parser to be smart enough to build these patterns up, but then it guarantees that we can't have 'Case_' of patterns which can't possibly match according to our type system. If we wanted to go really crazy, we could also index patterns by the type of what variables they bind, like we'll do for ASTPattern... But that's prolly overkill since we can just run the type checker over our AST.
data Pattern :: Hakaru * -> * where
    PWild  :: Pattern a
    PVar   :: Pattern a
    PTrue  :: Pattern 'HBool
    PFalse :: Pattern 'HBool
    PUnit  :: Pattern 'HUnit
    PPair  :: !(Pattern a) -> !(Pattern b) -> Pattern ('HPair a b)
    PInl   :: !(Pattern a) -> Pattern ('HEither a b)
    PInr   :: !(Pattern b) -> Pattern ('HEither a b)
    deriving (Eq, Read, Show)

----------------------------------------------------------------
-- TODO: (?)replace all the function primops (TrigOp, BoolOp, Not_, Erf_, GammaFunc_, BetaFunc_) with a proper signature and using Application? Would help to minimize the number of forms in the AST, and it'd make things more uniform wrf eta-expanding functional forms; however, it'd lead to constant-ly larger ASTs and we'd have to go in to recover the flatter structure...
-- If we did do that though, then why not also do the same for the numerical-hierarchy primops?

-- TODO: use the generating functor instead, so we can insert annotations with our fixpoint. Also, so we can use ABTs to separate our binders from the rest of our syntax
-- TODO: how does using the generating functor work for negative use sites??! (also non-strictlypositive use sites?)
data AST :: (Hakaru * -> *) -> Hakaru * -> * where
    -- Primitive types and their coercions
    Value_      :: Value a               -> AST ast a
    CoerceTo_   :: Coercion a b -> ast a -> AST ast b
    UnsafeFrom_ :: Coercion a b -> ast b -> AST ast a
    -- TODO: add @SafeFrom_ :: Coercion a b -> ast b -> AST ast ('HMaybe a)@ or something similar?
    
    
    -- Primitive data types
    List_  :: [ast a]       -> AST ast ('HList a)
    Maybe_ :: Maybe (ast a) -> AST ast ('HMaybe a)
    -- TODO: the embed stuff...
    Unit_  :: AST ast 'HUnit
    Pair_  :: ast a -> ast b -> AST ast ('HPair a b)
    Inl_   :: ast a -> AST ast ('HEither a b)
    Inr_   :: ast b -> AST ast ('HEither a b)
    Case_  :: ast a -> [(Pattern a, ast b)] -> AST ast b
    
    
    -- TODO: n-ary boolean operators
    -- The /non-polymorphic/ primitive operators.
    PrimOp_ :: PrimOp a -> AST ast a
    
    
    -- HOrder
    -- TODO: equality doesn't make constructive sense on the reals... would it be better to constructivize our notion of total ordering?
    -- TODO: what about posets?
    Less_  :: (HOrder a) => ast a -> ast a -> AST ast 'HBool
    Equal_ :: (HOrder a) => ast a -> ast a -> AST ast 'HBool
    
    
    -- HSemiring
    -- We prefer these n-ary versions to enable better pattern matching; the binary versions can be derived. Notably, because of this encoding, we encode subtraction and division via negation and reciprocal.
    -- TODO: helper functions for splitting Sum_/Prod_ into components to group up like things.
    Sum_    :: (HSemiring a) => Seq (ast a) -> AST ast a
    Prod_   :: (HSemiring a) => Seq (ast a) -> AST ast a
    NatPow_ :: (HSemiring a) => ast a -> ast 'HNat -> AST ast a
    -- TODO: an infix operator alias for NatPow_ a la (^)
    -- TODO: would it help to have a meta-AST version with Nat instead of AST'HNat?
    
    
    -- HRing
    -- TODO: break these apart into a hierarchy of classes. N.B, there are two different interpretations of "abs" and "signum". On the one hand we can think of rings as being generated from semirings closed under subtraction/negation. From this perspective we have abs as a projection into the underlying semiring, and signum as a projection giving us the residual sign lost by the abs projection. On the other hand, we have the view of "abs" as a norm (i.e., distance to the "origin point"), which is the more common perspective for complex numbers and vector spaces; and relatedly, we have "signum" as returning the value on the unit (hyper)sphere, of the normalized unit vector. In another class, if we have a notion of an "origin axis" then we can have a function Arg which returns the angle to that axis, and therefore define signum in terms of Arg.
    -- Ring: Semiring + negate, abs, signum
    -- NormedLinearSpace: LinearSpace + originPoint, norm, Arg
    -- ??: NormedLinearSpace + originAxis, angle
    Negate_ :: (HRing a) => ast a -> AST ast a
    Abs_    :: (HRing a) => ast a -> AST ast (NonNegative a)
    -- cf., <https://mail.haskell.org/pipermail/libraries/2013-April/019694.html>
    -- cf., <https://en.wikipedia.org/wiki/Sign_function#Complex_signum>
    -- Should we have Maple5's \"csgn\" as well as the usual \"sgn\"?
    -- Also note that the \"generalized signum\" anticommutes with Dirac delta!
    Signum_ :: (HRing a) => ast a -> AST ast a
    -- Law: x = CoerceTo_ signed (Abs_ x) * Signum_ x
    -- More strictly, the result of Signum_ should be either zero or an @a@-unit value. For Int and Real, the units are +1 and -1. For Complex, the units are any point on the unit circle. For vectors, the units are any unit vector. Thus, more generally:
    -- Law : x = CoerceTo_ signed (Abs_ x) `scaleBy` Signum_ x
    -- TODO: would it be worth defining the associated type of unit values for @a@? Probably...
    -- TODO: are there any salient types which support abs/norm but do not have all units and thus do not support signum/normalize?
    
    
    -- HFractional
    Recip_ :: (HFractional a) => ast a -> AST ast a
    -- TODO: define IntPow_ as a metaprogram
    -- TODO: an infix operator alias for the IntPow_ metaprogram a la (^^)
    
    
    -- HRadical
    NatRoot_ :: (HRadical a) => ast a -> ast 'HNat -> AST ast a
    -- TODO: define RationalPow_ and NonNegativeRationalPow_ metaprograms
    -- TODO: a infix operator aliases for them
    
    
    -- HContinuous
    -- TODO: what goes here? if anything? cf., <https://en.wikipedia.org/wiki/Closed-form_expression#Comparison_of_different_classes_of_expressions>
    Erf_ :: HContinuous a => ast a -> AST ast a
    -- TODO: make Pi_ and Infinity_ HContinuous-polymorphic so that we can avoid the explicit coercion? Probably more mess than benefit.
    
    
    -- Array stuff
    -- TODO: avoid exotic HOAS terms in Array_ & Reduce_
    Array_  :: ast 'HNat -> (ast 'HNat -> ast a) -> AST ast ('HArray a)
    Empty_  :: AST ast ('HArray a)
    Index_  :: ast ('HArray a) -> ast 'HNat -> AST ast a
    Size_   :: ast ('HArray a) -> AST ast 'HNat
    Reduce_ :: (ast a -> ast a -> ast a) -> ast a -> ast ('HArray a) -> AST ast a
    
    -- TODO: avoid exotic HOAS terms
    Fix_    :: (ast a -> ast a) -> AST ast a
    
    -- Mochastic
    Measure_ :: Measure a -> AST ast ('HMeasure a)
    Bind_    :: ast ('HMeasure a) -> (ast a -> ast ('HMeasure b)) -> AST ast ('HMeasure b)
    Dp_ :: ast 'HProb -> ast ('HMeasure a) -> AST ast ('HMeasure ('HMeasure a))
    Plate_ :: ast ('HArray ('HMeasure a)) -> AST ast ('HMeasure ('HArray a))
    Chain_
        :: ast ('HArray ('HFun s ('HMeasure ('HPair a s))))
        -> AST ast ('HFun s ('HMeasure ('HPair ('HArray a) s)))

    -- Integrate
    -- TODO: avoid exotic HOAS terms
    Integrate_ :: ast 'HReal -> ast 'HReal -> (ast 'HReal -> ast 'HProb) -> AST ast 'HProb
    Summate_   :: ast 'HReal -> ast 'HReal -> (ast 'HInt  -> ast 'HProb) -> AST ast 'HProb
    
    -- Lambda
    -- TODO: avoid exotic terms from using HOAS
    Lam_ :: (ast a -> ast b) -> AST ast ('HFun a b)
    App_ :: ast ('HFun a b) -> ast a -> AST ast b
    Let_ :: ast a -> (ast a -> ast b) -> AST ast b
    
    -- Lub
    -- TODO: should this really be part of the AST?
    Lub_ :: ast a -> ast a -> AST ast a
    Bot_ :: AST ast a


{-
Below we implement a lot of simple optimizations; however, these optimizations only apply if the client uses the type class methods to produce the AST. We should implement a stand-alone function which performs these sorts of optimizations, as a program transformation.
-}

-- N.B., we don't take advantage of commutativity, for more predictable AST outputs. However, that means we can end up being really slow;
-- N.B., we also don't try to eliminate the identity elements or do cancellations because (a) it's undecidable in general, and (b) that's prolly better handled as a post-processing simplification step
instance HRing a => Num (AST a) where
    Sum_ xs  + Sum_ ys  = Sum_ (xs Seq.>< ys)
    Sum_ xs  + y        = Sum_ (xs Seq.|> y)
    x        + Sum_ ys  = Sum_ (x  Seq.<| ys)
    x        + y        = Sum_ (x  Seq.<| Seq.singleton y)
    
    Sum_ xs  - Sum_ ys  = Sum_ (xs Seq.>< map negate ys)
    Sum_ xs  - y        = Sum_ (xs Seq.|> negate y)
    x        - Sum_ ys  = Sum_ (x  Seq.<| map negate ys)
    x        - y        = Sum_ (x  Seq.<| Seq.singleton (negate y))
    
    Prod_ xs * Prod_ ys = Prod_ (xs Seq.>< ys)
    Prod_ xs * y        = Prod_ (xs Seq.|> y)
    x        * Prod_ ys = Prod_ (x  Seq.<| ys)
    x        * y        = Prod_ (x  Seq.<| Seq.singleton y)

    negate (Negate_ x)  = x
    negate x            = Negate_ x
    
    abs (CoerceTo_ (ConsCoercion Signed IdCoercion) x) = CoerceTo_ signed x
    abs x = CoerceTo_ signed (Abs_ x)
    
    -- TODO: any obvious simplifications? idempotent?
    signum = Signum_
    
    fromInteger = error "fromInteger: unimplemented" -- TODO


instance (HRing a, HFractional a) => Fractional (AST a) where
    Prod_ xs / Prod_ ys = Prod_ (xs Seq.>< map recip ys)
    Prod_ xs / y        = Prod_ (xs Seq.|> recip y)
    x        / Prod_ ys = Prod_ (x  Seq.<| map recip ys)
    x        / y        = Prod_ (x  Seq.<| Seq.singleton (recip y))
    
    recip (Recip_ x) = x
    recip x          = Recip_ x
    
    fromRational = error "fromRational: unimplemented" -- TODO


{-
-- Can't do this, because no @HRing 'HProb@ instance
-- Also because the trigonometry functions wouldn't be well-typed/safe
-- Further evidence of being a bad abstraction...
instance Floating (AST 'HProb) where
    pi     = PrimOp_ Pi
    exp    = App (PrimOp_ Exp) . CoerceTo_ signed
    log    = UnsafeFrom_ signed . App (PrimOp_ Log) -- error for inputs in [0,1)
    sqrt x = NatRoot_ x 2
    x ** y = RealPow_ x (CoerceTo_ signed y)
    logBase b x = log x / log b -- undefined when b == 1
-}

instance Floating (AST 'HReal) where
    pi     = CoerceTo_ signed $ PrimOp_ Pi
    exp    = CoerceTo_ signed . App (PrimOp_ Exp)
    log    = App (PrimOp_ Log) . UnsafeFrom_ signed -- error for inputs in [negInfty,0)
    sqrt x = NatRoot_ x 2
    (**)   = app2 $ PrimOp_ RealPow
    logBase b x = log x / log b -- undefined when b == 1
    sin    = App $ PrimOp_ Sin
    cos    = App $ PrimOp_ Cos
    tan    = App $ PrimOp_ Tan
    asin   = App $ PrimOp_ Asin
    acos   = App $ PrimOp_ Acos
    atan   = App $ PrimOp_ Atan
    sinh   = App $ PrimOp_ Sinh
    cosh   = App $ PrimOp_ Cosh
    tanh   = App $ PrimOp_ Tanh
    asinh  = App $ PrimOp_ Asinh
    acosh  = App $ PrimOp_ Acosh
    atanh  = App $ PrimOp_ Atanh

----------------------------------------------------------------
----------------------------------------------------------------
{-
instance (Number a) => Order AST (a :: Hakaru *) where
    less  = Less_
    equal = Equal_
    
    
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
  piFraction         = fromBaseAST . Pi_
  expFraction        = fromBaseAST . Exp_ . baseToAST
  logFraction        = fromBaseAST . Log_ . baseToAST
  erfFraction        = fromBaseAST . Erf_ . baseToAST
-}

instance
    ( Order AST 'HInt , Num        (AST 'HInt )
    , Order AST 'HReal, Floating   (AST 'HReal)
    , Order AST 'HProb, Fractional (AST 'HProb)
    ) => Base AST where
    unit       = Unit_
    pair       = Pair_
    unpair e f = do
        x <- freshVar
        y <- freshVar
        return $ Case_ (syn e)
            [(PPair PVar PVar,
                open x (open y (syn $ f (var x Proxy) (var y Proxy)))]
    inl        = Inl_
    inr        = Inr_
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
    erf        = Erf_  -- Monomorphized at 'HReal
    erf_       = Erf_  -- Monomorphized at 'HProb
    log_       = App $ PrimOp_ Log
    sqrt_ x    = NatRoot_ x 2 -- Monomorphized at 'HProb
    pow_       = app2 $ PrimOp_ RealPow
    infinity   = CoerceTo_ signed $ PrimOp_ Infinity
    negativeInfinity = PrimOp_ NegativeInfinity
    gammaFunc = App  $ PrimOp_ GammaFunc
    betaFunc  = app2 $ PrimOp_ BetaFunc
    vector    = Array_
    empty     = Empty_
    index     = Index_
    size      = Size_
    reduce    = Reduce_
    fix       = Fix_

instance Mochastic AST where
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

instance Integrate AST where
    integrate = Integrate_
    summate   = Summate_

instance Lambda AST where
    lam  = Lam_
    app  = App_
    let_ = Let_

instance Lub AST where
    lub = Lub_
    bot = Bot_

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
