-- TODO: <https://git-scm.com/book/en/v2/Git-Branching-Basic-Branching-and-Merging>
{-# LANGUAGE KindSignatures
           , DataKinds
           , TypeFamilies
           , GADTs
           , FlexibleInstances
           #-}

module Language.Hakaru.Syntax.Wrengr where

import Prelude hiding (id, (.))
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
class (HSemiring (NonNegative a), HSemiring a)
    => HRing (a :: Hakaru *) where type NonNegative a :: Hakaru *
instance HRing 'HInt  where type NonNegative 'HInt  = 'HNat 
instance HRing 'HReal where type NonNegative 'HReal = 'HProb 


-- N.B., We're assuming two-sided inverses here. That doesn't entail commutativity, though it does strongly suggest it...
-- A division-semiring; Not quite a field nor a division-ring...
-- N.B., the (Nat,"+"=lcm,"*"=gcd) semiring is sometimes called "the division semiring"
-- HACK: tracking carriers here wouldn't be quite right b/c we get more than just the (non-negative)rationals generated from HNat/HInt!
class (HSemiring a) => HFractional (a :: Hakaru *)
instance HFractional 'HProb
instance HFractional 'HReal


-- TODO: find a better name than HRadical
-- TODO: any special associated type?
class (HSemiring a) => HRadical (a :: Hakaru *)
instance HRadical 'HProb
instance HRadical 'HReal


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
-- | Primitive numeric types (with concrete interpretation a~la Sample')
data Constant :: Hakaru * -> * where
    Nat_  :: Nat      -> Constant 'HNat
    Int_  :: Int      -> Constant 'HInt
    Prob_ :: LogFloat -> Constant 'HProb
    Real_ :: Double   -> Constant 'HReal

----------------------------------------------------------------
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
-- TODO: use the generating functor instead, so we can insert annotations with our fixpoint. Also, so we can use ABTs to separate our binders from the rest of our syntax
data AST :: Hakaru * -> * where
    -- Primitive numeric types and their coercions
    Constant_   :: Constant a            -> AST a
    CoerceTo_   :: Coercion a b -> AST a -> AST b
    UnsafeFrom_ :: Coercion a b -> AST b -> AST a
    -- TODO: add @SafeFrom_ :: Coercion a b -> AST b -> AST ('HMaybe a)@ ?
    
    
    -- Primitive data types
    List_     :: [AST a]       -> AST ('HList a)
    Maybe_    :: Maybe (AST a) -> AST ('HMaybe a)
    -- TODO: the embed stuff...
    Unit_     :: AST 'HUnit
    Pair_     :: AST a -> AST b -> AST ('HPair a b)
    -- TODO: avoid exotic HOAS terms in Unpair_
    Unpair_   :: AST ('HPair a b) -> (AST a -> AST b -> AST c) -> AST c
    Inl_      :: AST a -> AST ('HEither a b)
    Inr_      :: AST b -> AST ('HEither a b)
    -- TODO: avoid exotic HOAS terms in Uneither_
    Uneither_ :: AST ('HEither a b) -> (AST a -> AST c) -> (AST b -> AST c) -> AST c
    True_     :: AST 'HBool
    False_    :: AST 'HBool
    If_       :: AST 'HBool -> AST a -> AST a -> AST a
    
    
    -- HOrder
    -- TODO: equality doesn't make constructive sense on the reals... would it be better to constructivize our notion of total ordering?
    -- TODO: what about posets?
    Less_  :: (HOrder a) => AST a -> AST a -> AST 'HBool
    Equal_ :: (HOrder a) => AST a -> AST a -> AST 'HBool
    
    
    -- HSemiring
    -- We prefer these n-ary versions to enable better pattern matching; the binary versions can be derived. Notably, because of this encoding, we encode subtraction and division via negation and reciprocal.
    -- TODO: helper functions for splitting Sum_/Prod_ into components to group up like things.
    Sum_    :: (HSemiring a) => [AST a] -> AST a
    Prod_   :: (HSemiring a) => [AST a] -> AST a
    NatPow_ :: (HSemiring a) => AST a -> AST 'HNat -> AST a
    -- TODO: an infix operator alias for NatPow_ a la (^)
    -- TODO: would it help to have a meta-AST version with Nat instead of AST'HNat?
    -- TODO: a metaprogram for: Square_ :: (HSemiring a) => AST a -> AST a
    
    
    -- HRing
    -- TODO: break these apart into a hierarchy of three classes. N.B, there are two different interpretations of "abs" and "signum". On the one hand we can think of rings as being generated from semirings closed under subtraction/negation. From this perspective we have abs as a projection into the underlying semiring, and signum as a projection giving us the residual sign lost by the abs projection. On the other hand, we have the view of "abs" as a norm (i.e., distance to the "origin point"), which is the more common perspective for complex numbers and vector spaces. Relatedly, we have "signum" as Arg (i.e., the angle to the "origin axis") which works for complex numbers and for vector spaces with a distinguished origin axis (e.g., the usual implementation of vector spaces with orthonormal basis via arrays). However, not all normed spaces have a notion of "origin axis", thus we can have norm without having Arg. Thus, we have at least the three following classes:
    -- Ring: Semiring + negate, abs, signum
    -- NormedLinearSpace: LinearSpace + originPoint, norm
    -- ??: Normed + originAxis, Arg
    Negate_ :: (HRing a) => AST a -> AST a
    Abs_    :: (HRing a) => AST a -> AST (NonNegative a)
    -- cf., <https://mail.haskell.org/pipermail/libraries/2013-April/019694.html>
    -- cf., <https://en.wikipedia.org/wiki/Sign_function#Complex_signum>
    -- Should we have Maple5's \"csgn\" as well as the usual \"sgn\"?
    -- Also note that the \"generalized signum\" anticommutes with Dirac delta!
    Signum_ :: (HRing a) => AST a -> AST a
    -- Law: x = CoerceTo_ signed (Abs_ x) * Signum_ x
    -- TODO: would it be worth defining @AST 'HSign = Zero | Plus | Minus@ and then having @Signum_ :: (HRing a) => AST a -> AST 'HSign@ and @FromSign_ :: (HRing a) => AST 'HSign -> AST a@?
    
    -- Norm_ :: (HNormedLinearSpace a) => AST a -> AST 'HProb
    -- Arg_  :: (?? a) => AST a -> AST a
    
    
    -- HFractional
    Recip_ :: (HFractional a) => AST a -> AST a
    -- TODO: an infix operator alias for the IntPow_ metaprogram a la (^^)
    
    -- HRadical
    -- TODO: a better name for this class
    NatRoot_ :: (HRadical a) => AST a -> AST 'HNat -> AST a
    -- TODO: an infix operator alias for the RationalPow_ and NonNegativeRationalPow_ metaprograms
    
    -- HContinuous
    -- TODO: what goes here: Sqrt_/RealPow_, trig stuff, erf,...?
    -- TODO: why single out Sqrt_? Why not single out Square_?
    -- TODO: distinguish PowNat, PowInt, PowRational, PowReal, PowComplex...
    Erf_     :: HContinuous a => AST a -> AST a
    Sqrt_    :: HContinuous a => AST a -> AST a
    RealPow_ :: HContinuous a => AST a -> AST 'HReal -> AST a
    
    
    -- Trigonometry
    -- TODO: capture more domain information in these types?
    -- TODO: group these out into a single Trig_ constructor (a~la Measure_)?
    -- TODO: if we're going to bother naming the hyperbolic ones, why not also name /a?(csc|sec|cot)h?/ eh?
    Pi_    :: AST 'HProb -- N.B., HProb means non-negative real!
    Sin_   :: AST 'HReal -> AST 'HReal
    Cos_   :: AST 'HReal -> AST 'HReal
    Tan_   :: AST 'HReal -> AST 'HReal
    Asin_  :: AST 'HReal -> AST 'HReal
    Acos_  :: AST 'HReal -> AST 'HReal
    Atan_  :: AST 'HReal -> AST 'HReal
    Sinh_  :: AST 'HReal -> AST 'HReal
    Cosh_  :: AST 'HReal -> AST 'HReal
    Tanh_  :: AST 'HReal -> AST 'HReal
    Asinh_ :: AST 'HReal -> AST 'HReal
    Acosh_ :: AST 'HReal -> AST 'HReal
    Atanh_ :: AST 'HReal -> AST 'HReal
    
    
    -- The rest of the old Base class
    -- N.B., we only give the safe/exact versions here. The lifting of exp'soutput can be done with fromProb; and the lowering of log's input can be done with unsafeProb/unsafeProbFraction
    Exp_              :: AST 'HReal -> AST 'HProb
    Log_              :: AST 'HProb -> AST 'HReal
    Infinity_         :: AST 'HReal -- TODO: does infinity also live in HProb?
    NegativeInfinity_ :: AST 'HReal
    GammaFunc_        :: AST 'HReal -> AST 'HProb
    BetaFunc_         :: AST 'HProb -> AST 'HProb -> AST 'HProb
    
    -- Array stuff
    Array_  :: AST 'HNat -> (AST 'HNat -> AST a) -> AST ('HArray a)
    Empty_  :: AST ('HArray a)
    Index_  :: AST ('HArray a) -> AST 'HNat -> AST a
    Size_   :: AST ('HArray a) -> AST 'HNat
    Reduce_ :: (AST a -> AST a -> AST a) -> AST a -> AST ('HArray a) -> AST a
    
    -- TODO: avoid exotic HOAS terms
    Fix_    :: (AST a -> AST a) -> AST a
    
    -- Mochastic
    Measure_ :: Measure a -> AST ('HMeasure a)
    Bind_    :: AST ('HMeasure a) -> (AST a -> AST ('HMeasure b)) -> AST ('HMeasure b)
    Dp_ :: AST 'HProb -> AST ('HMeasure a) -> AST ('HMeasure ('HMeasure a))
    Plate_ :: AST ('HArray ('HMeasure a)) -> AST ('HMeasure ('HArray a))
    Chain_
        :: AST ('HArray ('HFun s ('HMeasure ('HPair a s))))
        -> AST ('HFun s ('HMeasure ('HPair ('HArray a) s)))

    -- Integrate
    -- TODO: avoid exotic HOAS terms
    Integrate_ :: AST 'HReal -> AST 'HReal -> (AST 'HReal -> AST 'HProb) -> AST 'HProb
    Summate_   :: AST 'HReal -> AST 'HReal -> (AST 'HInt  -> AST 'HProb) -> AST 'HProb
    
    -- Lambda
    -- TODO: avoid exotic terms from using HOAS
    Lam_ :: (AST a -> AST b) -> AST ('HFun a b)
    App_ :: AST ('HFun a b) -> AST a -> AST b
    Let_ :: AST a -> (AST a -> AST b) -> AST b
    
    -- Lub
    -- TODO: should this really be part of the AST?
    Lub_ :: AST a -> AST a -> AST a
    Bot_ :: AST a



-- N.B., we don't take advantage of commutativity, for more predictable AST outputs. However, that means we can end up being really slow;
-- TODO: use sets, fingertrees, etc instead of lists...
-- N.B., we also don't try to eliminate the identity elements or do cancellations because (a) it's undecidable in general, and (b) that's prolly better handled as a post-processing simplification step
instance HRing a => Num (AST a) where
    Sum_ xs  + Sum_ ys  = Sum_ (xs ++ ys)
    Sum_ xs  + y        = Sum_ (xs ++ [y])
    x        + Sum_ ys  = Sum_ (x : ys)
    x        + y        = Sum_ [x,y]
    
    Sum_ xs  - Sum_ ys  = Sum_ (xs ++ map negate ys)
    Sum_ xs  - y        = Sum_ (xs ++ [negate y])
    x        - Sum_ ys  = Sum_ (x : map negate ys)
    x        - y        = Sum_ [x, negate y]
    
    Prod_ xs * Prod_ ys = Prod_ (xs ++ ys)
    Prod_ xs * y        = Prod_ (xs ++ [y])
    x        * Prod_ ys = Prod_ (x : ys)
    x        * y        = Prod_ [x,y]

    negate (Negate_ x)  = x
    negate x            = Negate_ x
    
    abs (CoerceTo_ (ConsCoercion Signed IdCoercion) x) = CoerceTo_ signed x
    abs x = CoerceTo_ signed (Abs_ x)
    
    -- TODO: any obvious simplifications? idempotent?
    signum = Signum_
    
    fromInteger = error "fromInteger: unimplemented" -- TODO


instance (HRing a, HFractional a) => Fractional (AST a) where
    Prod_ xs / Prod_ ys = Prod_ (xs ++ map recip ys)
    Prod_ xs / y        = Prod_ (xs ++ [recip y])
    x        / Prod_ ys = Prod_ (x : map recip ys)
    x        / y        = Prod_ [x, recip y]
    
    recip (Recip_ x) = x
    recip x          = Recip_ x
    
    fromRational = error "fromRational: unimplemented" -- TODO


{-
-- Can't do this, because no @HRing 'HProb@ instance
-- Further evidence of being a bad abstraction...
instance Floating (AST 'HProb) where
    pi     = Pi_
    exp    = Exp_ . CoerceTo_ signed
    log    = UnsafeFrom_ signed . Log_ -- error for inputs in [0,1)
    sqrt   = Sqrt_
    x ** y = RealPow_ x (CoerceTo_ signed y)
    logBase b x = log x / log b -- undefined when b == 1
    {-
    -- Most of these won't work...
    sin   :: AST 'HProb -> AST 'HProb
    cos   :: AST 'HProb -> AST 'HProb
    tan   :: AST 'HProb -> AST 'HProb
    asin  :: AST 'HProb -> AST 'HProb
    acos  :: AST 'HProb -> AST 'HProb
    atan  :: AST 'HProb -> AST 'HProb
    sinh  :: AST 'HProb -> AST 'HProb
    cosh  :: AST 'HProb -> AST 'HProb
    tanh  :: AST 'HProb -> AST 'HProb
    asinh :: AST 'HProb -> AST 'HProb
    acosh :: AST 'HProb -> AST 'HProb
    atanh :: AST 'HProb -> AST 'HProb
    -}
-}

instance Floating (AST 'HReal) where
    pi    = CoerceTo_ signed Pi_
    exp   = CoerceTo_ signed . Exp_
    log   = Log_ . UnsafeFrom_ signed -- error for inputs in [negInfty,0)
    sqrt  = Sqrt_
    (**)  = RealPow_
    logBase b x = log x / log b -- undefined when b == 1
    sin   = Sin_
    cos   = Cos_
    tan   = Tan_
    asin  = Asin_
    acos  = Acos_
    atan  = Atan_
    sinh  = Sinh_
    cosh  = Cosh_
    tanh  = Tanh_
    asinh = Asinh_
    acosh = Acosh_
    atanh = Atanh_

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
    unpair     = Unpair_
    inl        = Inl_
    inr        = Inr_
    uneither   = Uneither_
    true       = True_
    false      = False_
    if_        = If_
    unsafeProb = UnsafeFrom_ signed
    fromProb   = CoerceTo_ signed
    fromInt    = CoerceTo_ continuous
    pi_        = Pi_   -- Monomorphized at 'HProb
    exp_       = Exp_
    erf        = Erf_  -- Monomorphized at 'HReal
    erf_       = Erf_  -- Monomorphized at 'HProb
    log_       = Log_
    sqrt_      = Sqrt_ -- Monomorphized at 'HProb
    pow_       = RealPow_  -- Monomorphized at 'HProb
    infinity   = Infinity_
    negativeInfinity = NegativeInfinity_
    gammaFunc = GammaFunc_
    betaFunc  = BetaFunc_
    vector    = Array_
    empty     = Empty_
    index     = Index_
    size      = Size_
    reduce    = Reduce_
    fix       = Fix_

instance Mochastic AST where
    dirac       = Measure_ Dirac
    bind        = Bind_
    lebesgue    = Measure_ Lebesgue
    counting    = Measure_ Counting
    superpose   = Measure_ Superpose
    categorical = Measure_ Categorical
    uniform     = Measure_ Uniform
    normal      = Measure_ Normal
    poisson     = Measure_ Poisson
    gamma       = Measure_ Gamma
    beta        = Measure_ Beta
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
