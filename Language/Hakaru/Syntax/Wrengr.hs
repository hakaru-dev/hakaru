-- TODO: <https://git-scm.com/book/en/v2/Git-Branching-Basic-Branching-and-Merging>
{-# LANGUAGE KindSignatures
           , DataKinds
           , TypeFamilies
           , GADTs
           , FlexibleInstances
           #-}

module Language.Hakaru.Syntax.Wrengr where

import qualified Data.Number.LogFloat as LF
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

-- TODO: find a better name than HIntegral
-- TODO: how to require that "if HRing a, then HRing b too"?
class (HSemiring (HIntegral a), HFractional a)
    => HContinuous (a :: Hakaru *) where type HIntegral a :: Hakaru *
instance HContinuous 'HProb where type HIntegral 'HProb = 'HNat 
instance HContinuous 'HReal where type HIntegral 'HReal = 'HInt 



----------------------------------------------------------------
-- | Proofs of the inclusions in our numeric hierarchy.
data Coercion :: Hakaru * -> Hakaru * -> * where
    Signed     :: HRing a => Coercion (NonNegative a) a
    Continuous :: HContinuous a => Coercion (HIntegral a) a
    -- TODO: do we care that this gives a bad induction principle?
    ComposeCoercion :: Coercion a b -> Coercion b c -> Coercion a c
    -- TODO: should we include reflexivity for the category structure? That'd require a clean-up pass to remove them; but it may make for easier intermediate ASTs...

-- TODO: implement a simplifying pass for coalescing and cancelling CoerceTo_/UnsafeFrom_
-- TODO: implement a simplifying pass for pushing/gathering coersions over other things (e.g., Less_/Equal_)


----------------------------------------------------------------
-- TODO: use the generating functor instead, so we can insert annotations with our fixpoint. Also, so we can use ABTs to separate our binders from the rest of our syntax
data AST :: Hakaru * -> * where
    -- Primitive numeric types (with concrete interpretation a~la Sample')
    Nat_      :: Nat         -> AST 'HNat
    Int_      :: Int         -> AST 'HInt
    Prob_     :: LF.LogFloat -> AST 'HProb
    Real_     :: Double      -> AST 'HReal
    
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
    -- TODO: equality doesn't make constructive sense on the reals... would it be better to constructivize things?
    -- TODO: what about posets?
    Less_  :: (HOrder a) => AST a -> AST a -> AST 'HBool
    Equal_ :: (HOrder a) => AST a -> AST a -> AST 'HBool
    
    
    -- Coercion between primitive types
    -- TODO: add a SafeFrom_ alternative?
    CoerceTo_   :: Coercion a b -> AST a -> AST b
    UnsafeFrom_ :: Coercion a b -> AST b -> AST a
    
    
    -- HSemiring
    -- We prefer these n-ary versions to enable better pattern matching; the binary versions can be derived. Notably, because of this encoding, we encode subtraction and division via negation and reciprocal.
    Sum_  :: (HSemiring a) => [AST a] -> AST a
    Prod_ :: (HSemiring a) => [AST a] -> AST a
    -- (:^) :: (HSemiring a) => AST a -> AST 'HNat -> AST a
    
    
    -- HRing
    Negate_   :: (HRing a) => AST a -> AST a
    Abs_      :: (HRing a) => AST a -> AST (NonNegative a)
    -- cf., <https://mail.haskell.org/pipermail/libraries/2013-April/019694.html>
    -- cf., <https://en.wikipedia.org/wiki/Sign_function#Complex_signum>
    -- Should we have Maple5's \"csgn\" as well as the usual \"sgn\"?
    -- Also note that the \"generalized signum\" anticommutes with Dirac delta!
    Signum_ :: (HRing a) => AST a -> AST a
    -- Law: x = CoerceTo_ Signed (Abs_ x) * Signum_ x
    
    
    -- HFractional
    Recip_ :: (HFractional a) => AST a -> AST a
    -- (:^^) :: (HFractional a) => AST a -> AST 'HInt -> AST a
    
    -- HContinuous
    -- TODO: what goes here: Sqrt_/Pow_, trig stuff, erf,...?
    -- TODO: why single out Sqrt_? Why not single out Square_?
    -- TODO: distinguish PowNat, PowInt, PowRational, PowReal, PowComplex...
    Erf_   :: HContinuous a => AST a -> AST a
    Sqrt_  :: HContinuous a => AST a -> AST a
    Pow_   :: HContinuous a => AST a -> AST 'HReal -> AST a
    
    -- Trigonometry
    -- TODO: capture more domain information in these types?
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
    Infinity_         :: AST 'HReal
    NegativeInfinity_ :: AST 'HReal
    GammaFunc_        :: AST 'HReal -> AST 'HProb
    BetaFunc_         :: AST 'HProb -> AST 'HProb -> AST 'HProb
    
    -- Array stuff
    Array_      :: AST 'HNat -> (AST 'HNat -> AST a) -> AST ('HArray a)
    Empty_      :: AST ('HArray a)
    Index_      :: AST ('HArray a) -> AST 'HNat -> AST a
    Size_       :: AST ('HArray a) -> AST 'HNat
    Reduce_     :: (AST a -> AST a -> AST a) -> AST a -> AST ('HArray a) -> AST a
    Fix_        :: (AST a -> AST a) -> AST a
    
    -- Mochastic
    Dirac_       :: AST a -> AST ('HMeasure a)
    Bind_        :: AST ('HMeasure a) -> (AST a -> AST ('HMeasure b)) -> AST ('HMeasure b)
    Lebesgue_    :: AST ('HMeasure 'HReal)
    Counting_    :: AST ('HMeasure 'HInt)
    Superpose_   :: [(AST 'HProb, AST ('HMeasure a))] -> AST ('HMeasure a)
    Categorical_ :: AST ('HArray 'HProb) -> AST ('HMeasure 'HInt)
    Uniform_     :: AST 'HReal -> AST 'HReal -> AST ('HMeasure 'HReal)
    Normal_      :: AST 'HReal -> AST 'HProb -> AST ('HMeasure 'HReal)
    Poisson_     :: AST 'HProb -> AST ('HMeasure 'HInt)
    Gamma_       :: AST 'HProb -> AST 'HProb -> AST ('HMeasure 'HProb)
    Beta_        :: AST 'HProb -> AST 'HProb -> AST ('HMeasure 'HProb)
    Dp_ :: AST 'HProb -> AST ('HMeasure a) -> AST ('HMeasure ('HMeasure a))
    Plate_ :: AST ('HArray ('HMeasure a)) -> AST ('HMeasure ('HArray a))
    Chain_
        :: AST ('HArray ('HFun s ('HMeasure ('HPair a s))))
        -> AST ('HFun s ('HMeasure ('HPair ('HArray a) s)))

    -- Integrate
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
    
    abs (CoerceTo_ Signed x) = CoerceTo_ Signed x
    abs x                    = CoerceTo_ Signed (Abs_ x)
    
    -- TODO: any obvious simplifications?
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
    exp    = Exp_ . CoerceTo_ Signed
    log    = UnsafeFrom_ Signed . Log_ -- error for inputs in [0,1)
    sqrt   = Sqrt_
    x ** y = Pow_ x (CoerceTo_ Signed y)
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
    pi    = CoerceTo_ Signed Pi_
    exp   = CoerceTo_ Signed . Exp_
    log   = Log_ . UnsafeFrom_ Signed -- error for inputs in [negInfty,0)
    sqrt  = Sqrt_
    (**)  = Pow_
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
  unsafeProbFraction = fromBaseAST . UnsafeFrom_ Signed . baseToAST
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
    unsafeProb = UnsafeFrom_ Signed
    fromProb   = CoerceTo_ Signed
    fromInt    = CoerceTo_ Continuous
    pi_        = Pi_   -- Monomorphized at 'HProb
    exp_       = Exp_
    erf        = Erf_  -- Monomorphized at 'HReal
    erf_       = Erf_  -- Monomorphized at 'HProb
    log_       = Log_
    sqrt_      = Sqrt_ -- Monomorphized at 'HProb
    pow_       = Pow_  -- Monomorphized at 'HProb
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
    dirac       = Dirac_
    bind        = Bind_
    lebesgue    = Lebesgue_
    counting    = Counting_
    superpose   = Superpose_
    categorical = Categorical_
    uniform     = Uniform_
    normal      = Normal_
    poisson     = Poisson_
    gamma       = Gamma_
    beta        = Beta_
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