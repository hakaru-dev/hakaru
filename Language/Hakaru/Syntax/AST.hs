-- TODO: <https://git-scm.com/book/en/v2/Git-Branching-Basic-Branching-and-Merging>
{-# LANGUAGE CPP
           , DataKinds
           , PolyKinds
           , GADTs
           , StandaloneDeriving
           , PatternSynonyms
           , ScopedTypeVariables
           #-}
#if __GLASGOW_HASKELL__ < 710
{-# LANGUAGE TypeOperators #-}
#endif

{-# OPTIONS_GHC -Wall -fwarn-tabs #-}
----------------------------------------------------------------
--                                                    2015.06.30
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
--
-- TODO: are we finally at the place where we can get rid of all those annoying underscores?
----------------------------------------------------------------
module Language.Hakaru.Syntax.AST
    (
    -- * Constant values
      Value(..),  singValue
    -- * Primitive operators
    , NaryOp(..),  singNaryOp
    , PrimOp(..),  singPrimOp
    , Measure(..), singMeasure
    -- * User-defined data types
    -- ** Data constructors\/patterns
    , Datum(..)
    -- ** Pattern matching
    , Pattern(..)
    , pattern PTrue
    , pattern PFalse
    , pattern PUnit
    , pPair
    , pInl
    , pInr
    , Branch(..), branchPattern, branchBody
    -- * Syntactic forms
    , AST(..)
    ) where

import Prelude                 hiding ((.))
import Data.Sequence           (Seq)
import qualified Data.Foldable as F
import Data.Proxy
#if __GLASGOW_HASKELL__ < 710
import Data.Monoid
#endif
import Control.Category        (Category(..))
import Control.Arrow           ((***))
import Data.Number.LogFloat    (LogFloat)

import Language.Hakaru.Syntax.Nat
import Language.Hakaru.Syntax.IClasses
import Language.Hakaru.Syntax.DataKind
import Language.Hakaru.Syntax.TypeEq (Sing(..), SingI(..))
import Language.Hakaru.Syntax.HClasses
import Language.Hakaru.Syntax.Coercion

----------------------------------------------------------------
----------------------------------------------------------------
-- TODO: use 'Integer' instead of 'Int', and 'Natural' instead of 'Nat'.
-- | Constant values for primitive types.
data Value :: Hakaru -> * where
    Bool_ :: !Bool     -> Value HBool
    Nat_  :: !Nat      -> Value 'HNat
    Int_  :: !Int      -> Value 'HInt
    Prob_ :: !LogFloat -> Value 'HProb
    Real_ :: !Double   -> Value 'HReal
    -- TODO: Should we add a @Datum Value@ option here?

deriving instance Eq   (Value a)
-- BUG: deriving instance Read (Value a)
deriving instance Show (Value a)

-- N.B., we do case analysis so that we don't need the class constraint!
singValue :: Value a -> Sing a
singValue (Bool_ _) = sing
singValue (Nat_  _) = sing
singValue (Int_  _) = sing
singValue (Prob_ _) = sing
singValue (Real_ _) = sing

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
data NaryOp :: Hakaru -> * where
    And  :: NaryOp HBool
    Or   :: NaryOp HBool
    Xor  :: NaryOp HBool
    -- TODO: even though 'Iff' is associative (in Boolean algebras), we should not support n-ary uses in our *surface* syntax. Because it's too easy for folks to confuse "a <=> b <=> c" with "(a <=> b) /\ (b <=> c)".
    Iff  :: NaryOp HBool -- == Not (Xor x y)

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


-- N.B., we do case analysis so that we don't need the class constraint!
singNaryOp :: NaryOp a -> Sing a
singNaryOp And  = sing
singNaryOp Or   = sing
singNaryOp Xor  = sing
singNaryOp Iff  = sing
{- BUG: case analysis isn't enough here, because of the class constraints. We should be able to fix that by passing explicit singleton dictionaries instead of using Haskell's type classes
singNaryOp Min  = sing
singNaryOp Max  = sing
singNaryOp Sum  = sing
singNaryOp Prod = sing
-}
singNaryOp _ = error "TODO: singNaryOp"

----------------------------------------------------------------
-- | Simple primitive functions, and constants.
data PrimOp :: Hakaru -> * where

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
    Not  :: PrimOp ('HFun HBool HBool)
    -- And, Or, Xor, Iff
    Impl :: PrimOp ('HFun HBool ('HFun HBool HBool)) -- == Or (Not x) y
    Diff :: PrimOp ('HFun HBool ('HFun HBool HBool)) -- == Not (Impl x y)
    Nand :: PrimOp ('HFun HBool ('HFun HBool HBool)) -- aka Alternative Denial, Sheffer stroke
    Nor  :: PrimOp ('HFun HBool ('HFun HBool HBool)) -- aka Joint Denial, aka Quine dagger, aka Pierce arrow
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
    -- TODO: Log1p, Expm1
    Infinity  :: PrimOp 'HProb
    NegativeInfinity :: PrimOp 'HReal -- TODO: maybe replace this by @negate (CoerceTo signed (PrimOp_ Infinity))@ ?
    -- TODO: add Factorial as the appropriate type restriction of GammaFunc?
    GammaFunc :: PrimOp ('HFun 'HReal 'HProb)
    BetaFunc  :: PrimOp ('HFun 'HProb ('HFun 'HProb 'HProb))



    -- -- -- Here we have the /polymorphic/ operators
    -- TODO: \"monomorphize\" these by passing explicit dictionary proxies

    -- -- Array stuff
    -- TODO: do these really belong here (as PrimOps), in AST, or in their own place (a la Datum)?
    Empty  :: PrimOp ('HArray a)
    Index  :: PrimOp ('HFun ('HArray a) ('HFun 'HNat a))
    Size   :: PrimOp ('HFun ('HArray a) 'HNat)
    -- TODO: is that the right type for the first argument? or was it a binder of some sort? Or should it only accept an NaryOp?
    Reduce :: PrimOp
        ('HFun ('HFun a ('HFun a a))
        ('HFun a
        ('HFun ('HArray a)
        a)))


    -- -- HOrder operators
    -- TODO: equality doesn't make constructive sense on the reals...
    -- would it be better to constructivize our notion of total ordering?
    -- TODO: what about posets?
    Less  :: (HOrder a) => PrimOp ('HFun a ('HFun a HBool))
    Equal :: (HOrder a) => PrimOp ('HFun a ('HFun a HBool))


    -- -- HSemiring operators (the non-n-ary ones)
    NatPow :: (HSemiring a) => PrimOp ('HFun a ('HFun 'HNat a))
    -- TODO: would it help to have a specialized version for when
    -- we happen to know that the 'HNat is a Value? Same goes for
    -- the other powers/roots
    -- TODO: add a specialized version which returns NonNegative when the power is even? N.B., be sure not to actually constrain it to HRing (necessary for calling it \"NonNegative\")


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


-- N.B., we do case analysis so that we don't need the class constraint!
singPrimOp :: PrimOp a -> Sing a
singPrimOp Not         = sing
singPrimOp Impl        = sing
singPrimOp Diff        = sing
singPrimOp Nand        = sing
singPrimOp Nor         = sing
singPrimOp Pi          = sing
singPrimOp Sin         = sing
singPrimOp Cos         = sing
singPrimOp Tan         = sing
singPrimOp Asin        = sing
singPrimOp Acos        = sing
singPrimOp Atan        = sing
singPrimOp Sinh        = sing
singPrimOp Cosh        = sing
singPrimOp Tanh        = sing
singPrimOp Asinh       = sing
singPrimOp Acosh       = sing
singPrimOp Atanh       = sing
singPrimOp RealPow     = sing
singPrimOp Exp         = sing
singPrimOp Log         = sing
singPrimOp Infinity    = sing
singPrimOp NegativeInfinity = sing
singPrimOp GammaFunc   = sing
singPrimOp BetaFunc    = sing
{-
-- BUG: case analysis isn't enough here, because of the class constraints. We should be able to fix that by passing explicit singleton dictionaries instead of using Haskell's type classes. Of course, we can't even do Unit anymore because of whatever bugginess with the embed stuff :(
singPrimOp Empty       = sing
singPrimOp Index       = sing
singPrimOp Size        = sing
singPrimOp Reduce      = sing
singPrimOp Less        = sing
singPrimOp Equal       = sing
singPrimOp NatPow      = sing
singPrimOp Negate      = sing
singPrimOp Abs         = sing
singPrimOp Signum      = sing
singPrimOp Recip       = sing
singPrimOp NatRoot     = sing
singPrimOp Erf         = sing
-}
singPrimOp _ = error "TODO: singPrimOp"

----------------------------------------------------------------
-- TODO: move the rest of the old Mochastic class into here?
-- | Primitive distributions\/measures.
data Measure :: Hakaru -> * where
    -- TODO: should we put Dirac back into the main AST?
    -- TODO: could we move Dp_, Plate_, or Chain_ to here?
    Dirac       :: Measure ('HFun a ('HMeasure a))
    Lebesgue    :: Measure ('HMeasure 'HReal)
    Counting    :: Measure ('HMeasure 'HInt)
    Categorical :: Measure ('HFun ('HArray 'HProb) ('HMeasure 'HNat))
    -- TODO: make Uniform polymorphic, so that if the two inputs are HProb then we know the measure must be over HProb too. More generally, if the first input is HProb (since the second input is assumed to be greater thant he first); though that would be a bit ugly IMO.
    Uniform     :: Measure ('HFun 'HReal ('HFun 'HReal ('HMeasure 'HReal)))
    Normal      :: Measure ('HFun 'HReal ('HFun 'HProb ('HMeasure 'HReal)))
    Poisson     :: Measure ('HFun 'HProb ('HMeasure 'HNat))
    Gamma       :: Measure ('HFun 'HProb ('HFun 'HProb ('HMeasure 'HProb)))
    Beta        :: Measure ('HFun 'HProb ('HFun 'HProb ('HMeasure 'HProb)))
    -- binomial, mix, geometric, multinomial,... should also be HNat

deriving instance Eq   (Measure a)
-- BUG: deriving instance Read (Measure a)
deriving instance Show (Measure a)

-- N.B., we do case analysis so that we don't need the class constraint!
singMeasure :: Measure a -> Sing a
-- TODO: singMeasure Dirac       = sing
singMeasure Lebesgue    = sing
singMeasure Counting    = sing
singMeasure Categorical = sing
singMeasure Uniform     = sing
singMeasure Normal      = sing
singMeasure Poisson     = sing
singMeasure Gamma       = sing
singMeasure Beta        = sing

----------------------------------------------------------------
----------------------------------------------------------------

-- BUG: rename all the patterns, data-constructors, singletons, and types to be *consistent* everywhere!
        
-- TODO: generate a type inequality proof showing that @AST ast (a
-- :$ b)@ is impossible. Of a few proofs demonstrating that, in
-- general @(:$)@ only occurs here in Datum.
--
-- Heck, maybe we can move @(:$)@ out of the Hakaru data kind all
-- together. Here's the plan: First we get rid of 'Roll', fusing
-- into 'PDatum' and 'Datum_' (and anywhere else similar). Then the
-- index type of 'Datum' becomes uniform, so we can break it up
-- into the two components. We'd have to define some weird stand-alone
-- variant of 'Functor1' in order to map over the first parameter;
-- and we'd lose the ability to wrap up a 'Datum' as a final package,
-- without committing to it being a constructor or a pattern; But
-- other than those two things, it looks like a win!

-- | The intermediate components of a data constructor. The @(:$)@
-- types aren't really proper Hakaru types, so this data type is
-- designed to separate it out from the rest of the AST.
data Datum :: (Hakaru -> *) -> Hakaru -> * where
    Roll
        :: !(Datum ast (Code t ':$ 'HData t (Code t)))
        -> Datum ast ('HData t (Code t))
    Nil :: Datum ast ('[ '[] ] ':$ a)
    Cons
        :: !(Datum ast ('[ '[ x ] ] ':$ a))
        -> !(Datum ast ('[ xs ] ':$ a))
        -> Datum ast ('[ x ': xs ] ':$ a)
    Zero  :: !(Datum ast ('[ xs ] ':$ a)) -> Datum ast ((xs ': xss) ':$ a)
    Succ  :: !(Datum ast (xss ':$ a))     -> Datum ast ((xs ': xss) ':$ a)
    Konst :: ast b -> Datum ast ('[ '[ 'K b ] ] ':$ a)
    Ident :: ast a -> Datum ast ('[ '[ 'I   ] ] ':$ a)

-- BUG: deriving instance Eq   (Datum ast a)
-- BUG: deriving instance Read (Datum ast a)

instance Show1 ast => Show1 (Datum ast) where
    showsPrec1 p t =
        case t of
        Roll  d     -> showParen_1   p "Roll"  d
        Nil         -> showString      "Nil"
        Cons  d1 d2 -> showParen_11  p "Cons"  d1 d2
        Zero  d     -> showParen_1   p "Zero"  d
        Succ  d     -> showParen_1   p "Succ"  d
        Konst d     -> showParen_1   p "Konst" d
        Ident d     -> showParen_1   p "Ident" d

instance Show1 ast => Show (Datum ast a) where
    showsPrec = showsPrec1
    show      = show1

instance Functor1 Datum where
    fmap1 f (Roll  d)     = Roll  (fmap1 f d)
    fmap1 _ Nil           = Nil
    fmap1 f (Cons  d1 d2) = Cons  (fmap1 f d1) (fmap1 f d2)
    fmap1 f (Zero  d)     = Zero  (fmap1 f d)
    fmap1 f (Succ  d)     = Succ  (fmap1 f d)
    fmap1 f (Konst d)     = Konst (f d)
    fmap1 f (Ident d)     = Ident (f d)

instance Foldable1 Datum where
    foldMap1 f (Roll  d)     = foldMap1 f d
    foldMap1 _ Nil           = mempty
    foldMap1 f (Cons  d1 d2) = foldMap1 f d1 `mappend` foldMap1 f d2
    foldMap1 f (Zero  d)     = foldMap1 f d
    foldMap1 f (Succ  d)     = foldMap1 f d
    foldMap1 f (Konst d)     = f d
    foldMap1 f (Ident d)     = f d


----------------------------------------------------------------
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
data Pattern :: Hakaru -> * where
    -- | The \"don't care\" wildcard pattern.
    PWild :: Pattern a
    
    -- | A pattern variable.
    PVar  :: Pattern a
    
    -- TODO: equality patterns for Nat\/Int.
    -- Does it make sense to have equality patterns for Prob\/Real?

    -- | A data type constructor pattern.
    PDatum
        :: !(Datum Pattern ('HData t (Code t)))
        -> Pattern ('HData t (Code t))


-- BUG: deriving instance Eq   (Pattern a)
-- BUG: deriving instance Read (Pattern a)

instance Show1 Pattern where
    showsPrec1 p pat =
        case pat of
        PWild    -> showString    "PWild"
        PVar     -> showString    "PVar"
        PDatum d -> showParen_1 p "PDatum" d

instance Show (Pattern a) where
    showsPrec = showsPrec1
    show      = show1


-- TODO: move these pattern synonyms up to just the types @Datum ast _@, so we can reuse them both for patterns and constructors.

-- BUG: should we even bother making these into pattern synonyms?
-- We can't do it for any of the other derived patterns, so having
-- these ones just screws up the API. Of course, once we move to
-- GHC 7.10, then we're finally allowed to have polymorphic pattern
-- synonyms, so we can make the other ones work!
pattern PTrue  = (PDatum (Roll (Zero Nil)) :: Pattern HBool)
pattern PFalse = (PDatum (Roll (Succ Nil)) :: Pattern HBool)
pattern PUnit  = (PDatum (Roll Nil)        :: Pattern HUnit)

pPair :: Pattern a -> Pattern b -> Pattern (HPair a b)
pPair a b = PDatum (Roll (Cons (Konst a) (Konst b)))

pInl :: Pattern a -> Pattern (HEither a b)
pInl a = PDatum (Roll (Zero (Konst a)))

pInr :: Pattern b -> Pattern (HEither a b)
pInr a = PDatum (Roll (Succ (Konst a)))



-- TODO: a pretty infix syntax, like (:->) or something
-- TODO: this type is helpful for capturing the existential, if we ever end up keeping track of local binding environments; but other than that, it should be replaced\/augmented with a type for pattern automata, so we can optimize case analysis.
data Branch :: Hakaru -> (Hakaru -> *) -> Hakaru -> * where
    Branch
        :: {-exists Γ.-}
           !(Pattern a) {-Γ-}
        -> ast {-Γ-} b
        -> Branch a ast b

branchPattern :: Branch a ast b -> Pattern a
branchPattern (Branch p _) = p

branchBody :: Branch a ast b -> ast b
branchBody (Branch _ e) = e

-- BUG: deriving instance Eq   (Branch ast a b)
-- BUG: deriving instance Read (Branch ast a b)

instance Show1 ast => Show1 (Branch a ast) where
    showsPrec1 p (Branch pat e) =
        showParen (p > 9)
            ( showString "Branch "
            . showsPrec  11 pat
            . showString " "
            . showsPrec1 11 e
            )

instance Show1 ast => Show (Branch a ast b) where
    showsPrec = showsPrec1
    show      = show1

instance Functor1 (Branch a) where
    fmap1 f (Branch p e) = Branch p (f e)

instance Foldable1 (Branch a) where
    foldMap1 f (Branch _ e) = f e


----------------------------------------------------------------
-- TODO: define a well-formedness check for the ABT structure, since
-- we don't encode it into the Haskell types themselves. For clarity,
-- we do note the typing environments for the open terms via comments.
-- TODO: should we tag the @abt@ type to capture whether the use
-- sites must/must-not be 'Open' terms? Or is the well-formedness
-- check sufficient?
--
-- BUG: we need the 'Functor1' instance to be strict, in order to guaranteee timely throwing of exceptions in 'subst'.
data AST :: (Hakaru -> *) -> Hakaru -> * where

    -- -- Standard lambda calculus stuff
    -- We store a Proxy in Lam_, so Haskell needn't infer @a@ in
    -- the result. As far as Hakaru is concerned, we only ever try
    -- to check lambdas, never infer them.
    Lam_    :: !(Proxy a) -> ast {-a-} b -> AST ast ('HFun a b)
    App_    :: ast ('HFun a b) -> ast a -> AST ast b
    Let_    :: ast a -> ast {-a-} b -> AST ast b
    -- TODO: a general \"@let*@\" version of let-binding so we can have mutual recursion
    Fix_    :: ast {-a-} a -> AST ast a
    -- | Explicitly given type annotations. (For the other
    -- change-of-direction rule in bidirectional type checking.)
    -- N.B., storing a 'Proxy' isn't enough; we need the 'Sing'.
    Ann_    :: !(Sing a) -> ast a -> AST ast a


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
    -- TODO: add something like @SafeFrom_ :: Coercion a b -> ast b -> AST ast ('HMaybe a)@ so we can capture the safety of patterns like @if_ (0 <= x) (let x_ = unsafeFrom signed x in...) (...)@ Of course, since we're just going to do case analysis on the result; why not make it a binding form directly?
    -- TODO: we'll probably want some more general thing to capture these sorts of patterns. For example, in the default implementation of Uniform we see: @if_ (lo < x && x < hi) (... unsafeFrom_ signed (hi - lo) ...) (...)@

    -- TODO: do we really need this to be a binding form, or could it take a Hakaru function (HFun) for the second argument?
    Array_ :: ast 'HNat -> ast {-'HNat-} a -> AST ast ('HArray a)


    -- -- User-defined data types
    -- | A data constructor applied to some expressions.
    Datum_
        :: Datum ast ('HData con (Code con))
        -> AST   ast ('HData con (Code con))
    
    -- | Generic case-analysis (via ABTs and Structural Focalization).
    Case_ :: ast a -> [Branch a ast b] -> AST ast b


    -- -- Mochastic stuff
    -- TODO: should Dirac move back here?
    -- TODO: should DP_, Plate_, and Chain_ move there?
    -- | Primitive operators which generate measures.
    Measure_ :: !(Measure a) -> AST ast a
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
        :: ast ('HArray ('HFun s ('HMeasure (HPair a s))))
        -> AST ast ('HFun s ('HMeasure (HPair ('HArray a) s)))


    -- Lub
    -- TODO: should this really be part of the AST?
    Lub_ :: ast a -> ast a -> AST ast a
    Bot_ :: AST ast a


----------------------------------------------------------------
-- N.B., having a @singAST :: AST ast a -> Sing a@ doesn't make sense: That's what 'inferType' is for, but not all terms can be inferred; some must be checked... Similarly, we can't derive Read, since that's what typechecking is all about.

-- BUG: deriving instance (forall b. Eq (ast b)) => Eq (AST ast a)

showParen_0 :: Show a => Int -> String -> a -> ShowS
showParen_0 p s e =
    showParen (p > 9)
        ( showString s
        . showString " "
        . showsPrec 11 e
        )

showParen_1 :: Show1 a => Int -> String -> a i -> ShowS
showParen_1 p s e =
    showParen (p > 9)
        ( showString s
        . showString " "
        . showsPrec1 11 e
        )

showParen_01 :: (Show b, Show1 a) => Int -> String -> b -> a i -> ShowS
showParen_01 p s e1 e2 =
    showParen (p > 9)
        ( showString s
        . showString " "
        . showsPrec  11 e1
        . showString " "
        . showsPrec1 11 e2
        )

showParen_11 :: (Show1 a) => Int -> String -> a i -> a j -> ShowS
showParen_11 p s e1 e2 =
    showParen (p > 9)
        ( showString s
        . showString " "
        . showsPrec1 11 e1
        . showString " "
        . showsPrec1 11 e2
        )

showParen_111 :: (Show1 a) => Int -> String -> a i -> a j -> a k -> ShowS
showParen_111 p s e1 e2 e3 =
    showParen (p > 9)
        ( showString s
        . showString " "
        . showsPrec1 11 e1
        . showString " "
        . showsPrec1 11 e2
        . showString " "
        . showsPrec1 11 e3
        )

instance Show1 ast => Show1 (AST ast) where
    showsPrec1 p t =
        case t of
        Lam_    a  e         -> showParen_01  p "Lam_"    a  e
        App_    e1 e2        -> showParen_11  p "App_"    e1 e2
        Let_    e1 e2        -> showParen_11  p "Let_"    e1 e2
        Fix_    e            -> showParen_1   p "Fix_"    e
        {- -- BUG: "Could not deduce (Show (Sing i))" ??
        Ann_    a e          -> showParen_01  p "Ann_"    a  e
        -}
        PrimOp_ o            -> showParen_0   p "PrimOp_" o
        NaryOp_ o es         ->
            showParen (p > 9)
                ( showString "NaryOp_ "
                . showsPrec  11 o
                . showString " "
                . showParen True
                    ( showString "Seq.fromList "
                    . showList1 (F.toList es)
                    )
                )
        Integrate_  e1 e2 e3 -> showParen_111 p "Integrate_"  e1 e2 e3
        Summate_    e1 e2 e3 -> showParen_111 p "Summate_"    e1 e2 e3
        Value_      v        -> showParen_0   p "Value_"      v
        CoerceTo_   c e      -> showParen_01  p "CoerceTo_"   c e
        UnsafeFrom_ c e      -> showParen_01  p "UnsafeFrom_" c e
        Array_      e1 e2    -> showParen_11  p "Array_"      e1 e2
        Datum_      d        -> showParen_1   p "Datum_"      d
        Case_       e bs     ->
            showParen (p > 9)
                ( showString "Case_ "
                . showsPrec1 11 e
                . showString " "
                . showList1 bs
                )
        Measure_   o         -> showParen_0   p "Measure_" o
        Bind_      e1 e2     -> showParen_11  p "Bind_"   e1 e2
        Superpose_ pes       -> error "TODO: show Superpose_"
        Dp_        e1 e2     -> showParen_11  p "Dp_"     e1 e2
        Plate_     e         -> showParen_1   p "Plate_"  e
        Chain_     e         -> showParen_1   p "Chain_"  e
        Lub_       e1 e2     -> showParen_11  p "Lub_"    e1 e2
        Bot_                 -> showString      "Bot_"

instance Show1 ast => Show (AST ast a) where
    showsPrec = showsPrec1
    show      = show1


----------------------------------------------------------------
instance Functor1 AST where
    fmap1 f (Lam_        p  e)     = Lam_        p      (f e)
    fmap1 f (App_        e1 e2)    = App_        (f e1) (f e2)
    fmap1 f (Let_        e1 e2)    = Let_        (f e1) (f e2)
    fmap1 f (Fix_        e)        = Fix_        (f e)
    fmap1 f (Ann_        p  e)     = Ann_        p      (f e)
    fmap1 _ (PrimOp_     o)        = PrimOp_     o
    fmap1 f (NaryOp_     o  es)    = NaryOp_     o      (fmap f es)
    fmap1 f (Integrate_  e1 e2 e3) = Integrate_  (f e1) (f e2) (f e3)
    fmap1 f (Summate_    e1 e2 e3) = Summate_    (f e1) (f e2) (f e3)
    fmap1 _ (Value_      v)        = Value_      v
    fmap1 f (CoerceTo_   c  e)     = CoerceTo_   c      (f e)
    fmap1 f (UnsafeFrom_ c  e)     = UnsafeFrom_ c      (f e)
    fmap1 f (Array_      e1 e2)    = Array_      (f e1) (f e2)
    fmap1 f (Datum_      d)        = Datum_      (fmap1 f d)
    fmap1 f (Case_       e  bs)    = Case_       (f e)  (map (fmap1 f) bs)
    fmap1 _ (Measure_    o)        = Measure_    o
    fmap1 f (Bind_       e1 e2)    = Bind_       (f e1) (f e2)
    fmap1 f (Superpose_  pes)      = Superpose_  (map (f *** f) pes)
    fmap1 f (Dp_         e1 e2)    = Dp_         (f e1) (f e2)
    fmap1 f (Plate_      e)        = Plate_      (f e)
    fmap1 f (Chain_      e)        = Chain_      (f e)
    fmap1 f (Lub_        e1 e2)    = Lub_        (f e1) (f e2)
    fmap1 _ Bot_                   = Bot_


----------------------------------------------------------------
instance Foldable1 AST where
    foldMap1 f (Lam_        _  e)     = f e
    foldMap1 f (App_        e1 e2)    = f e1 `mappend` f e2
    foldMap1 f (Let_        e1 e2)    = f e1 `mappend` f e2
    foldMap1 f (Fix_        e)        = f e
    foldMap1 f (Ann_        _  e)     = f e
    foldMap1 _ (PrimOp_     _)        = mempty
    foldMap1 f (NaryOp_     _  es)    = F.foldMap f es
    foldMap1 f (Integrate_  e1 e2 e3) = f e1 `mappend` f e2 `mappend` f e3
    foldMap1 f (Summate_    e1 e2 e3) = f e1 `mappend` f e2 `mappend` f e3
    foldMap1 _ (Value_ _)             = mempty
    foldMap1 f (CoerceTo_   _  e)     = f e
    foldMap1 f (UnsafeFrom_ _  e)     = f e
    foldMap1 f (Array_      e1 e2)    = f e1 `mappend` f e2
    foldMap1 f (Datum_      d)        = foldMap1 f d
    foldMap1 f (Case_       e  bs)    = f e  `mappend` F.foldMap (f . branchBody) bs
    foldMap1 _ (Measure_    _)        = mempty
    foldMap1 f (Bind_       e1 e2)    = f e1 `mappend` f e2
    foldMap1 f (Superpose_  pes)      = F.foldMap (\(e1,e2) -> f e1 `mappend` f e2) pes
    foldMap1 f (Dp_         e1 e2)    = f e1 `mappend` f e2
    foldMap1 f (Plate_      e)        = f e
    foldMap1 f (Chain_      e)        = f e
    foldMap1 f (Lub_        e1 e2)    = f e1 `mappend` f e2
    foldMap1 _ Bot_                   = mempty

----------------------------------------------------------------
----------------------------------------------------------- fin.
