-- TODO: <https://git-scm.com/book/en/v2/Git-Branching-Basic-Branching-and-Merging>
{-# LANGUAGE CPP
           , DataKinds
           , PolyKinds
           , GADTs
           , StandaloneDeriving
           , TypeOperators
           , TypeFamilies
           #-}

{-# OPTIONS_GHC -Wall -fwarn-tabs #-}
----------------------------------------------------------------
--                                                    2015.10.22
-- |
-- Module      :  Language.Hakaru.Syntax.AST
-- Copyright   :  Copyright (c) 2015 the Hakaru team
-- License     :  BSD3
-- Maintainer  :  wren@community.haskell.org
-- Stability   :  experimental
-- Portability :  GHC-only
--
-- The generating functor for the raw syntax, along with various
-- helper types. For a more tutorial sort of introduction to how
-- things are structured here and in "Language.Hakaru.Syntax.ABT",
-- see <http://winterkoninkje.dreamwidth.org/103978.html>
--
-- TODO: are we finally at the place where we can get rid of all
-- those annoying underscores?
--
-- TODO: what is the runtime cost of storing all these dictionary
-- singletons? For existential type variables, it should be the
-- same as using a type class constraint; but for non-existential
-- type variables it'll, what, double the size of the AST?
----------------------------------------------------------------
module Language.Hakaru.Syntax.AST
    (
    -- * Syntactic forms
      SCon(..)
    , SArgs(..)
    , AST(..)
    -- * Operators
    , LC, LCs, UnLCs
    , LC_(..)
    , NaryOp(..)
    , PrimOp(..)
    , MeasureOp(..)
    -- * Constant values
    , Value(..)
    ) where

import           Data.Sequence (Seq)
import qualified Data.Foldable as F
#if __GLASGOW_HASKELL__ < 710
import Data.Monoid             hiding (Sum)
#endif
import Control.Arrow           ((***))
import Data.Number.LogFloat    (LogFloat)

import Language.Hakaru.Syntax.Nat
import Language.Hakaru.Syntax.IClasses
import Language.Hakaru.Syntax.DataKind
import Language.Hakaru.Syntax.Sing
import Language.Hakaru.Syntax.HClasses
import Language.Hakaru.Syntax.Coercion
import Language.Hakaru.Syntax.Datum

----------------------------------------------------------------
----------------------------------------------------------------
-- TODO: use 'Integer' instead of 'Int', 'Natural' instead of 'Nat', and 'Rational' instead of 'LogFloat' and 'Double'.

-- TODO: is the restriction to ground terms too much? Would it be enough to just consider closed normal forms?

-- BUG: even though the 'Datum' type has a single constructor, we get a warning about not being able to UNPACK it in 'VDatum'...

-- | Constant values for primitive numeric types and user-defined
-- data-types. In addition to being normal forms, these are also
-- ground terms: that is, not only are they closed (i.e., no free
-- variables), they also have no bound variables and thus no binding
-- forms. Hence, we do not include lambdas nor arrays, even though
-- they can be closed normal forms.
data Value :: Hakaru -> * where
    VNat   :: {-# UNPACK #-} !Nat                      -> Value 'HNat
    VInt   :: {-# UNPACK #-} !Int                      -> Value 'HInt
    VProb  :: {-# UNPACK #-} !LogFloat                 -> Value 'HProb
    VReal  :: {-# UNPACK #-} !Double                   -> Value 'HReal
    VDatum :: {-# UNPACK #-} !(Datum Value (HData' t)) -> Value (HData' t)

instance Eq1 Value where
    eq1 (VNat   v1) (VNat   v2) = v1 == v2
    eq1 (VInt   v1) (VInt   v2) = v1 == v2
    eq1 (VProb  v1) (VProb  v2) = v1 == v2
    eq1 (VReal  v1) (VReal  v2) = v1 == v2
    eq1 (VDatum v1) (VDatum v2) = v1 `eq1` v2
    eq1 _           _           = False

instance Eq (Value a) where
    (==) = eq1

-- TODO: instance Read (Value a)

instance Show1 Value where
    showsPrec1 p t =
        case t of
        VNat   v -> showParen_0 p "VNat"   v
        VInt   v -> showParen_0 p "VInt"   v
        VProb  v -> showParen_0 p "VProb"  v
        VReal  v -> showParen_0 p "VReal"  v
        VDatum v -> showParen_1 p "VDatum" v

instance Show (Value a) where
    showsPrec = showsPrec1
    show      = show1

----------------------------------------------------------------
-- TODO: helper functions for splitting NaryOp_ into components to group up like things. (e.g., grouping all the Values together so we can do constant propagation)

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
    -- N.B., even though 'Iff' is associative (in Boolean algebras),
    -- we should not support n-ary uses in our *surface* syntax.
    -- Because it's too easy for folks to confuse "a <=> b <=> c"
    -- with "(a <=> b) /\ (b <=> c)".
    Iff  :: NaryOp HBool -- == Not (Xor x y)

    -- These two don't necessarily have identity elements; thus,
    -- @NaryOp_ Min []@ and @NaryOp_ Max []@ may not be well-defined...
    -- TODO: check for those cases!
    Min  :: !(HOrd a) -> NaryOp a
    Max  :: !(HOrd a) -> NaryOp a

    Sum  :: !(HSemiring a) -> NaryOp a
    Prod :: !(HSemiring a) -> NaryOp a

    {-
    GCD  :: !(GCD_Domain a) -> NaryOp a
    LCM  :: !(GCD_Domain a) -> NaryOp a
    -}

deriving instance Eq   (NaryOp a)
-- TODO: instance Read (NaryOp a)
deriving instance Show (NaryOp a)

----------------------------------------------------------------

-- TODO: should we define our own datakind for @([Hakaru], Hakaru)@ or perhaps for the @/\a -> ([a], Hakaru)@ part of it?

-- | Locally closed values (i.e., not binding forms) of a given type.
-- TODO: come up with a better name
type LC (a :: Hakaru) = '( '[], a )

-- BUG: how to declare that these are inverses?
type family LCs (xs :: [Hakaru]) :: [([Hakaru], Hakaru)] where
    LCs '[]       = '[]
    LCs (x ': xs) = LC x ': LCs xs

type family UnLCs (xs :: [([Hakaru], Hakaru)]) :: [Hakaru] where
    UnLCs '[]                  = '[]
    UnLCs ( '( '[], x ) ': xs) = x ': UnLCs xs


-- | Simple primitive functions, and constants. N.B., nothing in
-- here should produce or consume things of @HMeasure@ type (except
-- perhaps in a totally polymorphic way).
data PrimOp :: [Hakaru] -> Hakaru -> * where

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
    Not  :: PrimOp '[ HBool ] HBool
    -- And, Or, Xor, Iff
    Impl :: PrimOp '[ HBool, HBool ] HBool
    -- Impl x y == Or (Not x) y
    Diff :: PrimOp '[ HBool, HBool ] HBool
    -- Diff x y == Not (Impl x y)
    Nand :: PrimOp '[ HBool, HBool ] HBool
    -- Nand aka Alternative Denial, Sheffer stroke
    Nor  :: PrimOp '[ HBool, HBool ] HBool
    -- Nor aka Joint Denial, aka Quine dagger, aka Pierce arrow
    --
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
    Pi    :: PrimOp '[] 'HProb -- TODO: maybe make this HContinuous polymorphic?
    -- TODO: if we're going to bother naming the hyperbolic ones, why not also name /a?(csc|sec|cot)h?/ eh?
    -- TODO: capture more domain information in these types?
    Sin   :: PrimOp '[ 'HReal ] 'HReal
    Cos   :: PrimOp '[ 'HReal ] 'HReal
    Tan   :: PrimOp '[ 'HReal ] 'HReal
    Asin  :: PrimOp '[ 'HReal ] 'HReal
    Acos  :: PrimOp '[ 'HReal ] 'HReal
    Atan  :: PrimOp '[ 'HReal ] 'HReal
    Sinh  :: PrimOp '[ 'HReal ] 'HReal
    Cosh  :: PrimOp '[ 'HReal ] 'HReal
    Tanh  :: PrimOp '[ 'HReal ] 'HReal
    Asinh :: PrimOp '[ 'HReal ] 'HReal
    Acosh :: PrimOp '[ 'HReal ] 'HReal
    Atanh :: PrimOp '[ 'HReal ] 'HReal


    -- -- Other Real\/Prob-valued operators
    -- N.B., we only give the safe\/exact versions here. The old
    -- more lenient versions now require explicit coercions. Some
    -- of those coercions are safe, but others are not. This way
    -- we're explicit about where things can fail.
    -- N.B., we also have @NatPow{'HReal} :: 'HReal -> 'HNat -> 'HReal@,
    -- but non-integer real powers of negative reals are not real numbers!
    -- TODO: may need @SafeFrom_@ in order to branch on the input
    -- in order to provide the old unsafe behavior.
    RealPow   :: PrimOp '[ 'HProb, 'HReal ] 'HProb
    -- ComplexPow :: PrimOp '[ 'HProb, 'HComplex ] 'HComplex
    -- is uniquely well-defined. Though we may want to implement
    -- it via @r**z = ComplexExp (z * RealLog r)@
    -- Defining @HReal -> HComplex -> HComplex@ requires either
    -- multivalued functions, or a choice of complex logarithm and
    -- making it discontinuous.
    Exp       :: PrimOp '[ 'HReal ] 'HProb
    Log       :: PrimOp '[ 'HProb ] 'HReal
    -- TODO: Log1p, Expm1
    Infinity  :: PrimOp '[] 'HProb -- TODO: maybe make this HContinuous polymorphic?
    NegativeInfinity :: PrimOp '[] 'HReal -- TODO: maybe replace this by @negate (coerceTo signed $ Infinity)@ ?
    -- TODO: add Factorial as the appropriate type restriction of GammaFunc?
    GammaFunc :: PrimOp '[ 'HReal ] 'HProb
    BetaFunc  :: PrimOp '[ 'HProb, 'HProb ] 'HProb


    -- -- Continuous and discrete integration.
    -- TODO: turn these back into binders in order to avoid the need for lambdas! Of course, to do that, they have to move out of PrimOp and into SCon (or somewhere)
    --
    -- TODO: make Integrate and Summate polymorphic, so that if the
    -- two inputs are HProb then we know the function must be over
    -- HProb\/HNat too. More generally, if the first input is HProb
    -- (since the second input is assumed to be greater than the
    -- first); though that would be a bit ugly IMO.
    Integrate :: PrimOp '[ 'HReal, 'HReal, 'HReal ':-> 'HProb ] 'HProb
    -- TODO: the high and low bounds *should* be HInt. The only reason we use HReal is so that we can have infinite summations. Once we figure out a way to handle infinite bounds here, we can make the switch
    Summate   :: PrimOp '[ 'HReal, 'HReal, 'HInt  ':-> 'HProb ] 'HProb


    -- -- -- Here we have the /polymorphic/ operators
    -- -- Array stuff
    -- TODO: do these really belong here (as PrimOps) or should they be in their own place (e.g., \"ArrayOp\")?
    -- HACK: is there any way we can avoid storing the Sing values here, while still implementing 'sing_PrimOp'? Should we have a Hakaru class for the types which can be stored in arrays? might not be a crazy idea...
    Index  :: !(Sing a) -> PrimOp '[ 'HArray a, 'HNat ] a
    Size   :: !(Sing a) -> PrimOp '[ 'HArray a ] 'HNat
    -- The first argument should be a monoid, but we don't enforce
    -- that; it's the user's responsibility.
    Reduce :: !(Sing a) -> PrimOp '[ a ':-> a ':-> a, a, 'HArray a ] a
    -- TODO: would it make sense to have a specialized version for when the first argument is some \"Op\", in order to avoid the need for lambdas?


    -- -- HEq and HOrd operators
    -- TODO: equality doesn't make constructive sense on the reals...
    -- would it be better to constructivize our notion of total ordering?
    -- TODO: should we have LessEq as a primitive, rather than treating it as a macro?
    Equal :: !(HEq  a) -> PrimOp '[ a, a ] HBool
    Less  :: !(HOrd a) -> PrimOp '[ a, a ] HBool


    -- -- HSemiring operators (the non-n-ary ones)
    NatPow :: !(HSemiring a) -> PrimOp '[ a, 'HNat ] a
    -- TODO: would it help to have a specialized version for when
    -- we happen to know that the 'HNat is a Value? Same goes for
    -- the other powers\/roots
    --
    -- TODO: add a specialized version which returns NonNegative
    -- when the power is even? N.B., be sure not to actually constrain
    -- it to HRing (necessary for calling it \"NonNegative\")


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
    Negate :: !(HRing a) -> PrimOp '[ a ] a
    Abs    :: !(HRing a) -> PrimOp '[ a ] (NonNegative a)
    -- cf., <https://mail.haskell.org/pipermail/libraries/2013-April/019694.html>
    -- cf., <https://en.wikipedia.org/wiki/Sign_function#Complex_signum>
    -- Should we have Maple5's \"csgn\" as well as the usual \"sgn\"?
    -- Also note that the \"generalized signum\" anticommutes with Dirac delta!
    Signum :: !(HRing a) -> PrimOp '[ a ] a
    -- Law: x = coerceTo_ signed (abs_ x) * signum x
    -- More strictly/exactly, the result of Signum should be either
    -- zero or an @a@-unit value. For Int and Real, the units are
    -- +1 and -1. For Complex, the units are any point on the unit
    -- circle. For vectors, the units are any unit vector. Thus,
    -- more generally:
    -- Law : x = coerceTo_ signed (abs_ x) `scaleBy` signum x
    -- TODO: would it be worth defining the associated type of unit values for @a@? Probably...
    -- TODO: are there any salient types which support abs\/norm but
    -- do not have all units and thus do not support signum\/normalize?


    -- -- HFractional operators
    Recip :: !(HFractional a) -> PrimOp '[ a ] a
    -- generates macro: IntPow


    -- -- HRadical operators
    NatRoot :: !(HRadical a) -> PrimOp '[ a, 'HNat ] a
    -- generates macros: Sqrt, NonNegativeRationalPow, and RationalPow


    -- -- HContinuous operators
    -- TODO: what goes here, if anything? cf., <https://en.wikipedia.org/wiki/Closed-form_expression#Comparison_of_different_classes_of_expressions>
    Erf :: !(HContinuous a) -> PrimOp '[ a ] a
    -- TODO: make Pi and Infinity HContinuous-polymorphic so that we can avoid the explicit coercion? Probably more mess than benefit.


deriving instance Eq   (PrimOp args a)
-- TODO: instance Read (PrimOp args a)
deriving instance Show (PrimOp args a)


----------------------------------------------------------------
-- | Primitive operators to produce, consume, or transform
-- distributions\/measures. This corresponds to the old @Mochastic@
-- class, except that 'MBind' and 'Superpose_' are handled elsewhere
-- since they are not simple operators.
data MeasureOp :: [Hakaru] -> Hakaru -> * where
    -- TODO: Should Dirac move into SCon to be with MBind? Might help with removing the Sing value...
    -- HACK: is there any way we can avoid storing the Sing value here, while still implementing 'sing_MeasureOp'? Should we have a Hakaru class for the types which can be measurable? might not be a crazy idea...
    Dirac :: !(Sing a) -> MeasureOp '[ a ] ('HMeasure a)

    Lebesgue    :: MeasureOp '[]                 ('HMeasure 'HReal)
    Counting    :: MeasureOp '[]                 ('HMeasure 'HInt)
    Categorical :: MeasureOp '[ 'HArray 'HProb ] ('HMeasure 'HNat)
    -- TODO: make Uniform polymorphic, so that if the two inputs are HProb then we know the measure must be over HProb too. More generally, if the first input is HProb (since the second input is assumed to be greater thant he first); though that would be a bit ugly IMO.
    Uniform     :: MeasureOp '[ 'HReal, 'HReal ] ('HMeasure 'HReal)
    Normal      :: MeasureOp '[ 'HReal, 'HProb ] ('HMeasure 'HReal)
    Poisson     :: MeasureOp '[ 'HProb         ] ('HMeasure 'HNat)
    Gamma       :: MeasureOp '[ 'HProb, 'HProb ] ('HMeasure 'HProb)
    Beta        :: MeasureOp '[ 'HProb, 'HProb ] ('HMeasure 'HProb)

    -- HACK: is there any way we can avoid storing the Sing values here, while still implementing 'sing_MeasureOp'? Should we have a Hakaru class for the types which can be measurable? might not be a crazy idea...
    DirichletProcess
        :: !(Sing a)
        -> MeasureOp '[ 'HProb, 'HMeasure a ] ('HMeasure ('HMeasure a))
    -- TODO: unify Plate and Chain as @sequence@ a~la traversable?
    Plate
        :: !(Sing a)
        -> MeasureOp '[ 'HArray ('HMeasure a) ] ('HMeasure ('HArray a))
    -- TODO: if we swap the order of arguments to 'Chain', we could change the functional argument to be a binding form in order to avoid the need for lambdas. It'd no longer be trivial to see 'Chain' as an instance of @sequence@, but might be worth it... Of course, we also need to handle the fact that it's an array of transition functions; i.e., we could do:
    -- > chain n s0 $ \i s -> do {...}
    Chain
        :: !(Sing s)
        -> !(Sing a)
        -> MeasureOp
            '[ 'HArray (s ':-> 'HMeasure (HPair a s))
            ,  s
            ] ('HMeasure (HPair ('HArray a) s))


deriving instance Eq   (MeasureOp args a)
-- TODO: instance Read (MeasureOp args a)
deriving instance Show (MeasureOp args a)


----------------------------------------------------------------
----------------------------------------------------------------
-- N.B., the precedence of (:$) must be lower than (:*).
-- N.B., if these are changed, then be sure to update the Show instances
infix  4 :$ -- Chosen to be at the same precedence as (<$>) rather than ($)
infixr 5 :* -- Chosen to match (:)


-- | The constructor of a '(:$)' node in the 'AST'. Each of these
-- constructors denotes a \"normal\/standard\/basic\" syntactic
-- form (i.e., a generalized quantifier). In the literature, these
-- syntactic forms are sometimes called \"operators\", but we avoid
-- calling them that so as not to introduce confusion vs 'PrimOp'
-- etc. Instead we use the term \"operator\" to refer to any primitive
-- function or constant; that is, non-binding syntactic forms. Also
-- in the literature, the 'SCon' type itself is usually called the
-- \"signature\" of the term language. However, we avoid calling
-- it that since our 'AST' has constructors other than just @(:$)@,
-- so 'SCon' does not give a complete signature for our terms.
--
-- The main reason for breaking this type out and using it in
-- conjunction with '(:$)' and 'SArgs' is so that we can easily
-- pattern match on /fully saturated/ nodes. For example, we want
-- to be able to match @MeasureOp_ Uniform :$ lo :* hi :* End@
-- without needing to deal with 'App_' nodes nor 'viewABT'.
data SCon :: [([Hakaru], Hakaru)] -> Hakaru -> * where

    -- -- Standard lambda calculus stuff
    Lam_ :: SCon '[ '( '[ a ], b ) ] (a ':-> b)
    App_ :: SCon '[ LC (a ':-> b ), LC a ] b
    Let_ :: SCon '[ LC a, '( '[ a ], b ) ] b
    -- TODO: a general \"@let*@\" version of let-binding so we can have mutual recursion
    -- TODO: get rid of 'Fix_' and introduce induction principles for each HData instead.
    Fix_ :: SCon '[ '( '[ a ], a ) ] a

    -- -- Type munging
    -- | Explicitly given type annotations. (For the other
    -- change-of-direction rule in bidirectional type checking.)
    -- N.B., storing a 'Proxy' isn't enough; we need the 'Sing'.
    Ann_        :: !(Sing a)       -> SCon '[ LC a ] a
    CoerceTo_   :: !(Coercion a b) -> SCon '[ LC a ] b
    UnsafeFrom_ :: !(Coercion a b) -> SCon '[ LC b ] a
    -- TODO: add something like @SafeFrom_ :: Coercion a b -> abt b -> AST abt ('HMaybe a)@ so we can capture the safety of patterns like @if_ (0 <= x) (let x_ = unsafeFrom signed x in...) (...)@ Of course, since we're just going to do case analysis on the result; why not make it a binding form directly?
    -- TODO: we'll probably want some more general thing to capture these sorts of patterns. For example, in the default implementation of Uniform we see: @if_ (lo < x && x < hi) (... unsafeFrom_ signed (hi - lo) ...) (...)@

    -- HACK: we must add the constraints that 'LCs' and 'UnLCs' are inverses, so that we have those in scope when doing case analysis (e.g., in TypeCheck.hs).
    -- As for this file itself, we can get it to typecheck by using 'UnLCs' in the argument rather than 'LCs' in the result; trying to do things the other way results in type inference issues in the typeclass instances for 'SCon'
    PrimOp_
        :: (typs ~ UnLCs args, args ~ LCs typs)
        => !(PrimOp typs a) -> SCon args a
    MeasureOp_
        :: (typs ~ UnLCs args, args ~ LCs typs)
        => !(MeasureOp typs a) -> SCon args a
    -- TODO: should Dirac move back here?
    -- TODO: Does this one need to have a Sing value for @a@ (or @b@)?
    MBind :: SCon
        '[ LC ('HMeasure a)
        ,  '( '[ a ], 'HMeasure b)
        ] ('HMeasure b)


    -- -- Internalized program transformations
    -- TODO: do these belong in their own place?
    --
    -- We generally want to evaluate these away at compile-time,
    -- but sometimes we may be stuck with a few unresolved things
    -- for open terms.

    -- TODO: did we want the singleton @a@ argument back?
    Expect :: SCon '[ LC ('HMeasure a), '( '[ a ], 'HProb) ] 'HProb

    -- TODO: implement a \"change of variables\" program transformation
    -- to map, say, @Lam_ x. blah (Expect x)@ into @Lam x'. blah x'@.
    -- Or, perhaps rather, transform it into @Lam_ x. App_ (Lam_ x'. blah x') (Expect x)@.

    -- TODO: add the four ops for disingetration


-- TODO: instance Eq   (SCon args a)
-- TODO: instance Read (SCon args a)
deriving instance Show (SCon args a)


----------------------------------------------------------------
-- TODO: ideally we'd like to make SArgs totally flat, like tuples and arrays. Is there a way to do that with data families?
-- TODO: is there any good way to reuse 'List1' instead of defining 'SArgs' (aka @List2@)?

-- TODO: come up with a better name for 'End'
-- | The arguments to a '(:$)' node in the 'AST'; that is, a list
-- of ASTs, where the whole list is indexed by a (type-level) list
-- of the indices of each element.
data SArgs :: ([Hakaru] -> Hakaru -> *) -> [([Hakaru], Hakaru)] -> *
    where
    End :: SArgs abt '[]
    (:*) :: !(abt vars a)
        -> !(SArgs abt args)
        -> SArgs abt ( '(vars, a) ': args)

-- TODO: instance Read (SArgs abt args)

instance Show2 abt => Show1 (SArgs abt) where
    showsPrec1 _ End       = showString "End"
    showsPrec1 p (e :* es) =
        showParen (p > 5)
            ( showsPrec2 (p+1) e
            . showString " :* "
            . showsPrec1 (p+1) es
            )

instance Show2 abt => Show (SArgs abt args) where
    showsPrec = showsPrec1
    show      = show1

instance Eq2 abt => Eq1 (SArgs abt) where
    eq1 End       End       = True
    eq1 (x :* xs) (y :* ys) = eq2 x y && eq1 xs ys
    eq1 _         _         = False

instance Eq2 abt => Eq (SArgs abt args) where
    (==) = eq1

instance Functor21 SArgs where
    fmap21 f (e :* es) = f e :* fmap21 f es
    fmap21 _ End       = End

instance Foldable21 SArgs where
    foldMap21 f (e :* es) = f e `mappend` foldMap21 f es
    foldMap21 _ End       = mempty


----------------------------------------------------------------
data AST :: ([Hakaru] -> Hakaru -> *) -> Hakaru -> * where

    -- | Simple syntactic forms (i.e., generalized quantifiers)
    (:$) :: !(SCon args a) -> !(SArgs abt args) -> AST abt a

    -- | N-ary operators
    NaryOp_ :: !(NaryOp a) -> !(Seq (abt '[] a)) -> AST abt a

    -- TODO: 'Value_', 'Empty_', 'Array_', and 'Datum_' are generalized quantifiers (to the same extent that 'Ann_', 'CoerceTo_', and 'UnsafeFrom_' are). Should we move them into 'SCon' just for the sake of minimizing how much lives in 'AST'? Or are they unique enough to be worth keeping here?

    -- | Constant values
    Value_ :: !(Value a) -> AST abt a

    -- We have the constructors for arrays here, so that they're grouped together with our other constructors 'Value_' and 'Datum_'. Though, if we introduce a new @ArrayOp@ type, these should probably move there
    Empty_ :: AST abt ('HArray a)
    -- TODO: do we really need this to be a binding form, or could it take a Hakaru function for the second argument?
    Array_ :: !(abt '[] 'HNat) -> !(abt '[ 'HNat ] a) -> AST abt ('HArray a)

    -- -- User-defined data types
    -- BUG: even though the 'Datum' type has a single constructor, we get a warning about not being able to UNPACK it in 'Datum_'...
    -- | A data constructor applied to some expressions. N.B., this
    -- definition only accounts for data constructors which are
    -- fully saturated. Unsaturated constructors will need to be
    -- eta-expanded.
    Datum_
        :: {-# UNPACK #-} !(Datum (abt '[]) (HData' t))
        -> AST abt (HData' t)

    -- | Generic case-analysis (via ABTs and Structural Focalization).
    Case_ :: !(abt '[] a) -> [Branch a abt b] -> AST abt b

    -- | Linear combinations of measures.
    Superpose_
        :: [(abt '[] 'HProb, abt '[] ('HMeasure a))]
        -> AST abt ('HMeasure a)

    -- | Arbitrary choice between equivalent programs
    Lub_ :: [abt '[] a] -> AST abt a


----------------------------------------------------------------
-- N.B., having a @singAST :: AST abt a -> Sing a@ doesn't make
-- sense: That's what 'inferType' is for, but not all terms can be
-- inferred; some must be checked... Similarly, we can't derive
-- Read, since that's what typechecking is all about.

-- TODO: instance (Eq1 abt) => Eq1 (AST abt)

-- HACK: so we can print 'Datum_' nodes. Namely, we need to derive @Show1 (abt '[])@ from @Show2 abt@. Alas, we'll also need this same hack for lowering @Eq2 abt@ to @Eq1 (abt '[])@, etc...
newtype LC_ (abt :: [Hakaru] -> Hakaru -> *) (a :: Hakaru) =
    LC_ { unLC_ :: abt '[] a }

instance Show2 abt => Show1 (LC_ abt) where
    showsPrec1 p = showsPrec2 p . unLC_
    show1        = show2        . unLC_


instance Show2 abt => Show1 (AST abt) where
    showsPrec1 p t =
        case t of
        o :$ es ->
            showParen (p > 4)
                ( showsPrec  (p+1) o
                . showString " :* "
                . showsPrec1 (p+1) es
                )
        NaryOp_ o es ->
            showParen (p > 9)
                ( showString "NaryOp_ "
                . showsPrec  11 o
                . showString " "
                . showParen True
                    ( showString "Seq.fromList "
                    . showList2 (F.toList es)
                    )
                )
        Value_ v        -> showParen_0   p "Value_" v
        Empty_          -> showString      "Empty_"
        Array_ e1 e2    -> showParen_22  p "Array_" e1 e2
        Datum_ d        -> showParen_1   p "Datum_" (fmap11 LC_ d)
        Case_  e bs     ->
            showParen (p > 9)
                ( showString "Case_ "
                . showsPrec2 11 e
                . showString " "
                . showList1 bs
                )
        Superpose_ pes ->
            showParen (p > 9)
                ( showString "Superpose_ "
                . showListWith
                    (\(e1,e2) -> showTuple [shows2 e1, shows2 e2])
                    pes
                )
        Lub_ es ->
            showParen (p > 9)
                ( showString "Lub_ "
                . showList2 es
                )

instance Show2 abt => Show (AST abt a) where
    showsPrec = showsPrec1
    show      = show1


----------------------------------------------------------------
instance Functor21 AST where
    fmap21 f (o :$ es)              = o :$ fmap21 f es
    fmap21 f (NaryOp_     o  es)    = NaryOp_     o      (fmap f es)
    fmap21 _ (Value_      v)        = Value_      v
    fmap21 _ Empty_                 = Empty_
    fmap21 f (Array_      e1 e2)    = Array_      (f e1) (f e2)
    fmap21 f (Datum_      d)        = Datum_      (fmap11 f d)
    fmap21 f (Case_       e  bs)    = Case_       (f e)  (map (fmap21 f) bs)
    fmap21 f (Superpose_  pes)      = Superpose_  (map (f *** f) pes)
    fmap21 f (Lub_        es)       = Lub_        (map f es)


----------------------------------------------------------------
instance Foldable21 AST where
    foldMap21 f (_ :$ es)              = foldMap21 f es
    foldMap21 f (NaryOp_     _  es)    = F.foldMap f es
    foldMap21 _ (Value_ _)             = mempty
    foldMap21 _ Empty_                 = mempty
    foldMap21 f (Array_      e1 e2)    = f e1 `mappend` f e2
    foldMap21 f (Datum_      d)        = foldMap11 f d
    foldMap21 f (Case_       e  bs)    = f e  `mappend` F.foldMap (foldMap21 f) bs
    foldMap21 f (Superpose_  pes)      = F.foldMap (\(e1,e2) -> f e1 `mappend` f e2) pes
    foldMap21 f (Lub_        es)       = F.foldMap f es -- BUG: really, to handle Lub in a sensible way, we need to adjust Foldable so that it uses a semiring or something; so that we can distinguish \"multiplication\" from \"addition\".

----------------------------------------------------------------
----------------------------------------------------------- fin.
