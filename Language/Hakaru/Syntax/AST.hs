-- TODO: <https://git-scm.com/book/en/v2/Git-Branching-Basic-Branching-and-Merging>
{-# LANGUAGE DataKinds
           , PolyKinds
           , GADTs
           , StandaloneDeriving
           #-}

{-# OPTIONS_GHC -Wall -fwarn-tabs #-}
----------------------------------------------------------------
--                                                    2015.06.26
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
module Language.Hakaru.Syntax.AST where

import Prelude hiding (id, (.), Ord(..), Num(..), Integral(..), Fractional(..), Floating(..), Real(..), RealFrac(..), RealFloat(..), (^), (^^))
import qualified Prelude
import Data.Sequence        (Seq)
import Data.Proxy
import Control.Category     (Category(..))
import Control.Arrow        ((***))
import qualified Data.Foldable as F
import Data.Number.LogFloat (LogFloat)

import Language.Hakaru.Syntax.Nat
import Language.Hakaru.Syntax.IClasses
import Language.Hakaru.Syntax.DataKind
import Language.Hakaru.Syntax.HClasses
import Language.Hakaru.Syntax.Coercion
{-
import Language.Hakaru.Lazy (Backward, runDisintegrate, density)
import Language.Hakaru.Expect (Expect')
import Language.Hakaru.Simplify (simplify)
import Language.Hakaru.Any (Any)
import Language.Hakaru.Sample
-}

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

deriving instance Eq   (Value a)
-- BUG: deriving instance Read (Value a)
deriving instance Show (Value a)


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
    -- TODO: Log1p, Expm1
    Infinity  :: PrimOp 'HProb
    NegativeInfinity :: PrimOp 'HReal -- TODO: maybe replace this by @negate (CoerceTo signed (PrimOp_ Infinity))@ ?
    -- TODO: add Factorial as the appropriate type restriction of GammaFunc?
    GammaFunc :: PrimOp ('HFun 'HReal 'HProb)
    BetaFunc  :: PrimOp ('HFun 'HProb ('HFun 'HProb 'HProb))



    -- -- Primitive distributions/measures a~la Mochastic (including the polymorphic 'Dirac')
    -- TODO: should we put Dirac back into the main AST?
    -- TODO: could we move Dp_, Plate_, or Chain_ to here?
    Dirac       :: PrimOp ('HFun a ('HMeasure a))
    Lebesgue    :: PrimOp ('HMeasure 'HReal)
    Counting    :: PrimOp ('HMeasure 'HInt)
    Categorical :: PrimOp ('HFun ('HArray 'HProb) ('HMeasure 'HNat))
    -- TODO: make Uniform polymorphic, so that if the two inputs are HProb then we know the measure must be over HProb too
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
    Less  :: (HOrder a) => PrimOp ('HFun a ('HFun a 'HBool))
    Equal :: (HOrder a) => PrimOp ('HFun a ('HFun a 'HBool))


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

-- TODO: a pretty infix syntax, like (:->) or something
data Branch :: Hakaru * -> (Hakaru * -> *) -> Hakaru * -> * where
    Branch :: {-exists Γ.-} Pattern a {-Γ-} -> ast {-Γ-} b -> Branch a ast b

branchPattern :: Branch a ast b -> Pattern a
branchPattern (Branch p _) = p

branchBody :: Branch a ast b -> ast b
branchBody (Branch _ e) = e

-- BUG: deriving instance Eq   (Branch ast a b)
-- BUG: deriving instance Read (Branch ast a b)

instance Show1 ast => Show1 (Branch a ast) where
    showsPrec1 p (Branch pat e) =
        showParen (p Prelude.> 9)
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
    -- TODO: add something like @SafeFrom_ :: Coercion a b -> ast b -> AST ast ('HMaybe a)@ so we can capture the safety of patterns like @if_ (0 <= x) (let x_ = unsafeFrom signed x in...) (...)@ Of course, since we're just going to do case analysis on the result; why not make it a binding form directly?
    -- TODO: we'll probably want some more general thing to capture these sorts of patterns. For example, in the default implementation of Uniform we see: @if_ (lo < x && x < hi) (... unsafeFrom_ signed (hi - lo) ...) (...)@


    -- -- Primitive data types (which aren't PrimOps)
    -- TODO: add the embed stuff...
    -- TODO: replace 'HList and 'HMaybe by the embed stuff...
    -- TODO: replace 'HUnit, 'HPair, and 'HEither by the embed stuff...
    List_  :: [ast a]       -> AST ast ('HList a)
    Maybe_ :: Maybe (ast a) -> AST ast ('HMaybe a)
    -- | Generic case-analysis (via ABTs and Structural Focalization).
    Case_ :: ast a -> [Branch a ast b] -> AST ast b
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
-- BUG: deriving instance (forall b. Eq (ast b)) => Eq (AST ast a)
-- BUG: deriving instance Read (AST ast a)

showParen_0 :: Show a => Int -> String -> a -> ShowS
showParen_0 p s e =
    showParen (p Prelude.> 9)
        ( showString s
        . showString " "
        . showsPrec 11 e
        )

showParen_1 :: Show1 a => Int -> String -> a i -> ShowS
showParen_1 p s e =
    showParen (p Prelude.> 9)
        ( showString s
        . showString " "
        . showsPrec1 11 e
        )

showParen_01 :: (Show b, Show1 a) => Int -> String -> b -> a i -> ShowS
showParen_01 p s e1 e2 =
    showParen (p Prelude.> 9)
        ( showString s
        . showString " "
        . showsPrec  11 e1
        . showString " "
        . showsPrec1 11 e2
        )

showParen_11 :: (Show1 a) => Int -> String -> a i -> a j -> ShowS
showParen_11 p s e1 e2 =
    showParen (p Prelude.> 9)
        ( showString s
        . showString " "
        . showsPrec1 11 e1
        . showString " "
        . showsPrec1 11 e2
        )

showParen_111 :: (Show1 a) => Int -> String -> a i -> a j -> a k -> ShowS
showParen_111 p s e1 e2 e3 =
    showParen (p Prelude.> 9)
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
        Lam_ a  e            -> showParen_01  p "Lam_" a  e
        App_ e1 e2           -> showParen_11  p "App_" e1 e2
        Let_ e1 e2           -> showParen_11  p "Let_" e1 e2
        Fix_ e               -> showParen_1   p "Fix_" e
        PrimOp_ o            -> showParen_0   p "PrimOp_" o
        NaryOp_ o es         ->
            showParen (p Prelude.> 9)
                ( showString "NaryOp_ "
                . showsPrec  11 o
                . showString " "
                . showParen True
                    ( showString "Seq.fromList "
                    . showList1 (F.toList es)
                    )
                )
        Integrate_ e1 e2 e3  -> showParen_111 p "Integrate_" e1 e2 e3
        Summate_   e1 e2 e3  -> showParen_111 p "Summate_"   e1 e2 e3
        Value_ v             -> showParen_0   p "Value_" v
        CoerceTo_   c e      -> showParen_01  p "CoerceTo_"   c e
        UnsafeFrom_ c e      -> showParen_01  p "UnsafeFrom_" c e
        List_ es             ->
            showParen (p Prelude.> 9)
                ( showString "List_ "
                . showList1 es
                )
        Maybe_ me            -> error "TODO: show Maybe_"
        Case_  e pes         ->
            showParen (p Prelude.> 9)
                ( showString "Case_ "
                . showsPrec1 11 e
                . showString " "
                . showList1 pes
                )
        Array_ e1 e2         -> showParen_11  p "Array_" e1 e2
        Bind_  e1 e2         -> showParen_11  p "Bind_"  e1 e2
        Superpose_ pes       -> error "TODO: show Superpose_"
        Dp_    e1 e2         -> showParen_11  p "Dp_"    e1 e2
        Plate_ e             -> showParen_1   p "Plate_" e
        Chain_ e             -> showParen_1   p "Chain_" e
        Lub_   e1 e2         -> showParen_11  p "Lub_"   e1 e2
        Bot_                 -> showString      "Bot_"

instance Show1 ast => Show (AST ast a) where
    showsPrec = showsPrec1
    show      = show1

----------------------------------------------------------------
instance Functor1 AST where
    fmap1 f (Lam_ p  e)           = Lam_ p (f e)
    fmap1 f (App_ e1 e2)          = App_ (f e1) (f e2)
    fmap1 f (Let_ e1 e2)          = Let_ (f e1) (f e2)
    fmap1 f (Fix_ e)              = Fix_ (f e)
    fmap1 _ (PrimOp_ o)           = PrimOp_ o
    fmap1 f (NaryOp_ o es)        = NaryOp_ o (fmap f es)
    fmap1 f (Integrate_ e1 e2 e3) = Integrate_ (f e1) (f e2) (f e3)
    fmap1 f (Summate_   e1 e2 e3) = Summate_   (f e1) (f e2) (f e3)
    fmap1 _ (Value_ v)            = Value_ v
    fmap1 f (CoerceTo_   c e)     = CoerceTo_   c (f e)
    fmap1 f (UnsafeFrom_ c e)     = UnsafeFrom_ c (f e)
    fmap1 f (List_  es)           = List_  (map f es)
    fmap1 f (Maybe_ me)           = Maybe_ (fmap f me)
    fmap1 f (Case_  e pes)        = Case_ (f e) (map (fmap1 f) pes)
    fmap1 f (Array_ e1 e2)        = Array_ (f e1) (f e2)
    fmap1 f (Bind_  e1 e2)        = Bind_  (f e1) (f e2)
    fmap1 f (Superpose_ pes)      = Superpose_ (map (f *** f) pes)
    fmap1 f (Dp_    e1 e2)        = Dp_    (f e1) (f e2)
    fmap1 f (Plate_ e)            = Plate_ (f e)
    fmap1 f (Chain_ e)            = Chain_ (f e)
    fmap1 f (Lub_ e1 e2)          = Lub_   (f e1) (f e2)
    fmap1 _ Bot_                  = Bot_


----------------------------------------------------------------
instance Foldable1 AST where
    foldMap1 f (Lam_ _  e)           = f e
    foldMap1 f (App_ e1 e2)          = f e1 `mappend` f e2
    foldMap1 f (Let_ e1 e2)          = f e1 `mappend` f e2
    foldMap1 f (Fix_ e)              = f e
    foldMap1 _ (PrimOp_ _)           = mempty
    foldMap1 f (NaryOp_ _ es)        = foldMap f es
    foldMap1 f (Integrate_ e1 e2 e3) = f e1 `mappend` f e2 `mappend` f e3
    foldMap1 f (Summate_   e1 e2 e3) = f e1 `mappend` f e2 `mappend` f e3
    foldMap1 _ (Value_ _)            = mempty
    foldMap1 f (CoerceTo_   _ e)     = f e
    foldMap1 f (UnsafeFrom_ _ e)     = f e
    foldMap1 f (List_  es)           = foldMap f es
    foldMap1 f (Maybe_ me)           = foldMap f me
    foldMap1 f (Case_  e pes)        = f e  `mappend` foldMap (f . branchBody) pes
    foldMap1 f (Array_ e1 e2)        = f e1 `mappend` f e2
    foldMap1 f (Bind_  e1 e2)        = f e1 `mappend` f e2
    foldMap1 f (Superpose_ pes)      = foldMap (\(e1,e2) -> f e1 `mappend` f e2) pes
    foldMap1 f (Dp_    e1 e2)        = f e1 `mappend` f e2
    foldMap1 f (Plate_ e)            = f e
    foldMap1 f (Chain_ e)            = f e
    foldMap1 f (Lub_ e1 e2)          = f e1 `mappend` f e2
    foldMap1 _ Bot_                  = mempty


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
