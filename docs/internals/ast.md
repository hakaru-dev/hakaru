# Internal Representation of Hakaru terms

The Hakaru AST can be found defined in
[haskell/Language/Hakaru/Syntax/AST.hs](https://github.com/hakaru-dev/hakaru/blob/master/haskell/Language/Hakaru/Syntax/AST.hs). It is made up of several parts which this section and the next one will explain.

We should note, this datatype makes use of
[Abstract Binding Trees](http://winterkoninkje.dreamwidth.org/103978.html)
which we discuss in more detail in the next
[section](/internals/abt). ABTs can be understood as a way to abstract
the use of variables in the AST. The advantage of this is it allows
all variable substitution and manipulation logic to live in one place
and not be specific to a particular AST.

## Datakind

The AST is typed using the Hakaru kind, defined in [haskell/Language/Types/DataKind.hs](https://github.com/hakaru-dev/hakaru/blob/master/haskell/Language/Hakaru/Types/DataKind.hs). All Hakaru types are defined in terms of
the primitives in this datakind.

````haskell
-- | The universe\/kind of Hakaru types.
data Hakaru
    = HNat -- ^ The natural numbers; aka, the non-negative integers.

    -- | The integers.
    | HInt

    -- | Non-negative real numbers. Unlike what you might expect,
    -- this is /not/ restructed to the @[0,1]@ interval!
    | HProb

    -- | The affinely extended real number line. That is, the real
    -- numbers extended with positive and negative infinities.
    | HReal

    -- | The measure monad
    | HMeasure !Hakaru

    -- | The built-in type for uniform arrays.
    | HArray !Hakaru

    -- | The type of Hakaru functions.
    | !Hakaru :-> !Hakaru

    -- | A user-defined polynomial datatype. Each such type is
    -- specified by a \"tag\" (the @HakaruCon@) which names the type, and a sum-of-product representation of the type itself.
    | HData !HakaruCon [[HakaruFun]]

````

Please read Datakind.hs for more details.

## Term

The Term datatype includes all the syntactic constructions for the Hakaru language.
For all those where we know the number of arguments we expect that language construct
to get, we define the `(:$)` constructor, which takes `SCons` and `SArgs` datatypes
as arguments.

````haskell
-- | The generating functor for Hakaru ASTs. This type is given in
-- open-recursive form, where the first type argument gives the
-- recursive form. The recursive form @abt@ does not have exactly
-- the same kind as @Term abt@ because every 'Term' represents a
-- locally-closed term whereas the underlying @abt@ may bind some
-- variables.
data Term :: ([Hakaru] -> Hakaru -> *) -> Hakaru -> * where
    -- Simple syntactic forms (i.e., generalized quantifiers)
    (:$) :: !(SCon args a) -> !(SArgs abt args) -> Term abt a

    -- N-ary operators
    NaryOp_ :: !(NaryOp a) -> !(Seq (abt '[] a)) -> Term abt a

    -- Literal\/Constant values
    Literal_ :: !(Literal a) -> Term abt a

    Empty_ :: !(Sing ('HArray a)) -> Term abt ('HArray a)
    Array_
        :: !(abt '[] 'HNat)
        -> !(abt '[ 'HNat ] a)
        -> Term abt ('HArray a)

    -- -- User-defined data types
    -- A data constructor applied to some expressions. N.B., this
    -- definition only accounts for data constructors which are
    -- fully saturated. Unsaturated constructors will need to be
    -- eta-expanded.
    Datum_ :: !(Datum (abt '[]) (HData' t)) -> Term abt (HData' t)

    -- Generic case-analysis (via ABTs and Structural Focalization).
    Case_ :: !(abt '[] a) -> [Branch a abt b] -> Term abt b

    -- Linear combinations of measures.
    Superpose_
        :: L.NonEmpty (abt '[] 'HProb, abt '[] ('HMeasure a))
        -> Term abt ('HMeasure a)

    Reject_ :: !(Sing ('HMeasure a)) -> Term abt ('HMeasure a)
````

## SCons and SArgs

When using `(:$)` we have a way to describe primitives where we
know the number of arguments they should get. In that regard,
SArgs is a typed list of abt terms indexed by its size.

````haskell
-- | The arguments to a @(':$')@ node in the 'Term'; that is, a list
-- of ASTs, where the whole list is indexed by a (type-level) list
-- of the indices of each element.
data SArgs :: ([Hakaru] -> Hakaru -> *) -> [([Hakaru], Hakaru)] -> *
    where
    End :: SArgs abt '[]
    (:*) :: !(abt vars a)
        -> !(SArgs abt args)
        -> SArgs abt ( '(vars, a) ': args)
````

These are combined with SCons which describes the constructor, and
the types it expects for its arguments. For example suppose we had
an AST for a function `f` and it's argument `x`, we could construct
a Term for applying `f` to `x` by writing `App_:$ f :* x :* End`.

````haskell
-- | The constructor of a @(':$')@ node in the 'Term'. Each of these
-- constructors denotes a \"normal\/standard\/basic\" syntactic
-- form (i.e., a generalized quantifier). In the literature, these
-- syntactic forms are sometimes called \"operators\", but we avoid
-- calling them that so as not to introduce confusion vs 'PrimOp'
-- etc. Instead we use the term \"operator\" to refer to any primitive
-- function or constant; that is, non-binding syntactic forms. Also
-- in the literature, the 'SCon' type itself is usually called the
-- \"signature\" of the term language. However, we avoid calling
-- it that since our 'Term' has constructors other than just @(:$)@,
-- so 'SCon' does not give a complete signature for our terms.
--
-- The main reason for breaking this type out and using it in
-- conjunction with @(':$')@ and 'SArgs' is so that we can easily
-- pattern match on /fully saturated/ nodes. For example, we want
-- to be able to match @MeasureOp_ Uniform :$ lo :* hi :* End@
-- without needing to deal with 'App_' nodes nor 'viewABT'.
data SCon :: [([Hakaru], Hakaru)] -> Hakaru -> * where
    Lam_ :: SCon '[ '( '[ a ], b ) ] (a ':-> b)
    App_ :: SCon '[ LC (a ':-> b ), LC a ] b
    Let_ :: SCon '[ LC a, '( '[ a ], b ) ] b

    CoerceTo_   :: !(Coercion a b) -> SCon '[ LC a ] b
    UnsafeFrom_ :: !(Coercion a b) -> SCon '[ LC b ] a

    PrimOp_
        :: (typs ~ UnLCs args, args ~ LCs typs)
        => !(PrimOp typs a) -> SCon args a
    ArrayOp_
        :: (typs ~ UnLCs args, args ~ LCs typs)
        => !(ArrayOp typs a) -> SCon args a
    MeasureOp_
        :: (typs ~ UnLCs args, args ~ LCs typs)
        => !(MeasureOp typs a) -> SCon args ('HMeasure a)

    Dirac :: SCon '[ LC a ] ('HMeasure a)

    MBind :: SCon
        '[ LC ('HMeasure a)
        ,  '( '[ a ], 'HMeasure b)
        ] ('HMeasure b)

    Plate :: SCon
        '[ LC 'HNat
        , '( '[ 'HNat ], 'HMeasure a)
        ] ('HMeasure ('HArray a))

    Chain :: SCon
        '[ LC 'HNat, LC s
        , '( '[ s ],  'HMeasure (HPair a s))
        ] ('HMeasure (HPair ('HArray a) s))

    Integrate
        :: SCon '[ LC 'HReal, LC 'HReal, '( '[ 'HReal ], 'HProb) ] 'HProb

    Summate
        :: HDiscrete a
        -> HSemiring b
        -> SCon '[ LC a, LC a, '( '[ a ], b) ] b

    Product
        :: HDiscrete a
        -> HSemiring b
        -> SCon '[ LC a, LC a, '( '[ a ], b) ] b

    Expect :: SCon '[ LC ('HMeasure a), '( '[ a ], 'HProb) ] 'HProb

    Observe :: SCon '[ LC ('HMeasure a), LC a ] ('HMeasure a)
````

You'll notice in `SCon` there are definitions for PrimOp, MeasureOp, and ArrayOp
these are done more organizational purposes and have constructions for the
different categories of primitives.

## MeasureOp

````haskell
-- | Primitive operators to produce, consume, or transform
-- distributions\/measures. This corresponds to the old @Mochastic@
-- class, except that 'MBind' and 'Superpose_' are handled elsewhere
-- since they are not simple operators. (Also 'Dirac' is handled
-- elsewhere since it naturally fits with 'MBind', even though it
-- is a siple operator.)
data MeasureOp :: [Hakaru] -> Hakaru -> * where
    Lebesgue    :: MeasureOp '[]                 'HReal
    Counting    :: MeasureOp '[]                 'HInt
    Categorical :: MeasureOp '[ 'HArray 'HProb ] 'HNat
    Uniform     :: MeasureOp '[ 'HReal, 'HReal ] 'HReal
    Normal      :: MeasureOp '[ 'HReal, 'HProb ] 'HReal
    Poisson     :: MeasureOp '[ 'HProb         ] 'HNat
    Gamma       :: MeasureOp '[ 'HProb, 'HProb ] 'HProb
    Beta        :: MeasureOp '[ 'HProb, 'HProb ] 'HProb
````

## ArrayOp

## PrimOp

