# Coercions

For convenience, Hakaru offers functions to convert between the four
different numeric types in the language. These types are

* nat - Natural numbers
* int - Integers
* prob - Positive real numbers
* real - Real numbers

Amongst these types there are a collection of safe and unsafe
coercions. A safe coercion is one which is always guaranteed to
be valid. For example, converting a `nat` to an `int` is always
safe. Converting an `int` to a `nat` is unsafe as the value can
negative, and lead to runtime errors.

These are represented in the AST using the `CoerceTo` and `UnsafeFrom`
constructors. Note that coercions are always defined in terms of the
safe direction to go to.

````haskell
CoerceTo_   :: !(Coercion a b) -> SCon '[ LC a ] b
UnsafeFrom_ :: !(Coercion a b) -> SCon '[ LC b ] a
````

Internally, coercions are specified using the `Coercion` datatype. This
datatype states that each coercion is made up of a series of primitive
coercions.

````haskell
data Coercion :: Hakaru -> Hakaru -> * where
    CNil :: Coercion a a
    CCons :: !(PrimCoercion a b) -> !(Coercion b c) -> Coercion a c
````

These primitive coercions can either involve loosening a restriction
on the sign of the value, or changing the numeric value to be over
a continuous value. For example, to coerce from int to real, we would
have a single `Coercion` with a `PrimCoercion` in it with the Continuous
data constructor.

````haskell
data PrimCoercion :: Hakaru -> Hakaru -> * where
    Signed     :: !(HRing a)       -> PrimCoercion (NonNegative a) a
    Continuous :: !(HContinuous a) -> PrimCoercion (HIntegral   a) a
````
