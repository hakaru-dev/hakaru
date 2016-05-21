# Types and Coercions

Hakaru is a simply-typed language which has
a few basic types and some more complicated
ones which can be built out of simpler types.

## Types

* nat is the type for natural numbers. This includes zero.
* int is the integer type.
* prob is the type for positive real number. This includes zero.
* real is the type for real numbers.
* array(x) is the type for arrays where each element is type x
* measure(x) is the type for probability distributions whose
  sample space is type x

## Coercions

For the primitive numeric types we also offer coercion functions.

* prob2real
* int2real
* nat2int
* real2prob
* real2int
* int2nat

For the ones which are always safe to apply such as `nat2int` we will
automatically insert them if it is required for the program to typecheck.
