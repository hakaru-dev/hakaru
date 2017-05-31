# Expect

The expectation transformation takes a program representing a measure,
and a function over the sample space, and returns a program computing
the expectation over that measure with respect to the given function.

## Usage

Expect can be used inside programs with the `expect` keyword.

````nohighlight
expect x uniform(1,3):
    real2prob(2*x + 1)
````

This program computes the expectation of `uniform(1,3)` using the
function `2*x + 1`. This program expands to the following equivalent
program:

````
integrate x from 1 to 3: 
 recip(real2prob(3 - 1)) * real2prob(2*x + 1)
````

This can be optimized by piping by it into the `simplify` program. It
will in turn return `5`.