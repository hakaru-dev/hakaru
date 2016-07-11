# Disintegrations transformation

The disintegration transformation takes as input a program
representing a joint probability distribution, and returns
a program which represents an posterior distribution.

For example, if we have the following joint distribution `hello.hk`

````
θ <~ normal(0,1)
x <~ normal(θ,1)
return (x,θ)
````

When we call `disintegrate hello.hk` we obtain:

````
fn x2 real: 
 θ <~ normal(0, 1)
 x7 <~ weight((exp((negate(((x2 - θ) ^ 2)) / 2))
                / 
               1
                / 
               sqrt((2 * pi))),
              return ())
 return θ
````

This represents the posterior on `θ` given a value of `x` which
has been renamed `x2`.

## Density

Find the density of a probability distribution at a particular
point is actually a special-case of disintegrate and is
defined in terms of it.
