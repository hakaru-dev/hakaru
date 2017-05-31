# Density #

The density transform (`density`) finds the density of a probability distribution at a particular point. This transform is a specialized form of the 
[`disintegrate` transform](../transforms/disintegrate.md) that also computes the [expectation](../transforms/expect.md) of the probabilistic 
distribution as part of its work. 

## Usage ##

Your Hakaru program must be a proabability distribution (type `measure(x)`) in order to use the `density` transform. Most Hakaru programs that end
with a `return` statement do not meet this requirement because they return values instead of functions on values.

You can use the `density` transform in the command line by calling:

````bash
density hakaru_program.hk
````

This transformation will produce a new Hakaru program containing an [anonymous function](../lang/functions.md) representing the density function for that model.

## Example ##

The normal distribution is a commonly used distribution in probabilistic modeling. A simple Hakaru program modelling the simplest normal distribution
is:

````nohighlight
normal(0,1)
````

Assuming that this program is named `norm.hk`, we can calculate the density function for this distribution by running:

````bash
density norm.hk
````

**Note:** The output for `density` will be printed in the console. You can easily save this program to a file by redirecting the output to a file by calling 
`density model1.hk > model2.hk`. For this example, we will call our new program `norm_density.hk`.

When you open the new Hakaru program, `norm_density.hk`, you will find an anonymous Hakaru function. You can then assign values to the function's arguments to test the 
probabilistic density at a specific point in the model.
  
````nohighlight
fn x0 real: 
 (exp((negate(((x0 + 0) ^ 2)) / 2)) / 1 / sqrt((2 * pi)) / 1)
````

For example, if you wanted to test the density at `0.2`, you could alter `norm_density.hk` to:

````nohighlight
normalDensity = fn x0 real: 
 (exp((negate(((x0 + 0) ^ 2)) / 2)) / 1 / sqrt((2 * pi)) / 1)
 
return normalDensity(0.2)
````

You could then use the [`hakaru` command](../intro/samplegen.md) to have Hakaru compute the density:

````bash
$ hakaru norm_density.hk | head -n 1
0.3910426939754559
````

**Note:** If the argument `head -n 1` is omitted, the `hakaru` command will print out the resulting density value indefinitely.