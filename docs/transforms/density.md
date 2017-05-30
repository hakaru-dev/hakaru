# Density #

Finding the density of a probability distribution at a particular point is a special-case use of `disintegrate`. It is defined in terms of it and the expectation 
transformation.

## Usage ##

You can use the `density` transform in the command line by calling:

````bash
density hakaru_program.hk
````

## Example ##

````nohighlight
echo "normal(0,1)" | density -

fn x0 real: 
 (exp((negate(((x0 + 0) ^ 2)) / 2)) / 1 / sqrt((2 * pi)) / 1)
````