# Disintegrate #

The `disintegrate` transformation converts a Hakaru program representing a joint probability distribution into a Hakaru program representing a posterior distribution for a 
target distribution variable. This transform is equivalent to model conditioning in probability theory, where the known data is provided to the transformed Hakaru model.

**Note:** The `disintegrate` transform cannot be used to condition variables of type `bool` or expressions containing Boolean operators.

## Usage ##

Before you use the `disintegrate` transform, your Hakaru program should contain a `return` statement containing the variables for your known and unknown data. The order of the
variables in the `return` statement is important. The variable for the known data should appear first, followed by the variable representing the unknown data.

You can use the `disintegrate` transform in the command line by calling:

````bash
disintegrate hakaru_program.hk
````

This command will return a new Hakaru program that contains an anonymous function representing the transformed program. The function argument represents the variable for which 
you will test different values for your unknown variable.

## Example ##

Let's condition a joint probability distribution of two independent random variables that are each drawn from a normal distribution. You can define this model in Hakaru using
a program such as:

````nohighlight
x <~ normal(0,1)
y <~ normal(x,1)
return (y,x)
````

In this program, `x` and `y` are the independent variables. The statement `return (y,x)` states that you want to condition your model to create a posterior model for `x` using
known values for `y`. If you save this program as `hello1.hk`, you would call the disintegrate transform on it by running:

````bash
disintegrate hello1.hk
````

**Note:** The output for `disintegrate` will be printed in the console. You can easily save this program to a file by redirecting the output to a file by calling 
`disintegrate model1.hk > model2.hk`. For this example, we will call our new program `hello1_D.hk`.

The resulting program renames the known-value variable `y` (here it is renamed to `x2`) and creates an anonymous function that, given a value for `y`, calculates the 
corresponding value for `x`:

````nohighlight
fn x2 real: 
 x <~ normal(0, 1)
 x7 <~ weight((exp((negate(((x2 - x) ^ 2)) / 2))
                / 
               1
                / 
               sqrt((2 * pi))),
              return ())
 return x
````
