# Generating Samples from your Hakaru Program #

The `hakaru` command is used to indefinitely generate samples from a Hakaru program. The `hakaru` command is an importance sampler, so each sample is assigned a weight. 
These weights are typically `1.0`, but this might not be the case for all Hakaru programs.

## Usage ##

The `hakaru` command can take up to two Hakaru programs as arguments. If only one program is provided, the `hakaru` command generates samples based on the model described in
the Hakaru program. In this case, the `hakaru` command can be invoked in the command-line by calling:

````bash
hakaru hakaru_program.hk
````

If a second program is given to the `hakaru` command, it will treat the two programs as the start of a Markov Chain. This is used when you have created a transition kernel 
using the [Metropolis Hastings](../transforms/mh.md) transformation. To invoke the `hakaru` command with a transition kernel, you would call:

````bash
hakaru --transition-kernel transition.hk init.hk
````

The first program, `transition.hk`,  is treated as the transition kernel and the second program, `init.hk`, is treated as the initial state of the Markov Chain. When the 
`hakaru` command is run, a sample is drawn from `init.hk`. This sample is then passed to `transition.hk` to generate the second sample. After this point, samples generated
from `transition.hk` are passed back into itself to generate further samples.

### The Dash (`-`) Operator ###

You might encounter some scenarios where you wish to run a Hakaru command or transformation on a program and then send the resulting output to another command or transform. 
In these cases, you can take advantage of the dash (`-`) command-line notation.

The dash notation is a shortcut used to pass standard inputs and outputs to another command in the same line of script. For example, if you wanted to run the `disintegrate`
Hakaru command followed by the `simplify` command, you would enter:

````bash
disintegrate program.hk | simplify -
````

This command is equivalent to entering:

````bash
disintegrate program.hk > temp.hk
simplify temp.hk
````

**Note:** The `>` operator redirects the output from `disintegrate program.hk` to a new file called `temp.hk`.

## Example ##

The "trick coin" is a basic example that is used to introduce the probability or expectation of an outcome. Suppose we are given an unfair coin that follows the distribution:

````nohighlight
weight(3, return true) <|> weight(1, return false)
````

If you save this program as `biasedcoin.hk`, you can generate samples from it by calling:

````bash
hakaru biasedcoin.hk
````

The `hakaru` command will print a continuous stream of samples drawn from this program:

````bash
4.0     true
4.0     true
4.0     true
4.0     true
4.0     true
4.0     true
4.0     true
4.0     false
4.0     false
...
````

In this example, all sample weights are `4.0`. Let's say that you wanted to know how many times the coin landed on each of HEADS and TAILS. You can collect an estimate of 
this ratio by using a short command-line program that limits sample generation to 2000 samples:

````bash
$ hakaru biasedcoin.hk | head -n 2000 | awk '{a[$2]+=$1/$1}END{for(i in a) print i, a[i]}'
false 509
true 1491
````

**Note:** The `$1/$1` expression in the `awk` command normalizes the weight produced by the `hakaru` command so that individual samples are counted. If this expression is
simplified to `$1`, the `awk` command returns the sum of the weights.

To suppress the printing of weights during sample generation, you can use the `--no-weights` or `-w` option:

````bash
hakaru --no-weights norm.hk
````

Which will result in the printing of samples without their weight information:

````bash
false
true
true
true
false
true
true
true
...
````

An example for using the `hakaru` command using a transition kernel is available on the [Metropolis Hastings](../transforms/mh.md) transform page.
