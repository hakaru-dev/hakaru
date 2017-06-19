# Generating Samples from your Hakaru Program #

The Hakaru language is designed so that it is easy to express probabilistic models programmatically. In particular, Hakaru makes makes it easy to use Monte Carlo methods, 
which aim to generate individual samples and estimate expectation functions, or expectation, from a given distribution. The first task, drawing samples from a distribution, 
is often difficult because it might not be possible to sample from the target distribution directly. This can be exasperated as the dimensionality of the sample space 
increases. In these scenarios, a comparable distribution can be selected to draw samples from. Importance sampling is a Monte Carlo method that is used to generate samples 
by estimating an expectation for the target distribution instead. The estimated expectation is then used to generate samples. To account for the knowledge that the 
samples were not generated from the target distribution, a weight is assigned so that each sample's contribution to the estimator is adjusted according to its relevance. 
However, this method only works well if the distribution proposed by the expectation is similar to the target distribution. For more complex distributions, a 
different approach, such as the Metropolis Hastings method should be used[^1].

The `hakaru` command is used to indefinitely generate samples from a Hakaru program using importance sampling. Each sample is assigned a weight, and a sample's weight is 
initialized to `1.0`. Weights are changed by Hakaru primitives and processes such as [`weight`](../lang/rand.md).

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

To demonstrate weights in Hakaru, a sample problem of a burglary alarm is adapted from Pearl's textbook on probabilistic reasoning (page 35)[^2]:

> Imagine being awakened one night by the shrill sound of your burglar alarm. What is your degree of belief that a burglary attempt has taken place? For illustrative 
> purposes we make the following judgements: (a) There is a 95% chance that an attempted burglary will trigger the alarm system -- P(Alarm|Burglary) = 0.95; (b) based on 
> previous false alarms, there is a slight (1 percent) chance that the alarm will be triggered by a mechanism other than an attempted burglary -- P(Alarm|No Burglary) = 0.01;
> (c) previous crime patterns indicate that there is a one in ten thousand chance that a given house will be burglarized on a given night -- P(Burglary) = 10^-4.

This can be modelled in Hakaru by the program:

````nohighlight
burglary <~ categorical([0.0001, 0.9999])
weight([0.95, 0.01][burglary],
return [true,false][burglary])
````

If you save this program as `weight_burglary.hk`, you can generate samples from it by calling:

````bash
$ hakaru weight_burglary.hk
1.0000000000000004e-2   false
1.0000000000000004e-2   false
1.0000000000000004e-2   false
1.0000000000000004e-2   false
1.0000000000000004e-2   false
1.0000000000000004e-2   false
1.0000000000000004e-2   false
1.0000000000000004e-2   false
1.0000000000000004e-2   false
1.0000000000000004e-2   false
1.0000000000000004e-2   false
...
````

The `hakaru` command will print a continuous stream of samples drawn from this program. In this example, `true` and `false` samples have different weights. This will not be
immediately apparent if you manually sift through the samples. If you wanted to see the ratio of weights for a series of samples, you can use an `awk` script that tallies 
the weights for a limited set of samples:

````bash
$ hakaru weight_burglary.hk | head -n 2000 | awk '{a[$2]+=$1}END{for (i in a) print i, a[i]}'
false 19.99
true 0.95
````

If you were only interested in counting how many times the coin tosses landed on each of HEAD and TAILS, modify the `awk` script to be a counter instead:

````bash
$ hakaru weight_burglary.hk | head -n 2000 | awk '{a[$2]+=1}END{for (i in a) print i, a[i]}'
false 1999
true 1
````

In this case, the printing of sample weights might not be important. To suppress the printing of weights during sample generation, you can use the `--no-weights` or `-w` 
option:

````bash
$ hakaru --no-weights weight_burglary.hk
false
false
false
false
false
false
false
false
...
````

An example for using the `hakaru` command using a transition kernel is available on the [Metropolis Hastings](../transforms/mh.md) transform page.

[^1]: D.J.C. MacKay, "Introduction to Monte Carlo Methods", Learning in Graphical Models, vol. 89, pp. 175-204, 1998.
[^2]: J. Pearl, Probabilistic reasoning in intelligent systems: Networks of plausible inference. San Francisco: M. Kaufmann, 1988.