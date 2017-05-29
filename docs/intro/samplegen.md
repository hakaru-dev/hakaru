# Generating Samples from your Hakaru Program #

The `hakaru` command is used to indefinitely generate samples from a Hakaru program.

## Usage ##

The `hakaru` command can take up to two Hakaru programs as arguments. If only one program is provided, the `hakaru` command generates samples based on the model described in
the Hakaru program. In this case, the `hakaru` command can be invoked in the command-line by calling:

````bash
hakaru hakaru_program.hk
````

If a second program is given to the `hakaru` command, it will treat the two programs as the start of a Markov Chain. This is used when you have created a transition kernal 
using the [Metropolis Hastings](../transforms/mh.md) transformation. To invoke the `hakaru` command with a transition kernal, you would call:

````bash
hakaru --transition-kernel transition.hk init.hk
````

The first program, `transition.hk`,  is treated as the transition kernel and the second program, `init.hk`, is treated as the initial state of the Markov Chain. When the 
`hakaru` command is run, a sample is drawn from `init.hk`. This sample is then passed to `transition.hk` to generate the second sample. After this point, samples generated
from `transition.hk` are passed back into itself to generate further samples.

### The Dash (`-`) Operator ###

You might encounter some scenarios where you wish to run a Hakaru command or transformation on a program and then send the resulting output to another command or transform. In 
these cases, you can take advantage of the dash (`-`) command-line notation.

The dash notation is a shortcut used to pass standard inputs and outputs to another command in the same line of script. For example, if you wanted to run the `disintegrate`
Hakaru command followed by the `simplify` command, you would enter:

````bash
disintegrate program.hk | simplify -
````

This command is equilvalent to entering:

````bash
disintegrate program.hk > temp.hk
simplify temp.hk
````

**Note:** The `>` operator redirects the output from `disintegrate program.hk` to a new file called `temp.hk`.

## Example ##

The normal distribution is a commonly used distribution in probabilistic modeling. A simple Hakaru program to generate samples from this distribution is:

````nohighlight
return normal(0,1)
````

If you save this program as `norm.hk`, you can generate samples from it by calling:

````bash
hakaru norm.hk
````

The `hakaru` command will print a continuous stream of samples drawn from this program:

````bash
1.2806867344192752
1.7931987343253566
1.7437712239446213
0.21570155009510955
0.7124154152070546
0.14340054239444883
0.3125790473514405
-0.9078427070858872
0.7188339944834061
6.240694120048951e-2
0.5053667107752018
1.1994605612832265
-1.195280076420274
...
````

An example for using the `hakaru` command using a transition kernel is available on the [Metropolis Hastings](../transforms/mh.md) transform page.