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
1.0     1.0     -0.3972582073860394
1.0     1.0     5.6338252430958864e-2
1.0     1.0     -0.20943562475454072
1.0     1.0     -0.819120522312333
1.0     1.0     8.751803599366902e-2
1.0     1.0     -1.331099012725283
1.0     1.0     -2.7818114615228814e-2
1.0     1.0     0.826857488709436
1.0     1.0     0.8653639888398083
1.0     1.0     0.1538518225473193
1.0     1.0     -0.7354102387601734
1.0     1.0     1.1604484258837295
1.0     1.0     0.26847855847761243
1.0     1.0     -0.26134128530561285
...
````

In this example, all sample weights are `1`. To suppress the printing of weights during sample generation, you can use the `--no-weights` or `-w` option:

````bash
hakaru --no-weights norm.hk
````

Which will result in the printing of samples without their weight information:

````bash
0.7505833618849641
-3.0157439504826952e-2
1.8516535505034426
-0.1290032373875403
-1.3007179610623967
-1.1003383475624913
-6.582105542515895e-2
1.0295214963052317
1.0299285419588868
-6.214526660454764e-2
0.46461836869237355
-0.6303856890688903
0.22057597993019365
-1.5735921283484084
...
````

An example for using the `hakaru` command using a transition kernel is available on the [Metropolis Hastings](../transforms/mh.md) transform page.
