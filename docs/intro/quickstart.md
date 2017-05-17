# Quick Start: A Mixture Model Example

Let's start with a simple model of a coin toss experiment so that you can become familiar with some of Hakaru's data types and functionality. We will assume that a single 
coin flip can be represented using a Bernoulli distribution. After we have created the Bernoulli model, we will use it to create a mixture model and condition the experiment 
to see how different trick coins impact the mixture model over multiple samples.

## Modeling a Bernoulli Experiment

We will use the `categorical` Hakaru [Random Primitive](../lang/rand.md), to write a Bernoulli distribution for our model. The `categorical` primitive requires an 
[array](../lang/arrays.md) representing the probability of achieving each category in the experiement. Let's start with a fair experiment and state that each side of the 
coin has an equal chance of being picked. The result of the coin toss is stored in the variable `b` using Hakaru's notation for [bind](../lang/letbind):

````nohighlight
b <~ categorical([0.5, 0.5])
````

For data type simplicity, we will map Heads to `true` and Tails to `false`. By putting the values of `true` and `false` into an array, we can use the value in `b` to
select which of them to return as the result of the coin toss:

````nohighlight
return [true, false][b]
```` 

A characteristic of the Bernoulli distribution is that it assumes that only one experiment is conducted. To collect samples, we need to run this experiment multiple times.
To aid in this task, we can rewrite the Bernoulli model as a [function](../lang/functions.md). We will call our function `bern`: 

````nohighlight
def bern ():
	b <~ categorical([0.5, 0.5])
	return [true, false][b]
````

Now that we are using functions, we can generalize our model so that we can run experiments on both fair and trick coins. To do this, we should pass in a probability `p` as 
a function argument, which is then used to populate the `categorical` primitive. Hakaru has a specialized data type for probabilities called `prob`, which we will use as the
data type for our function input:

````nohighlight
def bern (p prob):
	b <~ categorical([p, (1 - p)])
	return [true, false][b]
````

If you we to run this function, we will get a `Type Mismatch` error. This is because the value `(1 - p)` is converted to type `real` as a result of the subtraction operation
and `categorical` expects all of the values in its array to be of type `prob`. One solution would be to manually pass in the value of `(1 - p)` as a function argument, which
would artificially complicate our function. Instead, we can use Hakaru's [coercions](../lang/coercions.md) to recast `(1 - p)` to type `prob`:

````nohighlight
def bern (p prob):
	b <~ categorical([p, real2prob(1 - p)])
	return [true, false][b]
````

We can now use our model to run a series of Bernoullli experiments. Let's set up our program to use a fair coin and save it as `bernoulli.hk`:

````nohighlight
def bern (p prob):
	b <~ categorical([p, real2prob(1 - p)])
	return [true, false][b]
	
bern(0.5)
````

Running this program using `hakaru bernoulli.hk` should result in an infinite stream of coin toss trials:

````bash
false
true
false
true
true
true
...
````

Now that we have set up our Bernoulli experiment, let's use it to create a mixture model.

## Creating a Mixture Model

Let's use our coin flip experiment to create a mixture model. Save a copy of your Bernoulli function into a new program and call it `twomixture.hk`.

to decide if a value is picked from a normal distribution or a uniform distribution. Since we stored the outcome of the coin toss
in the variable `x`, we can use it to determine which value to generate. We want to use the new value later, so we will store it in another variable `y`. Both the 
`normal` and `uniform` functions are included in Hakaru's [Random Primitives](../lang/rand.md). Since we are selecting values from two probabilistic distributions, we
are creating a *mixture model*[^1].

````nohighlight
coin <~ bern(0.5)
````

Our coin toss experiment has an equal chance of producing *Heads* or *Tails*, so we will use a value of `0.5` to divide the selection process. We want to generate a value 
from a normal distribution for `x < 0.5` and from a uniform distribution otherwise. For this task, we must use Hakaru's [pattern matching functionality](../lang/datatypes.md).
We then store the result of the match in `y`:

````nohighlight
sample <~ match coin:
	true: normal(0,1)
	false: uniform(0,1)
````

Now that we have both the result of our coin toss experiment (`x`) and our mixture model (`y`), we can return the values:

````nohighlight
return(sample, coin)
````

We have now completed the mixture model script. If you save the program as `twomixture.hk`, you can run the program using the command `hakaru twomixture.hk' to collect
samples indefinitely:

````bash
(-1.395602051006621, true)
(1.327998279831012, true)
(0.6096020267128114, true)
(8.391489905355709e-2, false)
(-0.31296413142229, true)
(0.9949687121707352, false)
(-0.6575376566451158, true)
(0.8439456991407505, true)
(0.8409098253407205, false)
(0.12109472056947934, false)
(1.0591255892006863, true)
...
````

## Conditioning a Hakaru Program

Of course, Hakaru wouldn't be very interesting if that was all it did. It is also common to condition a distribution using known data. Suppose for our `twomixture.hk` 
program, we knew `y` and want to sample `x` using this information. We can symbolically produce the unnormalized conditional distribution from which `x` samples are taken
by using Hakaru's [disintegration](../transforms/disintegrate.md) transform. You can use this transform on your program by calling `disintegrate twomixture.hk`, which 
returns a new model written as a function so that it is easier to draw samples from it. In this model, the variable `x2` is used to set a value for `y`:

````nohighlight
fn x5 real: 
 bern = fn p prob: 
         b <~ categorical([p, real2prob((1 - prob2real(p)))])
         return [true, false][b]
 coin <~ bern(1/2)
 (match coin: 
   true: 
    x12 <~ weight((exp((negate(((x5 + 0) ^ 2)) / 2))
                    / 
                   1
                    / 
                   sqrt((2 * pi))),
                  return ())
    return coin
   _: reject. measure(bool)) <|> 
 bern = fn p prob: 
         b <~ categorical([p, real2prob((1 - prob2real(p)))])
         return [true, false][b]
 coin <~ bern(1/2)
 (match coin: 
   false: 
    (match (not((x5 < 0)) && not((1 < x5))): 
      true: 
       x12 <~ return ()
       return coin
      _: reject. measure(bool))
   _: reject. measure(bool))
````
**Note:** You can easily save this program to a file by redirecting the output to a file by calling `hakaru disintegrate model1.hk > modelDis.hk`. For this example, we
will call our new program `twomixture_D.hk`. 

````nohighlight
x5 = 0.3
 bern = fn p prob: 
         b <~ categorical([p, real2prob((1 - prob2real(p)))])
         return [true, false][b]
 coin <~ bern(1/2)
 (match coin: 
   true: 
    x12 <~ weight((exp((negate(((x5 + 0) ^ 2)) / 2))
                    / 
                   1
                    / 
                   sqrt((2 * pi))),
                  return ())
    return coin
   _: reject. measure(bool)) <|> 
 bern = fn p prob: 
         b <~ categorical([p, real2prob((1 - prob2real(p)))])
         return [true, false][b]
 coin <~ bern(1/2)
 (match coin: 
   false: 
    (match (not((x5 < 0)) && not((1 < x5))): 
      true: 
       x12 <~ return ()
       return coin
      _: reject. measure(bool))
   _: reject. measure(bool))
````

Which we can run through some unix commands to get a sense of
the distribution

````bash
hakaru twomixture_D.hk | head -n 1000 | sort | uniq -c

    526 false
    474 true
````

As we can see, when `x5 = 0.3`, samples are slightly more likely to be picked from the uniform distribution instead of the normal distribution. If we change the value of 
`x5` to `3.0` and rerun the program, we find that values are only picked from the normal distribution:

````bash
hakaru twomixture_D.hk | head -n 1000 | sort | uniq -c

    1000 true
````

[^1]: [Mixture Model (Wikipedia)](https://en.wikipedia.org/wiki/Mixture_model)
