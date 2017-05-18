# Quick Start: A Mixture Model Example

Let's start with a simple model of a coin toss experiment so that you can become familiar with some of Hakaru's data types and functionality. We will assume that a single 
coin flip can be represented using a Bernoulli distribution. After we have created the Bernoulli model, we will use it to create a mixture model and condition the 
experiment to see how different trick coins impact the mixture model over multiple samples.

## Modeling a Bernoulli Experiment

We will use the `categorical` Hakaru [Random Primitive](../lang/rand.md), to write a Bernoulli distribution[^1] for our model. The `categorical` primitive requires an 
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

Let's use our coin flip experiment to create a mixture model by drawing a sample from a normal distribution when the coin is Heads (`true`) and from a uniform distribution
when it is Tails (`false`). This is called a *mixture model*[^2] because we are selecting samples from different distributions. Let's start by saving a copy of your 
Bernoulli function into a new program so that we can use it in our new model. For this example, we will call it `twomixture.hk`.

Let's start by binding the return value of our `bern` function to a variable called `coin` to represent the outcome of an experiment:

````nohighlight
coin <~ bern(0.5)
````

Now that we have stored the result of our experiment, let's use it to generate a sample. Our model has a selection condition where Heads causes a sample to be drawn from 
achieving normal distribution and Tails draws from a uniform distribution. There are two ways of handling this in Hakaru -- [conditionals](../lang/cond.md) and 
[pattern matching](../lang/datatypes.md). Since we are working with Booleans, let's use patern matching so that we can see what it looks like in Hakaru.

Hakaru pattern matching requires a sequence and a set of possible patterns to compare the sequence to. In our model, our sequence would be `coin` because that is what we are
using to select a distribution. Our possible patterns are the possible values that `coin` could have -- `true` and `false`. When the pattern is `true`, we call the normal
distribution and when it is `false` we call the uniform distribution. Both the `normal` and `uniform` functions are included in Hakaru's [Random Primitives](../lang/rand.md),
so we do not need to define our own functions for them. The outcome of the pattern match will not be saved unless we bind it to a variable, so let's bind it to a variable
called `sample`:

````nohighlight
sample <~ match coin:
	true: normal(0,1)
	false: uniform(0,1)
````

Now that we have both the result of our coin toss experiment (`coin`) and our mixture model (`sample`), we can return the values:

````nohighlight
return(coin, sample)
````

We have now completed the mixture model program. You can run the program using the command `hakaru twomixture.hk' to collect samples indefinitely:

````bash
(true, -0.37622272051934547)
(false, 4.666320977960081e-2)
(true, 1.3351978120820147)
(true, 0.4657111228024136)
(false, 0.6528078075939211)
(false, 0.2410145787295287)
(false, 0.624335005419879)
(true, -1.5127939371882644)
(false, 0.15925713370352967)
(true, 2.2762774663914114e-2)
...
````

Of course, Hakaru would not be very interesting if it only provided the means for you to define your model. Let's try conditioning our model so that we can experiment with 
trick coins (\(P \neq 0.5\)) to see how it affects our mixture model.

## Conditioning a Hakaru Program

Suppose for our `twomixture.hk` 
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

Which we can run through some unix commands to get a sense of the distribution

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

[^1]: [Bernoulli distribution (Wikipedia)](https://en.wikipedia.org/wiki/Bernoulli_distribution)
[^2]: [Mixture Model (Wikipedia)](https://en.wikipedia.org/wiki/Mixture_model)
