# Quickstart

Let's start with a simple model of a coin toss experiment so that you can become familiar with some of Hakaru's functionality. We will use the `categorical` Hakaru
[Random Primitive](../lang/rand.md), a generalized Bernoulli distribution for our model. The `categorical` primitive requires an array representing the probability of
achieving each category in the experiement. Since we want a fair experiment, we will state that each side of the coin has an equal chance of being picked. The result of
the coin toss is stored in the variable `x` using Hakaru's notation for [bind](../lang/letbind):

````nohighlight
x <~ categorical([0.5, 0.5])
````

(Why are we doing this?) We will use the value in `x` to choose which distribution, `normal` or `uniform`, to generate a value to bind to another variable `y`. Both the 
`normal` and `uniform` functions are included in Hakaru's [Random Primitives](../lang/rand.md). Since we are selecting values from two probabilistic distributions, we
are creating a *mixture model*.

We want to generate a value from a normal distribution for `x < 0.5` and from a uniform distribution otherwise. For this task, we must use Hakaru's 
[pattern matching functionality](../lang/datatypes.md).

````nohighlight
y <~ match x < 0.5:
	true: normal(0,1)
	false: uniform(0,1)
````

````nohighlight
return(y,x)
````

We then check if *x* is
true or false. Based on that we either have *y* be a draw from
a normal or uniform distribution, and then we return both *x* and *y*.

Assuming we save this file to `twomixture.hk` we can sample from it by
passing it as an argument to the `hakaru` command. 


```bash
hakaru twomixture.hk
```

Hakaru will then produce an infinite stream of samples from the model we created where the first value is from either a normal or uniform distribution, and the second value
is from a categorical distribution:

````bash
(0.8614855008328531, 0)
(0.27145378737815007, 0)
(6.137461559047042e-4, 0)
(0.9699201771404777, 1)
(1.2904529857533733, 1)
(8.605226081336681e-2, 0)
(-0.7713069511457459, 1)
(0.18162205213257607, 1)
(-1.143049106224509, 1)
(0.3667084406816875, 0)
...
````

Of course, Hakaru wouldn't be very interesting if that was all it
did. Often what we wish to do is condition a distribution on
data. Suppose for `twomixture.hk` we knew *y*, and would like to
sample `x` conditioned on this information. We can symbolically
produce the unnormalized conditional distribution, which we call the
*disintegration* of the program.

````bash
disintegrate twomixture.hk
````

This returns

````nohighlight
fn x2 real: 
 weight(0.5,
        weight((exp((negate(((x2 + 0.0) ^ 2)) * 0.5)) * 
                1.0 * 
                recip(natroot((2.0 * pi), 2))),
               x = true
               return x)) <|> 
 weight(0.5,
        match (not((x2 < 0.0)) && not((1.0 < x2))): 
         true: 
          x = false
          return x
         false: reject. measure(bool))
````

Disintegrate returns a function, to make it easier to sample
from, we'll give a value for x2. We'll call this file
`twomixture2.hk`

````
x2 = 0.3
weight(0.5,
    weight((exp((negate(((x2 + 0.0) ^ 2)) * 0.5)) * 
        1.0 * 
            recip(natroot((2.0 * pi), 2))),
            x = true
            return x)) <|> 
weight(0.5,
    match (not((x2 < 0.0)) && not((1.0 < x2))): 
        true:
		 x = false
         return x
        false: reject. measure(bool))
````

Which we can run through some unix commands to get a sense of
the distribution

````bash
hakaru twomixture2.hk | head -n 1000 | sort | uniq -c

    526 false
    474 true
````

As we can see, when x2 = 0.3, the uniform distribution is slightly more
likely. If we change x2 to be 3.0

````nohighlight
x2 = 3.0
weight(0.5,
    weight((exp((negate(((x2 + 0.0) ^ 2)) * 0.5)) * 
        1.0 * 
            recip(natroot((2.0 * pi), 2))),
            x = true
            return x)) <|> 
weight(0.5,
    match (not((x2 < 0.0)) && not((1.0 < x2))): 
        true:
		 x = false
         return x
        false: reject. measure(bool))
````

This reflects that only the normal case is possible.

````bash
hakaru twomixture3.hk | head -n 1000 | sort | uniq -c

    1000 true
````
