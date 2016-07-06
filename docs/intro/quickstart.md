# Quickstart

Assuming you have Hakaru [installed](/intro/installation), let's
sample a simple a model.

````nohighlight
x <~ bern(0.5)
y <~ match x:
      true:  normal(0,1)
      false: uniform(0,1)
return (y,x)
````

The generative model here has us flip a coin with bias 0.5, and then
have *x* be a draw from that distribution. We then check if *x* is
true or false. Based on that we either have *y* be a draw from
a normal or uniform distribution, and then we return both *x* and *y*.
Because we are choosing between a normal and a uniform distribution,
programs like these are sometimes called *mixture* models.

Assuming we save this file to `twomixture.hk` we can sample from it by
passing it as an argument to the `hakaru` command. 


````bash
hakaru twomixture.hk
````

Hakaru will then produce an infinite stream of samples from the
distribution this program represents.

````bash
(0.8614855008328531, false)
(0.27145378737815007, false)
(6.137461559047042e-4, false)
(0.9699201771404777, true)
(1.2904529857533733, true)
(8.605226081336681e-2, false)
(-0.7713069511457459, true)
(0.18162205213257607, true)
(-1.143049106224509, true)
(0.3667084406816875, false)
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
