# Quickstart

Assuming you have Hakaru [installed](intro/installation), let's
sample a simple a model.

````hakaru
x <~ bern(0.5)
y <~ match x:
      true:  normal(0,1)
      false: uniform(0,1)
return (y,x)
````
<div class="panel panel-warning">
    <div class="panel-heading">
        <h4 class="panel-title">TODO</h4>
	</div>
	<div class="panel-body">
        Use the Hello World example here instead
	</div>
</div>

The generative model here has us flip a coin with bias 0.5, and then
have *x* be a draw from that distribution. We then check if *x* is
true or false. Based on that we either have *y* be a draw from
a normal or uniform distribution, and then we return both *x* and *y*.
Because we are choosing between a normal and a uniform distribution,
programs like these are sometimes called *mixture* models.

Assuming we safe this file to `twomixture.hk` we can sample from it by
passing it as an argument to the `hakaru` command. 


````bash
hakaru twomixture.hk
````

Hakaru will then produce an infinite stream of sample from the
distribution this program represents.

````bash
(-1.792312122450636, 0.5625788978622042)
(1.0545434155815236, 0.17282565691683857)
(-0.8067848738790029, -7.252302309445298e-2)
(-0.28957586068598845, 0.36290414348961947)
(-0.9296988703003928, -1.3689136115836704)
(0.5371250035781452, 0.19993976843063022)
(-1.5183422992252413, -0.21361312207358144)
(-0.9034026482987778, -0.443400152034198)
(-1.1619572227232755e-2, 2.6079518001675708)
(-1.8278545158017236, -0.9876417502011157)
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

````
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

As we can see, as 0.3 the uniform distribution is slightly more
likely. If we change x2 to be 3.0

````
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
