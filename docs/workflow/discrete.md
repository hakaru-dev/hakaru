# Tutorial: Hakaru Workflow for a Discrete Model #

The problem of a burglary alarm has been used to illustrate the workflow for modelling discrete distributions in Hakaru[^1]. It has been adapted from Pearl's textbook on 
probabilistic reasoning (page 35)[^2]:

> Imagine being awakened one night by the shrill sound of your burglar alarm. What is your degree of belief that a burglary attempt has taken place? For illustrative 
> purposes we make the following judgements: (a) There is a 95% chance that an attempted burglary will trigger the alarm system -- P(Alarm|Burglary) = 0.95; (b) based on 
> previous false alarms, there is a slight (1 percent) chance that the alarm will be triggered by a mechanism other than an attempted burglary -- P(Alarm|No Burglary) = 0.01;
> (c) previous crime patterns indicate that there is a one in ten thousand chance that a given house will be burglarized on a given night -- P(Burglary) = 10^-4.

## Modelling ##

To determine whether or not you believe that a burglary is taking place, you must begin by modelling the prior probability distribution. This requires you to create a model
based on what you have observed (the sounding of the alarm) and what you would like to know or infer (is a burglary happening?). This is a discrete model because you can only
select from distinct choices for each of the knowledge sets that you have.

One way that you can model this scenario in Hakaru is by first creating a function for a Bernoulli experiment, which will return either `true` or `false`:

````nohighlight
def bern(p prob):
    x <~ categorical([p, real2prob(1 - p)])
    return [true, false][x]
````

This helper function makes it simpler to represent the information that we are provided in Pearl's problem. For example, the knowledge \(P(Burglary) = 10^{-4}\) 
(`burglary == true`) can now be encoded in the Hakaru program as:

````nohighlight
burglary <~ bern(0.0001)
````

Now that we have encoded the likelihood of a burglary taking place, we can also encode the conditional probabilities of the alarm going off in the case of a burglary,
and the chances of a false alarm. We want `alarm` to be `true` with a 95% probability when a burglary is taking place (`burglary == true`). We also want `alarm` to be
`true` with a 1% probability when there is no burglary (`burglary == false`). Since the likelihood of the alarm going off is dependent on the value of `burglary`, we can
use Hakaru's [conditionals](../lang/cond.md) to determine which distribution to pick from. We can then pass this decision to our `bern` function to get the value for `alarm`:

````nohighlight
alarm <~ bern(if burglary: 0.95 else: 0.01)
````

To complete our model, we return the values for `burglary` and `alarm`. Note that the order that the values are returned in matters for the next step in the Hakaru workflow.
Since we want to make an inference based on known information, we must return values in order of known (`alarm`) followed by unknown (`burglary`) knowledge:

````nohighlight
return (alarm, burglary)
````

## Transformation ##

For this problem, we are only interested in the cases where the alarm is sounding (`alarm == true`). If we were to skip down to the application step in the Hakaru workflow,
we would have a difficult time collecting enough samples for this set because they happen infrequently. Instead, we will use the transformation step of the Hakaru 
workflow to convert our prior model into a conditional distribution. This will make it easier to collect the samples that we want later on. For our burglary problem, our
transformation stage only requires the [`disintegrate` transformation](../transforms/disintegrate.md). 

Assuming that you saved your model as `burglary.hk`, we can use the disintegrate transformation on it by calling `disintegrate burglary.hk` in the command line. It will
produce a conditional model represented as a new Hakaru program:

````nohighlight
fn x5 bool: 
 bern = fn p prob: 
         x <~ categorical([p, real2prob((1 - prob2real(p)))])
         return [true, false][x]
 burglary <~ bern(1/10000)
 p = (match burglary: 
       true: 19/20
       false: 1/100)
 x16 <~ weight(([p, real2prob((1 - prob2real(p)))][(match x5: 
                                                     true: 0
                                                     false: 1)]
                 / 
                (summate x0 from 0 to size([p, real2prob((1 - prob2real(p)))]): 
                  [p, real2prob((1 - prob2real(p)))][x0])),
               return ())
 return burglary
````

**Note:** The output for `disintegrate` will be printed in the console. You can easily save this program to a file by redirecting the output to a file by calling 
`disintegrate model1.hk > model2.hk`. For this example, we will call our new program `burglary_disintegrate.hk`.

This Hakaru program represents the mapping from our known knowledge (the alarm is sounding) and the knowledge that we want to infer from it (are we being burglarized?). As
a result of the disintegration, our original variable `alarm` has been renamed to `x5`.

## Application ##

Once we have transformed our original model (`burglary.hk`) into a function that is better suited to making the inference that we are interested in (`burglary_disintegrate.hk`),
we can use the generated function to create a new Hakaru program that knows that the alarm has been triggered (`alarm == true`). In this case, the only change that needs to be
made is to the line `fn x5 bool:`, which tells the Hakaru program what state the alarm is in. Since we are only interested in cases where `alarm == true`, we must change this
line to `x5 = true`:

````nohighlight
x5 = true
 bern = fn p prob: 
         x <~ categorical([p, real2prob((1 - prob2real(p)))])
         return [true, false][x]
 burglary <~ bern(1/10000)
 p = (match burglary: 
       true: 19/20
       false: 1/100)
 x16 <~ weight(([p, real2prob((1 - prob2real(p)))][(match x5: 
                                                     true: 0
                                                     false: 1)]
                 / 
                (summate x0 from 0 to size([p, real2prob((1 - prob2real(p)))]): 
                  [p, real2prob((1 - prob2real(p)))][x0])),
               return ())
 return burglary
````

One program transformation that can be called at this stage is the [Hakaru-Maple `simplify` subcommand](../transforms/hk-maple.md). This will call Maple to algebraically
simplify Hakaru models. Calling `hk-maple burglary_disintegrate.hk` produces a new, simpler, model of our burglary alarm scenario:

````nohighlight
weight(19/200000, return true) <|> 
weight(9999/1000000, return false)
````

Without any further work, we can already see that the alarm sounding is most likely a false alarm. However, the `simplify` transformation will not always produce a clear
result such as this one. For these situations, you must use the [`hakaru` command](../intro/samplegen.md).

How does the `hakaru` command answer our original question? If you simply call the command `hakaru burglary_disintegrate.hk` in the command line, you will create an 
infinite stream of samples:

````bash
$ hakaru burglary_disintegrate_simplify.hk
9.999999999999995e-3    false
9.999999999999995e-3    false
9.999999999999995e-3    false
9.999999999999995e-3    false
9.999999999999995e-3    false
9.999999999999995e-3    false
9.999999999999995e-3    false
9.999999999999995e-3    false
9.999999999999995e-3    false
9.999999999999995e-3    false
9.999999999999995e-3    false
9.999999999999995e-3    false
9.999999999999995e-3    false
9.999999999999995e-3    false
9.999999999999995e-3    false
9.999999999999995e-3    false
9.999999999999995e-3    false
...
````

This does not quite answer our original question because there is no summary of the samples that we have generated. Instead, we should summarize the samples by their weight:

````bash
$ hakaru burglary_disintegrate.hk | head -n 100000 | awk '{a[$2]+=$1}END{for (i in a) print i, a[i]}'
false 999.92
true 7.6
````

**Note:** This summary is limited to 100,000 samples.

This summary of information makes it much easier to determine that, even though the alarm is going off, the chances of the house being burglarized is very low.

[^1]: P. Narayanan, J. Carette, W. Romano, C. Shan and R. Zinkov, "Probabilistic Inference by Program Transformation in Hakaru (System Description)", Functional and Logic 
Programming, pp. 62-79, 2016.
[^2]: J. Pearl, Probabilistic reasoning in intelligent systems: Networks of plausible inference. San Francisco: M. Kaufmann, 1988.