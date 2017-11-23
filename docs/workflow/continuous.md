# Tutorial: Hakaru Workflow for a Continuous Model #

The real world is a complex and unpredictable place, so many statistical problems involve random real numbers. Hakaru is able to tackle
these real world problems using a similar approach to the one used for discrete models. To illustrate this workflow, the calibration of
thermometers is used[^1].

In this scenario, we are building thermometers that measure the temperature of a room. A reliable thermometer here relies on two
attributes:

- Temperature noise, or how much the room's temperature fluctuates over time
- Measurement noise, or how often the thermometer measures the wrong value due to device defects

In order to calibrate our thermometers, we want to approximate these values as accurately as possible so that our thermometers can 
tune its measurements based on its knowledge of temperature and measurement noise in the environment. 

## Modelling ##

For our thermometer model, we must first make a few assumptions about the environment. Normally this information would be collected as
part of the problem's domain knowledge. For this example, we will use the following information:

- The temperature noise follows a uniform distribution on the interval \([\)3, 8\(]\)
- The measurement noise follows a uniform distribution with a range of \([\)1, 4\(]\)
- Temperature and measurement samples follow a normal distribution
- The initial temperature of the room is 21\(^{\circ}\)C

Our model starts with the definition of the temperature and measurement noise. From our assumptions, we know that these values follow
a uniform distribution with real number intervals. In addition to defining distributions for these values, we will also use 
[coercions](../lang/coercions.md) to cast the values from `real` to `prob` values:

````nohighlight
nT <~ uniform(3,8)
nM <~ uniform(1,4)

noiseT = real2prob(nT)
noiseM = real2prob(nM)
````

**Note:** See [Let and Bind](../lang/letbind.md) for usage differences.

The values generated for `noiseT` and `noiseM` are used as the standard deviation required by the [`normal` primitive probability 
distribution](../lang/rand.md) when generating values for temperature (`t1`, `t2`) and measurement (`m1`, `m2`).

For temperature, we need two values. The first is a temperature centered about the initial room temperature (21\(^{\circ}\)C) and the 
second is a future room temperature centered about the the first measured temperature. Both follow a normal distribution with a 
standard deviation of `noiseT`: 

````nohighlight
t1 <~ normal(21, noiseT)
t2 <~ normal(t1, noiseT)
````

Temperature measurements are centered about the temperature value being measured, therefore the values `t1` and `t2` are used. 
We made the initial assumption that measurement values follow a normal distribution, and we have generated `noiseM` as the standard
deviation:

````nohighlight
m1 <~ normal(t1, noiseM)
m2 <~ normal(t2, noiseM)
````

Finally, we must return the information that we are interested in from our model. For measurement tuning, we are interested in the 
values of `m1` and `m2`. We would also like to know what kind of noise was generated in our model, `noiseT` and `noiseM`. We will
package these values together in related pairs. Instead of returning two seperate pairs of information, we will encapsulate the sets
into a container pair:

````nohighlight
return ((m1, m2), (noiseT, noiseM))
````

The return statement completes our model definition. We have defined two values, `noiseT` and `noiseM`, to represent the environmental
noise in the temperature and measurement samples. We generated two room temperatures, `t1` and `t2`, which we used to generate the 
dependent measurement samples `m1` and `m2`. Once all the values have been generated, we return an information set containing the two
measurement samples and the environmental noise. With our completed model, we can use Hakaru program transformations to determine 
plausible thermometer calibration values.

## Transformation ##

To calibrate our thermometers, we need to know how differences in environmental noises affect temperature measurements. For our scenario,
this means that we want to know what the conditional distribution on environmental noise given the measurement data. Unlike the [discrete
model example](discrete.md), this problem would be extremely difficult to reason about without transforming it in any way. 

To generate a conditional distribution for this problem, we will use Hakaru's [disintegrate transform](../transforms/disintegrate.md).
This transformation requires that the target model have a [return statement](../lang/rand.md) that presents information in the order of 
known information followed by unknown information. We have already configured our model in this manner, so we can run the `disintegrate`
transform immediately:

````nohighlight
fn x8 pair(real, real):
match x8:
(x25, x26):
  nT <~ uniform(+3/1, +8/1)
  nM <~ uniform(+1/1, +4/1)
  noiseT = real2prob(nT)
  noiseM = real2prob(nM)
  t1 <~ normal(+21/1, noiseT)
  t2 <~ normal(t1, noiseT)
  x28 <~ weight
           (exp((-(x25 - t1) ^ 2) / prob2real(2/1 * noiseM ^ 2))
            / noiseM
            / sqrt(2/1 * pi),
            return ())
  x27 <~ weight
           (exp((-(x26 - t2) ^ 2) / prob2real(2/1 * noiseM ^ 2))
            / noiseM
            / sqrt(2/1 * pi),
            return ())
  return (noiseT, noiseM)
_: reject. measure(pair(prob, prob))
````

An additional Hakaru transformation that can be performed at this stage is
the [Hakaru-Maple `simplify` subcommand](../transforms/hk-maple.md). This will
call Maple to algebraically simplify Hakaru models. The result is a more
efficient program, sampling from two `uniform` distributions instead of four.

````nohighlight
fn x8 pair(real, real):
match x8:
(r3, r1):
  weight
    (1/ pi * (1/2),
     nTd <~ uniform(+3/1, +8/1)
     nMb <~ uniform(+1/1, +4/1)
     weight
       (exp
          ((nMb ^ 2 * r1 ^ 2
            + nMb ^ 2 * r3 ^ 2
            + nTd ^ 2 * r1 ^ 2
            + nTd ^ 2 * r1 * r3 * (-2/1)
            + nTd ^ 2 * r3 ^ 2 * (+2/1)
            + nMb ^ 2 * r1 * (-42/1)
            + r3 * nMb ^ 2 * (-42/1)
            + r3 * nTd ^ 2 * (-42/1)
            + nMb ^ 2 * (+882/1)
            + nTd ^ 2 * (+441/1))
           / (nMb ^ 4 + nTd ^ 2 * nMb ^ 2 * (+3/1) + nTd ^ 4)
           * (-1/2))
        / sqrt(real2prob(nMb ^ 4 + nTd ^ 2 * nMb ^ 2 * (+3/1) + nTd ^ 4)),
        return (real2prob(nTd), real2prob(nMb))))
````

The two models are equivalent, so you must decide which model that you want to use for your application. For the purposes of this tutorial, we will use the
unsimplified version of the model (`thermometer_disintegrate.hk`).

Our thermometer model is two dimensional, so it is possible for us to tune our model values using importance sampling or an exhaustive search. However, these approaches
will not be possible in higher dimensions. Therefore, we will use a *Markov Chain Monte Carlo* method called *Metropolis-Hastings* to demonstrate how Hakaru can be used 
for problems with high dimensionality. To use the [Metropolis-Hastings transform](../transforms/mh.md), you must have a target distribution and a transition kernel. The 
thermometer model that we have already built will be our target distribution, but we have yet to create the transition kernel.

When specifying a model to be the transition kernel, our goal is to propose samples that are representative of the posterior model. For this example, we will hold one of 
the noise parameters constant will updating the other by drawing new values from a `uniform` distribution. This allows the sampler to remember a good setting for a parameter
when one is found, allowing it to concentrate on the remaining parameters:

````nohighlight
fn noise pair(prob, prob):
          match noise:
           (noiseTprev, noiseMprev):
            weight(1/2, 
                    noiseTprime <~ uniform(3,8)
                    return (real2prob(noiseTprime), noiseMprev)) <|>
            weight(1/2, 
                   noiseMprime <~ uniform(1,4)
                   return (noiseTprev, real2prob(noiseMprime)))
````

**Note: **Like any model in Hakaru, this program can be passed to other program transformations such as `hk-maple`. 

## Application ##

With both our target distribution and transition kernel defined, we can now use the Metropolis-Hastings method to transform our program. However, instead of calling `mh` in
the command prompt, we will include it as part of our Hakaru program by using the `mcmc(<kernel>, <target>)` syntactic transform:

````nohighlight
	mcmc(
		simplify(
		fn noise pair(prob, prob):
          match noise:
           (noiseTprev, noiseMprev):
            weight(1/2, 
                    noiseTprime <~ uniform(3,8)
                    return (real2prob(noiseTprime), noiseMprev)) <|>
            weight(1/2, 
                   noiseMprime <~ uniform(1,4)
                   return (noiseTprev, real2prob(noiseMprime))))
		  ,
		  simplify(
		  fn x8 pair(real, real):
			match x8:
			(r3, r1):
			  weight
				(1/ pi * (1/2),
				 nTd <~ uniform(+3/1, +8/1)
				 nMb <~ uniform(+1/1, +4/1)
				 weight
				   (exp
					  ((nMb ^ 2 * r1 ^ 2
						+ nMb ^ 2 * r3 ^ 2
						+ nTd ^ 2 * r1 ^ 2
						+ nTd ^ 2 * r1 * r3 * (-2/1)
						+ nTd ^ 2 * r3 ^ 2 * (+2/1)
						+ nMb ^ 2 * r1 * (-42/1)
						+ r3 * nMb ^ 2 * (-42/1)
						+ r3 * nTd ^ 2 * (-42/1)
						+ nMb ^ 2 * (+882/1)
						+ nTd ^ 2 * (+441/1))
					   / (nMb ^ 4 + nTd ^ 2 * nMb ^ 2 * (+3/1) + nTd ^ 4)
					   * (-1/2))
					/ sqrt(real2prob(nMb ^ 4 + nTd ^ 2 * nMb ^ 2 * (+3/1) + nTd ^ 4)),
					return (real2prob(nTd), real2prob(nMb)))))
      )
````

**Note:** Each model within the `mcmc` syntax must be wrapped within another syntactic transform. For this example, we are using the `simplify` transform.

The `mcmc` syntactic transform must also be wrapped in a Hakaru function that has the same type signature as the target model. Due to the self-referential nature of MCMC
methods, this function is referenced at the end of the target model's definition. We will call this function `recurse`:

````nohighlight
fn recurse pair(real, real):
	mcmc(
		simplify(
		fn noise pair(prob, prob):
          match noise:
           (noiseTprev, noiseMprev):
            weight(1/2, 
                    noiseTprime <~ uniform(3,8)
                    return (real2prob(noiseTprime), noiseMprev)) <|>
            weight(1/2, 
                   noiseMprime <~ uniform(1,4)
                   return (noiseTprev, real2prob(noiseMprime))))
		  ,
		  simplify(
		  fn x8 pair(real, real):
			match x8:
			(r3, r1):
			  weight
				(1/ pi * (1/2),
				 nTd <~ uniform(+3/1, +8/1)
				 nMb <~ uniform(+1/1, +4/1)
				 weight
				   (exp
					  ((nMb ^ 2 * r1 ^ 2
						+ nMb ^ 2 * r3 ^ 2
						+ nTd ^ 2 * r1 ^ 2
						+ nTd ^ 2 * r1 * r3 * (-2/1)
						+ nTd ^ 2 * r3 ^ 2 * (+2/1)
						+ nMb ^ 2 * r1 * (-42/1)
						+ r3 * nMb ^ 2 * (-42/1)
						+ r3 * nTd ^ 2 * (-42/1)
						+ nMb ^ 2 * (+882/1)
						+ nTd ^ 2 * (+441/1))
					   / (nMb ^ 4 + nTd ^ 2 * nMb ^ 2 * (+3/1) + nTd ^ 4)
					   * (-1/2))
					/ sqrt(real2prob(nMb ^ 4 + nTd ^ 2 * nMb ^ 2 * (+3/1) + nTd ^ 4)),
					return (real2prob(nTd), real2prob(nMb)))))(recurse)
      )
````

Our MCMC transform is now defined and ready to be processed. To convert this model into a form understood by the `hakaru` command, you must run the `hk-maple` transform:

````bash
$ hk-maple examples/documentation/thermometer_mcmc.hk
fn recurse pair(real, real):
x5 = x17 = fn x16 pair(prob, prob):
           1/1
           * (1/1)
           * (match x16:
              (x35, x36):
                x37 = prob2real(x35)
                x38 = prob2real(x36)
                match recurse:
                (r3, r1):
                  1/ pi
                  * (1/2)
                  * (match +3/1 <= x37 && x37 <= +8/1:
                     true:
                       1/ real2prob(+8/1 - (+3/1))
                       * (nTdd = prob2real(x35)
                          match +1/1 <= x38 && x38 <= +4/1:
                          true:
                            1/ real2prob(+4/1 - (+1/1))
                            * (x44 = ()
                               nMbb = prob2real(x36)
                               exp
                                 ((nMbb ^ 2 * r1 ^ 2
                                   + nMbb ^ 2 * r3 ^ 2
                                   + nTdd ^ 2 * r1 ^ 2
                                   + nTdd ^ 2 * r1 * r3 * (-2/1)
                                   + nTdd ^ 2 * r3 ^ 2 * (+2/1)
                                   + nMbb ^ 2 * r1 * (-42/1)
                                   + nMbb ^ 2 * r3 * (-42/1)
                                   + nTdd ^ 2 * r3 * (-42/1)
                                   + nMbb ^ 2 * (+882/1)
                                   + nTdd ^ 2 * (+441/1))
                                  / (nMbb ^ 4 + nMbb ^ 2 * nTdd ^ 2 * (+3/1) + nTdd ^ 4)
                                  * (-1/2))
                               / sqrt
                                   (real2prob(nMbb ^ 4 + nMbb ^ 2 * nTdd ^ 2 * (+3/1) + nTdd ^ 4))
                               * (1/1))
                          _: 0/1)
                     _: 0/1)
                _: 0/1
              _: 0/1)
     fn x16 pair(prob, prob):
     x0 <~ (fn noise pair(prob, prob):
            match noise:
            (r3, r1):
              weight
                (1/2,
                 noiseTprime7 <~ uniform(+3/1, +8/1)
                 return (real2prob(noiseTprime7), r1)) <|>
              weight
                (1/2,
                 noiseMprime9 <~ uniform(+1/1, +4/1)
                 return (r3, real2prob(noiseMprime9))))
             (x16)
     return (x0, x17(x0) / x17(x16))
fn x4 pair(prob, prob):
x3 <~ x5(x4)
match x3:
(x1, x2):
  x0 <~ x0 <~ categorical
                ([min(1/1, x2),
                  real2prob(prob2real(1/1) - prob2real(min(1/1, x2)))])
        return [true, false][x0]
  return if x0: x1 else: x4
````

**Note:** You can run the `hk-maple` function on the resulting program to 
[simplify it](https://github.com/hakaru-dev/hakaru/blob/master/examples/documentation/thermometer_mcmc_processed.hk).

With our model defined and processed, we can now assign it values to generate samples from. For the sake of this example, let's say that we observed temperature measurements
of 29\(^{\circ}\)C and 26\(^{\circ}\)C. To use these values, we must turn our anonymous Hakaru functions into callable ones so that we can assign them the pair (29,26). For
our transition kernel ([thermometer_mcmc_processed.hk](https://github.com/hakaru-dev/hakaru/blob/master/examples/documentation/thermometer_mcmc_processed.hk)), this change 
would be:

````nohighlight
therm = fn recurse pair(real, real):
 match recurse:
 ...
           return (rf, rd)))
therm((29,26))
````
**Note:** This is the simplified version of our transition kernel. Due to its length, this program has been shortened to make the changes more apparent.

After the same change, our target Hakru program ([thermometer_disintegrate_simplify.hk](https://github.com/hakaru-dev/hakaru/blob/master/examples/documentation/thermometer_disintegrate_simplify.hk))
becomes:

````nohighlight
thermometer = fn x8 pair(real, real):
 match x8:
 (r3, r1):
  weight
    (1/ pi * (1/2),
     nTd <~ uniform(+3/1, +8/1)
     nMb <~ uniform(+1/1, +4/1)
     weight
       (exp
          ((nMb ^ 2 * r1 ^ 2
            + nMb ^ 2 * r3 ^ 2
            + nTd ^ 2 * r1 ^ 2
            + nTd ^ 2 * r1 * r3 * (-2/1)
            + nTd ^ 2 * r3 ^ 2 * (+2/1)
            + nMb ^ 2 * r1 * (-42/1)
            + r3 * nMb ^ 2 * (-42/1)
            + r3 * nTd ^ 2 * (-42/1)
            + nMb ^ 2 * (+882/1)
            + nTd ^ 2 * (+441/1))
           / (nMb ^ 4 + nTd ^ 2 * nMb ^ 2 * (+3/1) + nTd ^ 4)
           * (-1/2))
        / sqrt(real2prob(nMb ^ 4 + nTd ^ 2 * nMb ^ 2 * (+3/1) + nTd ^ 4)),
        return (real2prob(nTd), real2prob(nMb))))
thermometer((29,26))
````

With these alterations, we can finally use the `hakaru` command to generate samples from our model:

````bash
$ hakaru --transition-kernel thermometer_mcmc_processed.hk thermometer_disintegrate_simplify.hk
(3.1995679303602578, 2.3093879567135325)
(3.1995679303602578, 2.3093879567135325)
(3.1995679303602578, 3.664010086898677)
(3.1995679303602578, 3.664010086898677)
(3.512655151270474, 3.664010086898677)
(6.535434584595698, 3.664010086898677)
(7.944581473529944, 3.664010086898677)
(6.960163985266382, 3.664010086898677)
(6.960163985266382, 1.850724571692917)
(6.960163985266382, 1.850724571692917)
(6.960163985266382, 1.850724571692917)
...
````

In the Hakaru system definition paper[^1], a graph is generated from the data by collecting every fifth sample from 20,000 generated 
samples. You can create a file with this information by using an `awk` script, which can then be imported into a graphing software
package such as Maple:

````bash
$ hakaru --transition-kernel thermometer_mcmc_processed.hk thermometer_disintegrate_simplify.hk | head -n 20000 | awk 'BEGIN{i = 0}{if (i % 5 == 0) a[i/5] = $0; i = i + 1}END{for (j in a) print a[j]}' > thermometer_output.txt
````

## Extra: A Syntactic Definition ##

This tutorial demonstrates how both command line and syntactic Hakaru transforms can be used in the same problem. This might not always be necessary because you might be able
to use only command line or only syntactic Hakaru transforms. For example, the thermometer model can be expressed 
[using only syntactic transforms](https://github.com/hakaru-dev/hakaru/blob/master/examples/documentation/thermometer_workflow.hk):

````nohighlight
simplify(
  fn x pair(real, real):
    mcmc(
      simplify(
        fn noise pair(prob, prob):
          match noise:
           (noiseTprev, noiseMprev):
            weight(1/2, 
                    noiseTprime <~ uniform(3,8)
                    return (real2prob(noiseTprime), noiseMprev)) <|>
            weight(1/2, 
                   noiseMprime <~ uniform(1,4)
                   return (noiseTprev, real2prob(noiseMprime))))
      ,
      simplify(
        disint(
          nT <~ uniform(3,8)
          nM <~ uniform(1,4)
          
          noiseT = real2prob(nT)
          noiseM = real2prob(nM)
          
          t1 <~ normal(21, noiseT)
          t2 <~ normal(t1, noiseT)
          
          m1 <~ normal(t1, noiseM)
          m2 <~ normal(t2, noiseM)
          
          return ((m1, m2), (noiseT, noiseM))))(x)
      )
)
````

This Hakaru program will produce [the same output program](https://github.com/hakaru-dev/hakaru/blob/master/examples/documentation/thermometer_workflow_res.hk) as the 
mixed-usage example when evaluated using `hk-maple`.

[^1]: P. Narayanan, J. Carette, W. Romano, C. Shan and R. Zinkov, "Probabilistic Inference by Program Transformation in Hakaru (System Description)", Functional and Logic 
Programming, pp. 62-79, 2016.
