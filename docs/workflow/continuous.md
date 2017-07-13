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

## Application ##

[^1]: P. Narayanan, J. Carette, W. Romano, C. Shan and R. Zinkov, "Probabilistic Inference by Program Transformation in Hakaru (System Description)", Functional and Logic 
Programming, pp. 62-79, 2016.