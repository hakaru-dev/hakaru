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
- The initial temperature of the room is 21\(^{\circ}\)C
- Temperature and measurement samples follow a normal distribution

````nohighlight
nT <~ uniform(3,8)
nM <~ uniform(1,4)

noiseT = real2prob(nT)
noiseM = real2prob(nM)

t1 <~ normal(21, noiseT)
t2 <~ normal(t1, noiseT)

m1 <~ normal(t1, noiseM)
m2 <~ normal(t2, noiseM)

return ((m1, m2), (noiseT, noiseM))
````

## Transformation ##

## Application ##

[^1]: P. Narayanan, J. Carette, W. Romano, C. Shan and R. Zinkov, "Probabilistic Inference by Program Transformation in Hakaru (System Description)", Functional and Logic 
Programming, pp. 62-79, 2016.