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

## Transformation ##

## Application ##

[^1]: P. Narayanan, J. Carette, W. Romano, C. Shan and R. Zinkov, "Probabilistic Inference by Program Transformation in Hakaru (System Description)", Functional and Logic 
Programming, pp. 62-79, 2016.