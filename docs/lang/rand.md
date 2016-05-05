# Primitive Probability Distributions

Hakaru comes with a small set of primitive probability
distributions.

|<h4>normal(mean. *real*, standard_deviation. *prob*): *measure(real)* </h4> |
|----------------------------------------------------------------------------|
| univariate Normal (Gaussian) distribution                                  |

|<h4>uniform(low. *real*, high. *real*): *measure(real)* </h4>                          |
|---------------------------------------------------------------------------------------|
| Uniform distribution is a continuous univariate distribution defined from low to high |

|<h4>gamma(shape. *prob*, scale. *prob*): *measure(prob)* </h4>              |
|--------------------------------------------------------------------------- |
| Gamma distribution with shape and scale parameterization                   |

|<h4>beta(a. *prob*, b. *prob*): *measure(prob)* </h4>                       |
|--------------------------------------------------------------------------- |
| Beta distribution                                                          |

|<h4>poisson(l. *prob*): *measure(nat)* </h4>                                |
|--------------------------------------------------------------------------- |
| Poisson distribution                                                       |

|<h4>categorical(v. *array(prob)*): *measure(nat)* </h4>                     |
|--------------------------------------------------------------------------- |
| Categorical distribution                                                   |

|<h4>dirac(x. *a*): *measure(a)* </h4>                                       |
|--------------------------------------------------------------------------- |
| Dirac distribution                                                         |

The Dirac distribution appears often enough, that we have given an
additional keyword in our language for it: `return`. The following
programs are equivalent.

````nohighlight
dirac(3)
````

````nohighlight
return 3
````

|<h4>weight(x. *prob*, m. *measure(a)*): *measure(a)* </h4>                  |
|--------------------------------------------------------------------------- |
| a *m* distribution, reweighted by *x*                                      |


|<h4>reject: *measure(a)* </h4>                                              |
|--------------------------------------------------------------------------- |
| The distribution over the empty set                                        |


Finally, we have a binary choice operator `<|>`, which takes two
distributions, and returns an unnormalized distribution which returns
one or the other.  For example, to get a distribution which where with
probability 0.5 draws from a uniform(0,1), and probability 0.5 draws
from uniform(5,6).

````nohighlight
weight(0.5, uniform(0,1)) <|>
weight(0.5, uniform(5,6))
````
