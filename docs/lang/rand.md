# Primitive Probability Distributions

Hakaru comes with a small set of primitive probability
distributions.

|<h4>normal(mean. *real*, standard_deviation. *prob*): *measure(real)* </h4> | |
|----------------------------------------------------------------------------|-|
| univariate Normal (Gaussian) distribution                                  |-|

|<h4>uniform(low. *real*, high. *real*): *measure(real)* </h4>                          | |
|---------------------------------------------------------------------------------------|-|
| Uniform distribution is a continuous univariate distribution defined from low to high |-|

|<h4>gamma(shape. *prob*, scale. *prob*): *measure(prob)* </h4>              | |
|--------------------------------------------------------------------------- |-|
| Gamma distribution with shape and scale parameterization                   |-|

|<h4>beta(a. *prob*, b. *prob*): *measure(prob)* </h4>                       | |
|--------------------------------------------------------------------------- |-|
| Beta distribution                                                          |-|

|<h4>poisson(l. *prob*): *measure(nat)* </h4>                                | |
|--------------------------------------------------------------------------- |-|
| Poisson distribution                                                       |-|

|<h4>categorical(v. *array(prob)*): *measure(nat)* </h4>                     | |
|--------------------------------------------------------------------------- |-|
| Categorical distribution                                                   |-|

|<h4>dirac(x. *a*): *measure(a)* </h4>                                       | |
|--------------------------------------------------------------------------- |-|
| Dirac distribution                                                         |-|

The Dirac distribution appears often enough, that we have given an
additional keyword in our language for it: `return`. The following
programs are equivalent.

````nohighlight
dirac(3)
````

````nohighlight
return 3
````
|<h4>lebesgue(low. *real*, high.*real*): *measure(real)* </h4>               | |
|--------------------------------------------------------------------------- |-|
| the distribution constant between `low` and `high` and zero elsewhere. `high` must be at least `low`. |-|


|<h4>weight(x. *prob*, m. *measure(a)*): *measure(a)* </h4>                  | |
|--------------------------------------------------------------------------- |-|
| a *m* distribution, reweighted by *x*                                      |-|


|<h4>reject: *measure(a)* </h4>                                              | |
|--------------------------------------------------------------------------- |-|
| The distribution over the empty set                                        |-|


Finally, we have a binary choice operator `<|>`, which takes two
distributions, and returns an unnormalized distribution which returns
one or the other.  For example, to get a distribution which where with
probability 0.5 draws from a uniform(0,1), and probability 0.5 draws
from uniform(5,6).

````nohighlight
weight(0.5, uniform(0,1)) <|>
weight(0.5, uniform(5,6))
````
# Standard Library Distributions

## Discrete

|<h4>benford() : *measure(real)* </h4>                                       | |
|----------------------------------------------------------------------------|-|
| Benford distribution                                                      |-|

|<h4>bernoulli(p. *prob*): *measure(nat)* </h4>                              | |
|----------------------------------------------------------------------------|-|
| Bernoulli distribution                                                     |-|

|<h4>betaBinomial(a. *prob*, b. *prob*, n. *nat*): *measure(nat)* </h4>      | |
|----------------------------------------------------------------------------|-|
| Beta-Binomial distribution                                                 |-|

|<h4>betaPascal(n. *nat*, a. *prob*, b. *prob*): *measure(nat)* </h4>        | |
|----------------------------------------------------------------------------|-|
| Beta-Pascal distribution                                                   |-|

|<h4>binomial(n. *nat*, p. *prob*): *measure(nat)* </h4>                     | |
|----------------------------------------------------------------------------|-|
| Binomial distribution                                                      |-|

|<h4>natUniform(n1. *nat*, n1. *nat*): *measure(nat)* </h4>                  | |
|----------------------------------------------------------------------------|-|
| Discrete Uniform distribution                                              |-|

|<h4>intUniform(n1. *int*, n1. *int*): *measure(int)* </h4>                  | |
|----------------------------------------------------------------------------|-|
| Integer Uniform distribution                                               |-|

|<h4>discreteWeibull(p. *prob*, beta. *prob*): *measure(int)* </h4>            | |
|------------------------------------------------------------------------------|-|
| Discrete Weibull distribution                                                |-|

|<h4>gammaPoisson(shape. *prob*, scale. *prob*): *measure(prob)* </h4>       | |
|----------------------------------------------------------------------------|-|
| Gamma-Poisson distribution                                                 |-|

|<h4>geometric(p. *prob*): *measure(nat)* </h4>                                | |
|------------------------------------------------------------------------------|-|
| Geometric distribution                                                       |-|

|<h4>hyperGeo(n. *nat*, k. *nat*, r. *nat*): *measure(nat)* </h4>              | |
|------------------------------------------------------------------------------|-|
| Hypergeometric distribution                                                  |-|

|<h4>logarithm(c. *prob*): *measure(int)* </h4>                                | |
|------------------------------------------------------------------------------|-|
| Logarithm distribution                                                       |-|

|<h4>negativeHyperGeometric(n. *nat*, k. *nat*, r. *nat*): *measure(nat)* </h4>| |
|------------------------------------------------------------------------------|-|
| Negative Hypergeometric distribution                                         |-|

|<h4>pascal(n. *nat*, p. *prob*): *measure(nat)* </h4>                         | |
|------------------------------------------------------------------------------|-|
| Pascal distribution                                                          |-|

|<h4>polya(n. *nat*, p. *prob*, beta. *prob*): *measure(nat)* </h4>            | |
|------------------------------------------------------------------------------|-|
| Polya distribution                                                           |-|

|<h4>powerSeries(a. *prob*, c. *prob*): *measure(nat)* </h4>                   | |
|------------------------------------------------------------------------------|-|
| Power Series distribution                                                    |-|

|<h4>zeta(alpha. *prob*): *measure(nat)* </h4>                                 | |
|------------------------------------------------------------------------------|-|
| Zeta distribution                                                            |-|

## Continuous

|<h4>arcsin(): *measure(prob)* </h4>                                         | |
|----------------------------------------------------------------------------|-|
| Arcsine distribution                                                       |-|

|<h4>cauchy(a. *real*, alpha. *prob*): *measure(real)*</h4>                  | |
|----------------------------------------------------------------------------|-|
| Cauchy distribution                                                        |-|

|<h4>chi(means. *array(real)*, stdevs. *array(prob)*): *measure(prob)* </h4>  | |
|-----------------------------------------------------------------------------|-|
| Chi distribution                                                            |-|

|<h4>chi(means. *array(real)*, stdevs. *array(prob)*): *measure(prob)* </h4>  | |
|-----------------------------------------------------------------------------|-|
| Chi Square distribution                                                     |-|

|<h4>erlang(shape. *prob*, scale. *nat*) : *measure(prob)* </h4>             | |
|----------------------------------------------------------------------------|-|
| Erlang distribution                                                        |-|

|<h4>exponential(alpha. *prob*) : *measure(prob)* </h4>                      | |
|----------------------------------------------------------------------------|-|
| Exponential distribution                                                   |-|

|<h4>exponentialPower(lambda. *prob*, kappa. *prob*): *measure(prob)* </h4>  | |
|----------------------------------------------------------------------------|-|
| Exponential Power distribution                                             |-|

|<h4>extremeValue(alpha. *prob*, beta. *prob*) : *measure(real)* </h4>       | |
|----------------------------------------------------------------------------|-|
| Extreme Value distribution                                                 |-|

|<h4>F(n1. *nat*, n2. *nat*): *measure(nat)* </h4>                           | |
|----------------------------------------------------------------------------|-|
| F distribution                                                             |-|

|<h4>T(n. *nat* ): *measure(nat)* </h4>                                      | |
|----------------------------------------------------------------------------|-|
| T distribution                                                             |-|

|<h4>gammaNormal(mu. *real*, alpha. *prob*, beta. *prob*) : *measure(real)* </h4>| |
|--------------------------------------------------------------------------------|-|
| Gamma-Normal distribution                                                      |-|

|<h4>generalizedPareto(delta. *prob*, kappa. *prob*, gamma. *prob*) : *measure(prob)* </h4>| |
|------------------------------------------------------------------------------------------|-|
| Generalized Pareto distribution                                                          |-|

|<h4>gompertz(delta. *prob*, kappa. *prob*) : *measure(prob)* </h4>          | |
|----------------------------------------------------------------------------|-|
| Gompertz distribution                                                      |-|

|<h4>hyperbolicSecant(): *measure(real)* </h4>                               | |
|----------------------------------------------------------------------------|-|
| Hyperbolic Secant distribution                                             |-|

|<h4>hyperexponential(alpha. *array(prob)*, p. *array(prob)*: *measure(prob)* </h4>| |
|----------------------------------------------------------------------------------|-|
| Hyperexponential distribution                                                    |-|

|<h4>hypoexponential(alpha. *array(prob)*): *measure(prob)* </h4>            | |
|----------------------------------------------------------------------------|-|
| Hyperexponential distribution                                              |-|

|<h4>IDB(delta. *prob*, kappa. *prob*, gamma. *prob*) : *measure(prob)* </h4>| |
|----------------------------------------------------------------------------|-|
| IDB distribution                                                           |-|

|<h4>invGaussian(lambda. *prob*, mu. *prob*): *measure(prob)* </h4>          | |
|----------------------------------------------------------------------------|-|
| Inverted Gaussian distribution                                             |-|

|<h4>invBeta(a. *prob*, b. *prob*): *measure(prob)* </h4>                    | |
|----------------------------------------------------------------------------|-|
| Inverted Beta distribution                                                 |-|

|<h4>invGamma(shape. *prob*, scale. *prob*) : *measure(prob)* </h4>          | |
|----------------------------------------------------------------------------|-|
| Inverted Gamma distribution                                                |-|

|<h4>laplace(alpha. *prob*, beta. *prob*) : *measure(real)* </h4>            | |
|----------------------------------------------------------------------------|-|
| Laplace distribution                                                       |-|

|<h4>logGamma(alpha. *prob*, beta. *prob*) : *measure(real)* </h4>           | |
|----------------------------------------------------------------------------|-|
| Log Gamma distribution                                                     |-|

|<h4>log_logistic(lambda. *prob*, kappa. *prob*): *measure(prob)* </h4>      | |
|----------------------------------------------------------------------------|-|
| Log Logistic distribution                                                  |-|

|<h4>logistic(lambda. *prob*, kappa. *prob*): *measure(prob)* </h4>          | |
|----------------------------------------------------------------------------|-|
| Logistic distribution                                                      |-|

|<h4>logisticExponential(lambda. *prob*, kappa. *prob*): *measure(prob)* </h4>| |
|-----------------------------------------------------------------------------|-|
| Logistic Exponential distribution                                           |-|

|<h4>lomax(lambda. *prob*, kappa. *prob*): *measure(prob)* </h4>             | |
|----------------------------------------------------------------------------|-|
| Lomax distribution                                                         |-|

|<h4>makeham(delta. *prob*, kappa. *prob*, gamma. *prob*) : *measure(prob)* </h4>| |
|--------------------------------------------------------------------------------|-|
| Makeham distribution                                                           |-|

|<h4>minimax(beta. *prob*, gamma. *prob*): *measure(prob)* </h4>             | |
|----------------------------------------------------------------------------|-|
| Minimax distribution                                                       |-|

|<h4>nonCentralChiSq(means. *array(real)*, stdevs. *array(prob)*): *measure(prob)* </h4>| |
|---------------------------------------------------------------------------------------|-|
| Noncentral Chi Square distribution                                                    |-|

|<h4>nonCentralT(n. *nat*, delta. *prob*): *measure(prob)* </h4>             | |
|----------------------------------------------------------------------------|-|
| Noncentral T distribution                                                  |-|

|<h4>pareto(lambda. *prob*, kappa. *prob*) : *measure(prob)* </h4>           | |
|----------------------------------------------------------------------------|-|
| Pareto distribution                                                        |-|

|<h4>power(alpha. *prob*, beta. *prob*) : *measure(prob)* </h4>              | |
|----------------------------------------------------------------------------|-|
| Power distribution                                                         |-|

|<h4>rayleigh(alpha. *prob*) : *measure(prob)* </h4>                         | |
|----------------------------------------------------------------------------|-|
| Rayleigh distribution                                                      |-|

|<h4>stdCauchy() : *measure(real)* </h4>                                     | |
|----------------------------------------------------------------------------|-|
| Standard Cauchy distribution                                               |-|

|<h4>stdNormal() : *measure(real)* </h4>                                     | |
|----------------------------------------------------------------------------|-|
| Standard Normal distribution                                               |-|

|<h4>standardPower(beta. *prob*) : *measure(prob)* </h4>                     | |
|----------------------------------------------------------------------------|-|
| Standard Power distribution                                                |-|

|<h4>stdTriangle() : *measure(real)* </h4>                                   | |
|----------------------------------------------------------------------------|-|
| Standard Triangular distribution                                           |-|

|<h4>stdWald(lambda. *prob*): *measure(prob)* </h4>                          | |
|----------------------------------------------------------------------------|-|
| Standard Wald distribution                                                 |-|

|<h4>triangle(a. *real*, m. *real*, b. *real*) : *measure(real)* </h4>       | |
|----------------------------------------------------------------------------|-|
| Triangular distribution                                                    |-|

|<h4>weibull(alpha. *prob*, beta. *prob*) : *measure(prob)* </h4>            | |
|----------------------------------------------------------------------------|-|
| Weibull distribution                                                       |-|
