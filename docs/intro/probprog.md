# What is Probabilistic Programming?

Probabilistic programming is a software-driven method for creating probabilistic models and then using them to make probabilistic inferences. It 
provides a means for writing programs which describe probabilistic models such that they can be used to make probabilistic inferences. For example, the 
Hakaru program \(poisson(5)\) represents the Poisson distribution with a rate of five. A Probabilistic Programming Language (PPL) is a computer language designed to 
describe probabilistic models and distributions such that probabilistic inferences can be made programmatically[^1]. Hakaru is an example of a PPL. 

Why do we need a programming language for describing probability distributions? Consider a machine learning problem. A typical workflow for this type of design is, when 
presented with a problem, to design an inference algorithm for a specific probabilistic distribution and query. The development of a distribution, query, and inference
algorithm can be a time consuming task, even for someone that is skilled in these areas. Automating this process via a PPL allows for a broader exploration of the design
space without the added effort that is required to using a traditional approach.

## Probabilistic Models ##

The world is intrinsically an uncertain place. When you try to predict what will happen in the world given some data you have collected, you are engaging in some
sort of probabilistic modeling. A distribution or program that describes your data is called the *model*. In probabilistic modeling, the quantity you wish to predict is 
treated as a parameter and known data is described as some noisy function of this parameter. This function is called the *likelihood* of the parameter. 

For example, you might want to estimate the average time it takes for a bus to arrive at a stop based on actual arrival times. In this situation, you determine that you
can represent the likelihood function using a Poisson distribution:

$$ x \sim \text{Poisson}(\lambda) $$

where \( x \) is the actual arrival time, and \(\lambda\) is the quantity you are using to make the prediction. 

You can also represent this likelihood function as a density function which returns how likely it is for \(x\) to be generated for a given choice of \(\lambda\):

$$ f(\lambda) = \frac{\lambda^x e^{-\lambda}}{x!} $$

## Methods of Probabilistic Reasoning ##

There are two main approaches to statistical reasoning: Frequentist and Bayesian. In Frequentist reasoning, the goal is to maximize the likelihood function. In the density
model for our bus arrival times, this would mean finding a value for \(\lambda\) that maximizes \(f\). In Bayesian reasoning, an estimation is made using the given 
function parameters and a conditioned data set collected for the event. For our density model, we would design an estimation functions using our parameters and given it
our set of bus arrival times to predict a value for \(f\). You can use either approach to probabilistic reasoning in your Hakaru programs. 

## Example: Bayesian Tug-of-War ##

To demonstrate the value of this problem-solving approach, we will write a Hakaru program to represent a simplified version of the 
[tug-of-war](https://probmods.org/v1/generative-models.html#example-bayesian-tug-of-war) example from probmods.org. A completed version of this program can be found
in the [Hakaru examples directory](https://github.com/hakaru-dev/hakaru/blob/master/examples/tugofwar_rejection.hk).

Three friends, Alice, Bob and Carol, want to know which of them is the strongest. They decide that the winner of a game of tug-of-war must be stronger than their opponent,
and arrange to take turns playing tug-of-war against each other. The person who wins the most matches will be deemed the strongest of them.

You can write a probabilistic program to represent this scenario. In this simulation, the friends are only interested in knowing who will win the third match (`match3`) 
when they already know who won the first two matches. You can represent this problem using either the frequentist or Bayesian reasoning methods, but this example will use 
the Bayesian approach.

Your program will begin with the description of the probabilistic model. You can assume that each friend's strength comes from a standard normal distribution and that the 
strength that they pull with also follows some normal distribution centered around their true strength. You can also trivially assume that the friend that pulled the 
hardest will win the match. You can represent this model in Hakaru by writing:

````nohighlight
def pulls(strength real):
    normal(strength, 1)

def winner(a real, b real):
	a_pull <~ pulls(a)
	b_pull <~ pulls(b)
	return (a_pull > b_pull)

alice <~ normal(0,1)
bob   <~ normal(0,1)
carol <~ normal(0,1)

match1 <~ winner(alice, bob)
match2 <~ winner(bob, carol)
match3 <~ winner(alice, carol)
````

**Note:** This Hakaru code will not compile yet.

Now that you have created your model, you can condition your sample generation based on known data. In the third match, Alice is competing against Carol. She wants to know 
how likely she is to win the match. She won her match against Bob (`match1`) and that Carol lost her match to Bob (`match2`). 

In your model, the result of `match1` is `True` when Alice wins and the result of `match2` is `True` when Carol loses. You can use this knowledge to write a conditions for 
your scenario that will return the result of `match3` when Alice wins `match1` and Carol loses `match2`. If a simulation is run that does not match this pattern, it is 
rejected. This restriction can be written in Hakaru as:

````nohighlight
if match1 && match2:
   return match3
else:
   reject. measure(bool)
````

You have now created a Hakaru program that describes a probabilistic model and restricted the accepted samples based on known data. You should save your program as 
`tugofwar_rejection.hk` so that you can run Hakaru to infer the outcome of `match3`. 

If you call `hakaru tugofwar_rejection.hk`, you will get a continuous stream of Boolean results. You can make the calculations more legible by restricting the number of 
program executions and counting how many of each Boolean appears. For example, if you restrict the number of program executions to 10000 and collect the results, you will 
see that `True` occurs much more frequently than `False`. This means that Alice is likely to win `match3` against Carol.

````bash
hakaru -w tugofwar_rejection.hk | head -n 10000 | sort | uniq -c
   3060 false
   6940 true
````

## Simulation and Inference

Ideally, you could collect a sufficient number of samples from your observed population to create your probabilistic model. This could be accomplished with populations that
only require a manageable number of samples or that are easy to collect. However, for many experiments this is not possible due to limited resources and time. In cases like
this, you could generate samples using a *simulation*. In a simulation, you can select the population's mean and then generate values around this data point. If you wanted 
to know what a population would look like with a different mean, you simply need to change that value in your model and run the simulation again. 

What about the cases where you do have some samples and you want to know something about it? In this case, you use the data you have to guide the generation of samples in 
order to learn how the data occurred. This approach is called *inference*. To be able to make inferences from your known samples, you must add reasoning mechanisms to your 
model to gauge the usefulness of a model-generated sample with respect to some data that you have already collected. For example, you might have collected some disease data 
from a hospital and want to know how it spread in the affected patients. After creating a probabilistic model of disease transmission, you can use your collected data 
to reason about the samples generated from your model to judge its relevance in the creation of the data that you have collected.

In the tug-of-war example, you used Hakaru to restrict which samples were kept (Alice must have won `match1` and Bob must have won `match2`) and which ones were discarded. 
This inference approach is called *rejection sampling* because restricted samples generated from your model are discarded. Would this approach still work if the model were 
changed? Could we use this same technique to determine if Alice will win her match and by how much?

As you pose more complex questions, creating models as rejection samplers becomes increasingly inefficient because of the number of discarded samples. It would be
better if your model could be transformed such that only observed data points are generated so that computational resources are not wasted on data that will not exist in 
your data set.

Hakaru uses *importance sampling* where, instead of being rejected immediately, each sample is assigned a weight so that a sample average can be calculated. As more 
samples are generated, sample weights are updated to reflect the likelihood of that sample's rejection. While this works well for model inference when the model has
only a few dimensions, there are more powerful tools that can be used for more complex scenarios.

### The Metropolis-Hastings Algorithm: A Markov Chain Monte Carlo Method

You might encounter situations where direct sampling from your model is difficult, which is common for multi-dimensional models. In models with high dimensionality, sample 
points tend to cluster in regions so that when a "good" sample is found, there is a higher chance of finding other good samples in the same area. This means that we want to 
stay in that region to collect more. In this situation, importance sampling becomes less efficient because it does not consider what other samples it has already found when
generating a new one. Instead, a Markov Chain Monte Carlo (MCMC) method should be used. 

The MCMC methods are used to sample probability distributions by constructing a Markov Chain. A Markov Chain is used to make predictions solely based on a process's current 
state, so it does not require extensive memory for its calculations. In MCMC, a Markov chain is used to generate the next sample based on the current one, making it more 
likely to stay in densely packed probability regions. As a model increases in dimensions, MCMC methods become essential for the generation of samples because the task of 
finding high-value samples becomes more difficult.

The Metropolis-Hastings algorithm[^2] is an MCMC method for generating a sequence of random samples from a probabilistic distribution. This is useful for approximating a 
distribution that fits your existing data. The algorithm is included in Hakaru's transformations as the command tool [`mh`](../transforms/mh.md). This transform converts
your probabilistic program into a Markov Chain which can be used for sample generation.

[^1]: [Proababilistic programming language (Wikipedia)](https://en.wikipedia.org/wiki/Probabilistic_programming_language)
[^2]: D.J.C. MacKay, "Introduction to Monte Carlo Methods", Learning in Graphical Models, vol. 89, pp. 175-204, 1998.
