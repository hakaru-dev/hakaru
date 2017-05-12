# What is Probabilistic Programming?

Probablilistic programming is a software-driven method for creating and testing probabilistic models and distributions to automate parts of the model testing process. It 
provides a means for writing programs which describe probabilistic models and distributions such that they can be used to make probabilistic inferences. For example, the 
Hakaru program \(poisson(5)\) represents the Poisson distribution with a rate of five. A Probabilistic Programming Language (PPL) is a computer language designed to 
describe probabalistic models and distributions such that probabilistic inferences can be made programmatically[^1]. Hakaru is an example of a PPL. 

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

There are two main approaches to statistical reasoning: Frequentist and Bayesian. In Frequentist reasoning, the goal is to maximize the liklihood function. In the density
model for our bus arrival times, this would mean finding a value for \(\lambda\) that maximizes \(f\). In Bayesian reasoning, an estimation is made using the given 
function parameters and a conditioned data set collected for the event. For our density model, we would design an estimation functions using our parameters and given it
our set of bus arrival times to predict a value for \(f\). You can use either approach to probabilistic reasoning in your Hakaru programs. 

## Example: Bayesian Tug-of-War ##

To demonstrate the value of this problem-solving approach, we will write a Hakaru program to represent a simplified version of the 
[tug-of-war](https://probmods.org/v1/generative-models.html#example-bayesian-tug-of-war) example from probmods.org.

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

Now that you have created your model, you can create inference rules based on known data. In the third match, Alice is competing against Carol. She wants to know how 
likely she is to win the match. She won her match against Bob (`match1`) and that Carol lost her match to Bob (`match2`). 

In your model, the result of `match1` is `True` when Alice wins and the result of `match2` is `True` when Carol loses. You can use this knowledge to write an inference
rule for your scenario that will return the result of `match3` when Alice wins `match1` and Carol loses `match2`. If a simulation is run that does not match this pattern,
it is rejected. This inference rule can be written in Hakaru as:

````nohighlight
if match1 && match2:
   return match3
else:
   reject. measure(bool)
````

You have now created a Hakaru program that describes a probabilistic model and an inference rule based on known data. You should save your program as `tugofwar.hk` so that
you can run Hakaru to infer the outcome of `match3`. 

If you call `hakaru tugofwar.hk`, you will get a continuous stream of Boolean results. You can make the calculations more legible by restricting the number of program 
executions and counting how many of each Boolean appears. For example, if you restrict the number of program executions to 10000 and collect the results, you will see that 
`True` occurs much more frequently than `False`. This means that Alice is likely to win `match3` against Carol.

````bash
hakaru tugofwar.hk | head -n 10000 | sort | uniq -c
   3060 false
   6940 true
````

## Simulation vs Inference

Of course, in the above program we performed inference, by taking our model and throwing out all events that didn't agree with the data we had. How well would this work if 
we changed our model slightly? Suppose our data wasn't boolean values, but instead the difference of strengths, and we want to not just whether Alice will win, but by how 
much.

As we pose more complex questions, posing our models as rejection samplers becomes increasing inefficient. Instead we would like to directly transform our models into those 
which only generate the data we observed and don't waste any computation simulating data which we know will never exist.

### Metropolis Hastings

By default hakaru performs importance sampling. This works well for inference in low dimensions, but we want to use MCMC for more realistic problems. Hakaru provides a `mh` 
command tool to transform probabilistic programs into a Markov Chain.

[^1]: [Proababilistic programming language (Wikipedia)](https://en.wikipedia.org/wiki/Probabilistic_programming_language)