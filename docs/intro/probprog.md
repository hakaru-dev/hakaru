# What is Probabilistic Programming?

Probabilistic programs are programs which represent probability
distributions. For example, the program `poisson(5)` represents the
poisson distribution with a rate of five. Why do we need a
language for describing probability distributions?

The world is intrinsically an uncertain place. When we try to predict
what will happen in the world given some data we have collected, we
are inherently engaging in some sort of probabilistic modeling. In
probabilistic modeling, we treat the quantity we wish to predict as a
parameter, and then describe our data as some noisy function of this
parameter. This function is called *likelihood*, and depending on which
statistical regime you use can be used in predominately two ways.

For instance, we might want to estimate the average time it takes for
a bus to arrive at a stop, based on actual arrival times. In this situation,
the likelihood function would be:

$$ x \sim \text{Poisson}(\lambda) $$

where $x$ is the actual arrival time, and $\lambda$ is the quantity we
wish to predict. In other words, this likelihood says our data is a
noisy measurement of ther average waiting time which follows a Poisson
distribution. We can also represent this likelihood function as a
density function which for a given choice of $\lambda$ returns how
likely it is for $x$ to be generated under that parameter.

$$ f(\lambda) = \frac{\lambda^x e^{-\lambda}}{x!} $$

Under a frequentist regime we perform maximum likelihood, where we find
the best parameter by finding the $\lambda$ which maximizes $f$.

Under a Bayesian regime, we don't estimate a single best value for the
parameter. Instead we place a prior distribution on the parameters and
estimate that posterior distribution conditioned on our data.

In Hakaru, it is possible to use either regime for solving your
problems.  We will call the distribution or program which describes
our data the *model*.

## Tug of War

We demonstrate the value of this problem-solving approach using a
simplified version of the
[tug of war](https://probmods.org/generative-models.html#example-bayesian-tug-of-war)
example from probmods.org. For this problem we will take a Bayesian
approach to prediction.

For this problem, we have three friends, Alice, Bob and Carol who take
turns playing a tug of war against each other and we'd like to know
which of them is the strongest. We can pose this problem as a
probabilistic program. In particular, we will try to predict who will
win match3 given we have observed who won the first two matches.

We can start by assuming each player's strength comes from a standard
normal distribution. Then we assume the strength they pull with some
normal distribution centered around their true strength, and the
person who pulled harder wins.

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

We then restrict the set of events to only those where Alice won the
first match and Bob won the second, and return the results of the
third match.

````nohighlight
if match1 && match2:
   return match3
else:
   reject. measure(bool)
````

We can then run the above model using hakaru, which shows that Alice
is likely to win her match against Carol.

````bash
hakaru tugofwar.hk | head -n 10000 | sort | uniq -c
   3060 false
   6940 true
````

## Simulation vs Inference

Of course, in the above program we performed inference, by taking
our model and throwing out all events that didn't agree with
the data we had. How well would this work if we changed our
model slightly? Suppose our data wasn't boolean values, but instead
the difference of strengths, and we want to not just whether Alice
will win, but by how much.

As we pose more complex questions, posing our models as rejection
samplers becomes increasing inefficient.

<div class="panel panel-warning">
    <div class="panel-heading">
        <h4 class="panel-title">TODO</h4>
	</div>
	<div class="panel-body">
        Explain simplify and mh
	</div>
</div>

