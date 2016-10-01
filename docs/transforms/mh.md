# Metropolis Hastings transform

In Hakaru, all inference algorithms are represented as program
transformations. In particular, the Metropolis-Hastings transform
takes as input a probabilistic program representing the target
distribution, and a probabilistic program representing the proposal
distribution and returns a probabilistic program representing the MH
transition kernel.

## mh command

You can access this functionality using the `mh` command. It takes
two files as input representing the target distribution and proposal
kernel.
