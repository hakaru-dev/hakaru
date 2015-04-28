RoadmapHMM.hs is an example of how Hakaru in the future would be used to
perform a combination of MCMC and exact inference on a discrete hidden
Markov model.  It contains four related programs, starting with the model
and ending with inference:

* roadmapProg1 is the *joint* distribution on observations and parameters.
* roadmapProg2 is the distribution on parameters *conditioned* on
  observations.
* roadmapProg3 is the same distribution as roadmapProg2, but computed exactly
  in polynomial time using *matrix multiplication*.
* roadmapProg4 is a *Metropolis-Hastings* transition kernel that samples
  parameters from the posterior, using the exact computation in roadmapProg3
  to figure the acceptance ratio.

Each adjacent pair of these programs is related by a transformation:

* Producing roadmapProg2 from roadmapProg1 requires *disintegration*.
* Producing roadmapProg3 from roadmapProg2 requires changing to a
  *specialized representation* of measures.
* Producing roadmapProg4 from roadmapProg3 requires *disintegration*
  (for probability density) and *simplification*.

Because the step from roadmapProg2 to roadmapProg3 involves only the part of
the model that samples the observations, not the part that samples the
parameters, we detail this step in HMM.hs and further in HMMDeriv.hs.

----

EasierRoadmap.hs is an example of how Hakaru today can be used to perform
a combination of MCMC and exact inference on a model without arrays, namely
two time steps of a linear dynamic model in one dimension.  Like
RoadmapHMM.hs, EasierRoadmap.hs contains four related programs, starting
with the model and ending with inference:

* easierRoadmapProg1 is the *joint* distribution on observations and
  parameters.
* easierRoadmapProg2 is the distribution on parameters *conditioned* on
  observations.
* easierRoadmapProg3 is the same distribution as easierRoadmapProg2, but
  computed exactly by symbolically *integrating out* latent variables.
* easierRoadmapProg4 is a *Metropolis-Hastings* transition kernel that
  samples parameters from the posterior, using the exact computation in
  easierRoadmapProg3 to figure the acceptance ratio.

Each adjacent pair of these programs is related by a transformation:

* Producing roadmapProg2 from roadmapProg1 requires *disintegration*.
* Producing roadmapProg3 from roadmapProg2 requires *simplification*.
* Producing roadmapProg4 from roadmapProg3 requires *disintegration*
  (for probability density) and *simplification*.

----

HMMContinuous.hs is like HMM.hs but for an HMM whose states are continuous
rather than discrete.  More specifically, HMMContinuous.hs shows a linear
dynamic model in one dimension, and how it could be turned into a Kalman
filter.
