RoadmapHMM.hs is an example of how Hakaru in the future would be used to
perform a combination of MCMC and exact inference on a discrete hidden
Markov model.  It contains four related programs, starting with the model
and ending with inference:

* roadmapProg1 is the *joint* distribution on observations and parameters.
* roadmapProg2 is the distribution on parameters *conditioned* on observations.
* roadmapProg3 is the same distribution as roadmapProg2, but computed exactly
  in polynomial time using *matrix multiplication*.
* roadmapProg4 is a *Metropolis-Hastings* transition kernel that samples
  parameters from the posterior, using the exact computation in roadmapProg3
  to figure the acceptance ratio.

Producing roadmapProg2 from roadmapProg1 requires *disintegration*.
Producing roadmapProg3 from roadmapProg2 requires changing to a
*specialized representation* of measures.  
Producing roadmapProg4 from roadmapProg3 requires *disintegration*
(for probability density) and *simplification*.
