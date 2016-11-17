The example Hakaru programs in this directory include the case studies
that Section 6 of our POPL 2017 paper "Exact Bayesian Inference by
Symbolic Disintegration" refers to:

* Uniform distributions over polytopes, such as the unit square, subject
  to the observations in Section 2 and the observation max(x,y) used by
  Chang and Pollard (1997) to motivate disintegration
    * borel-sub.hk
    * borel-div.hk
    * triangle.hk
    * max.hk
* Normal distributions over correlated real variables, such as Bayesian
  linear regression
    * hello1.hk
    * hello3.hk
    * blr.hk
* Discrete mixtures of continuous distributions, such as Gaussian
  mixture models for clustering
    * msum.hk
    * rj.hk
    * gaussian_mixture.hk
* Continuous mixtures of discrete distributions, such as Naive Bayes
  models for document classification
    * dice_index_joint.hk
    * lda.hk
* A simplified model of seismic event detection, involving spherical
  geometry (Arora, Russell, and Sudderth 2013)
    * seismic.hk
* The collision model used by Afshar, Sanner, and Webers (2016) to motivate
  observing combinations (such as sums) of random variables
    * momentum.hk
* A linear dynamic model in one dimension, with noisy observations of
  two time steps
    * easyroad.hk

