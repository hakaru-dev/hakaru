This directory contains Hakaru programs that illustrate our symbolic
array disintegrator. The following programs have been described in our
ICFP 2017 submission "Symbolic conditioning of arrays in probabilistic
programs":

* The `pendulum` example developed throughout the paper, as it appears
  in its final version in Section 4

    pendulum.hk
    
* R2 benchmarks that use arrays, as described in Section 6

    * clinicalTrial.hk
      Observe a pair of arrays of boolean values
    
    * coinBias.hk
      Estimate the bias of a coin by observing repeated tosses
      
    * digitRecognition.hk 
      Infer the digit by observing an array of booleans generated
      from handwriting data
      
    * hiv.hk
      A linear dynamical model; observe an array of reals drawn 
      independently from unidentical normal distributions; infer
      the parameters of the model
      
    * linearRegression.hk
      Observe an array of real numbers and fit a line through
      them, i.e., infer the slope, y-intercept, and noise
      
    * surveyUnbias.hk
      Observe an array of booleans representing a survey answer
      to infer the gender bias of a population modeled using a
      normal distribution
      
* Microbenchmarks to test array manipulation (inside the `micro/`
  directory)
    
    * Probabilistic hello world, where we infer the mean of a Gaussian
      that is observed several times
        
        helloWorld.hk

    * Different ways of copying and indexing into arrays
        
        * copy1.hk
        * copy2.hk
        * copy3.hk
        * copy4.hk

    * Mapping simple numeric functions across arrays
       
        * mapIncr.hk
        * mapDouble.hk
        
               
      
