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

For example, suppose we would like to make a Markov Chain for the
normal distribution, where the proposal distribution is a random walk.

### Target
````nohighlight
# target.hk
normal(0,1)
````

### Proposal
````nohighlight
# proposal.hk
fn x real: normal(x, 0.04)
````

We can use `mh` to create a transition kernel.

````bash
mh target.hk proposal.hk

x5 = x2 = fn x0 real: 
           (exp((negate(((x0 - nat2real(0)) ^ 2))
                  / 
                 prob2real((2 * (nat2prob(1) ^ 2)))))
             / 
            nat2prob(1)
             / 
            sqrt((2 * pi))
             / 
            1)
     fn x1 real: 
      x0 <~ normal(x1, (1/25))
      return (x0, (x2(x0) / x2(x1)))
fn x4 real: 
 x3 <~ x5(x4)
 (match x3: 
   (x1, x2): 
    x0 <~ weight(min(1, x2), return true) <|> 
          weight(real2prob((prob2real(1) - prob2real(min(1, x2)))),
                 return false)
    return (match x0: 
             true: x1
             false: x4))

````

This can then be simplified.

````bash
mh target.hk proposal.hk | simplify -

fn x4 real: 
 x03 <~ normal(x4, (1/25))
 weight(min(1, (exp(((x03 ^ 2) * -1/2)) * exp(((x4 ^ 2) / 2)))),
        return x03) <|> 
 weight(real2prob((1
                    + 
                   (prob2real(min(1, (exp(((x03 ^ 2) * -1/2)) * exp(((x4 ^ 2) / 2)))))
                     * 
                    (-1)))),
        return x4)
````
		
This can then be run using `hakaru`. Hakaru when run with two
arguments will assume that the first file is a transition kernel,
and the second file represents a measure to initialize from.
		

````bash
mh target.hk proposal.hk | simplify - | hakaru - target.hk | head

-0.6133542972818671
-0.6111567543723275
-0.5963756142974966
-0.5661156231637984
-0.6280335079595971
-0.616432866701967
-0.6053631512209712
-0.5964839795872353
-0.6020821843203473
-0.6535246137595148
````
