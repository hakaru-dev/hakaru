kernelopts(assertlevel=2): # be strict on all assertions while testing
kernelopts(opaquemodules=false): # allow testing of internal routines
if not (NewSLO :: `module`) then
  WARNING("loading NewSLO failed");
  `quit`(3);
end if;

with(Hakaru):
with(NewSLO):
with(TestWrapper):

#####################################################################
#
# disintegration tests
#
#####################################################################

# this uses a *global* name 't'.
assume(t::real);

TestDisint := MakeTest(
 proc(
  M::{t_Hakaru, list({algebraic, name=list})}, #args to disint, or just 1st arg
  n::set({t_Hakaru, identical(NULL)}), #desired return
  {ctx::list:= []}, #context: assumptions, "knowledge"
  {TLim::{positive, identical(-1)}:= 80} #timelimit
)
  local m;
  m:= `if`(M::list, M, [M, :-t])[], :-ctx= ctx;

  timelimit(
       TLim,
       CodeTools[Test]({disint(m)}, n, set(measure(simplify)), _rest)
  );
end proc
 , testGroup = "Disint" ):

# End of the possibly statistically meaningless tests.

d1 := Bind(Lebesgue(-infinity,infinity), x, Ret(Pair(-5*x,3/x))):
d1r := {Weight(1/5,Ret(-15/t))}:

# should try d2 with 1/c as well
d2 := Bind(Lebesgue(-infinity,infinity), x, Ret(Pair((-1/7)*x-1,3))):
d2r := {Weight(7, Ret(3))}:

#The next two tests are simplified versions of the Borel-Kolmogorov paradox.
#https://en.wikipedia.org/wiki/Borel-Kolmogorov_paradox
d3 := Bind(Uniform(0,1), x, Bind(Uniform(0,1), y, Ret(Pair(x-y,f(x,y))))):
d3r := {
  Bind(Uniform(0, 1), x丅,
    piecewise(And(x丅 < t+1, t < x丅), Ret(f(x丅, x丅-t)), Msum())),
  Bind(Uniform(0, 1), y七,
    piecewise(And(-t < y七, y七 < 1-t), Ret(f(y七+t, y七)), Msum()))
}:

d4 := Bind(Uniform(0,1), x, Bind(Uniform(0,1), y, Ret(Pair(x/y,x)))):
d4r := {
  Weight(1/abs(t)^2,
    Bind(Uniform(0,1),`x丫丵`,
         piecewise(`x丫丵` < t,Weight(`x丫丵`,Ret(`x丫丵`)),Msum()))),
  piecewise(0 < t,
    Bind(Uniform(0,1),`y丩丱`,
         piecewise(t < 1/`y丩丱`,
           Weight(`y丩丱`,Ret(t*`y丩丱`)),
           Msum())),
    Msum())
}:

d5 := Bind(Gaussian(0,1), x, Bind(Gaussian(x,1), y, Ret(Pair(y,x)))):
d5r := {Weight((1/2)*exp(-(1/4)*t^2)/Pi^(1/2), Gaussian((1/2)*t, (1/2)*2^(1/2)))}:

d6 := Bind(Gaussian(0,1), x, Bind(Gaussian(x,1), y, Ret(Pair(x,y)))):
d6r := {Weight(1/2*2^(1/2)/Pi^(1/2)*exp(-1/2*t^2),Gaussian(t,1))}:

# note (y+y), which gives trouble for a syntactic approach
normalFB1 :=
  Bind(Gaussian(0,1), x,
  Bind(Gaussian(x,1), y,
  Ret(Pair((y+y)+x, _Unit)))):

normalFB1r := {Weight(1/26*exp(-1/26*t^2)/Pi^(1/2)*13^(1/2)*2^(1/2),Ret(_Unit))}:

# tests taken from haskell/Tests/Disintegrate.hs
# use same names, to be clearer
norm0a :=
  Bind(Gaussian(0,1), x,
  Bind(Gaussian(x,1), y,
  Ret(Pair(y, x)))):
  # note that the answer below is much nicer than the one expected in Haskell
norm0r := {Weight(1/2/Pi^(1/2)/exp(t^2)^(1/4),Gaussian(t/2,sqrt(2)/2))}:

norm1a :=
  Bind(Gaussian(3,2), x,Ret(piecewise(x<0, Pair(-x, _Unit), Pair(x, _Unit)))):
norm1b :=
  Bind(Gaussian(3,2), x,piecewise(x<0, Ret(Pair(-x, _Unit)), Ret(Pair(x, _Unit)))):

norm1r := {}: #Desired output unknown.

assume(s::real, noiseT >= 3, noiseT <= 8, noiseE >= 1, noiseE <= 8);
easyRoad:= [
  Bind(Uniform(3, 8), noiseT,
  Bind(Uniform(1, 4), noiseE,
  Bind(Gaussian(0, noiseT), x1,
  Bind(Gaussian(x1, noiseE), m1,
  Bind(Gaussian(x1, noiseT), x2,
  Bind(Gaussian(x2, noiseE), m2,
  Ret(Pair(Pair(m1,m2), Pair(noiseT,noiseE)))
  )))))),
  Pair(s,t)
]:
#The first expression below comes from the actual output of disint, hand-
#simplified 1) to bring factors into the innnermost integral, 2) to combine
#products of exps, and 3) to express the polynomial arg of exp in a logical way
#by sub-factoring.
easyRoadr:= {
  Weight(                #Weight 1
    Pi/8,
    Bind(                #Bind 1
      Uniform(3, 8), noiseT,
      Weight(            #Weight 2
        1/noiseT^2,
        Bind(            #Bind 2
          Uniform(1, 4), noiseE,
          Weight(        #Weight 3
            int(         #Int 1
              int(       #Int 2
                exp(
                  -(x2^2/2 - x1*x2 + x1^2)/noiseT^2 -
                  ((t-x2)^2 + (s-x1)^2)/noiseE^2
                )*2/Pi/noiseE,
                x2= -infinity..infinity
              ),         #-Int 2
              x1= -infinity..infinity
            ),           #-Int 1
            Ret(Pair(noiseT, noiseE))
          )              #-Weight 3
        )                #-Bind 2
      )                  #-Weight 2
    )                    #-Bind 1
  ),                     #-Weight 1

  #Hopefully, that's equivalent to...
  Bind(Uniform(3, 8), noiseT,
  Bind(Uniform(1, 4), noiseE,
  Bind(Gaussian(0, noiseT), x1,
  Bind(Weight(density[Gaussian](x1, noiseE)(s), Ret(_Unit)), _,
  Bind(Gaussian(x1, noiseT), x2,
  Weight(density[Gaussian](x2, noiseE)(t), Ret(Pair(noiseT, noiseE)))
  )))))
}:
helloWorld:= [
  Bind(Gaussian(0,1), mu,
  Bind(Plate(n, k, Gaussian(mu, 1)), nu,
  Ret(Pair(nu, mu))
  )),
  :-t,
  ctx= [n::integer, n > 0]
]:
helloWorldr:= {
  Bind(Gaussian(0,1), mu,
  Plate(n, i, Weight(density[Gaussian](mu, 1)(idx(t,i)), Ret(mu)))
  )
}:


#This first block of tests is to test the basic functionality of disint, and,
#to some extent, the system as a whole. These tests may be meaningless to you,
#the statistician and end user of this Hakaru product; they aren't meant to
#have any statistical meaning.--Carl 2016Oct04

TestDisint(
     [Ret(Pair(sqrt(Pi), x)), t &M Ret(7)],
     {Msum()},
     label= "(d0_2) `Dirac` test 1"
);

TestDisint(
     [Ret(Pair(sqrt(Pi), x^2)), t &M Ret(sqrt(Pi))],
     {Ret(x^2)},
     label= "(d0_3) `Dirac` test 2"
);

TestDisint(
     [Bind(Lebesgue((-1,1)*~infinity), x, Ret(Pair(sqrt(Pi), x^2))),
      t &M Ret(sqrt(Pi))
     ],
     {Bind(Lebesgue((-1,1)*~infinity), x1, Ret(x1^2))},
     label= "(d0_4) `Dirac` test with `Bind`"
);

TestDisint(d1, d1r, label = "(d1) Disintegrate linear function");
TestDisint(d2, d2r, label = "(d2) Disintegrate linear function II");
TestDisint(d5, d5r, label = "(d5) Disintegrate N(0,1)*N(x,1), over y");
TestDisint(d6, d6r, label = "(d6) Disintegrate N(0,1)*N(x,1), over x");
TestDisint(norm0a, norm0r,
     label = "(norm0a) U(0,1) >>= \x -> U(x,1) >>= \y -> Ret(y,x)"
);

######################################################################
#
# These tests fail, and are expected to.  Move them up when they
# start passing (and are expected to).
#
# They are, however, roughly in order of what we'd like to have work.
#

# change of variables
TestDisint(d3, d3r, label = "(d3) Disintegrate U(0,1) twice, over x-y");
TestDisint(d4, d4r, label = "(d4) Disintegrate U(0,1) twice, over x/y");

# funky piecewise
TestDisint(norm1a, norm1r,
     label = "(norm1a) U(0,1) into Ret of pw"
);
TestDisint(norm1b, norm1r,
     label = "(norm1b) U(0,1) into pw of Ret"
);
# This one is kind of cosmetic; it would be 'fixed' properly if the
# disintegration process did not use 'improve' to do "domain information
# discovery", but rather had a specific function (and then improve could
# indeed do this integral).
TestDisint( normalFB1, normalFB1r,
     label = "(d7_normalFB1) Disintegrate N(0,1)*N(x,1), over (y+y)+x"
);
#In this one the function in the inequality, x+x^3, is injective but nonlinear.
TestDisint(
     Bind(Gaussian(0,1), x, Ret(Pair(x+x^3, f(x)))),
     {}, #I don't know what to expect.
     label= "(d0_5) Injective nonlinear inequality"
);
# takes too long.
TestDisint(
     easyRoad, easyRoadr,
     label= "(easyRoad) Combo of Normals with distinct Uniform noises",
     TLim= 5 #takes 6 - 8 minutes to `improve` on an Intel i7
);

#This one is a basic test of the Counting wrt-var type.
#This one gives the Weight(-1, ...) error
assume(n_, integer);
TestDisint(
     [Bind(PoissonD(2), n, Ret(Pair(3,n))), n_ &M Counting((-1,1)*~infinity)],
     {},  #I don't know what to expect.
     ctx= [n::integer, n >= 0],
     label= "(d0_1) `Counting` test; `Weight` bug (currently failing)"
);

TestDisint(
     helloWorld, helloWorldr,
     label= "(helloWorld) Plate of Normals",
     ctx= [n::integer, n > 0]
);
