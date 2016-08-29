kernelopts(assertlevel=2): # be strict on all assertions while testing
kernelopts(opaquemodules=false): # allow testing of internal routines
if not (NewSLO :: `module`) then
  WARNING("loading NewSLO failed");
  `quit`(3);
end if;

with(Hakaru):
with(NewSLO):

#####################################################################
#
# disintegration tests
#
#####################################################################

# this uses a *global* name 't'.
assume(t::real);
TestDisint := proc(m, n, {ctx::list:= []}, {TLim::{positve, identical(-1)}:= 80})
  #global t;
  timelimit(
       TLim,
       CodeTools[Test]({disint(m, :-t, :-ctx= ctx)}, n, set(measure(simplify)), _rest)
  )
end proc:

d1 := Bind(Lebesgue(-infinity,infinity), x, Ret(Pair(-5*x,3/x))):
d1r := {Weight(1/5,Ret(-15/t))}:

# should try d2 with 1/c as well
d2 := Bind(Lebesgue(-infinity,infinity), x, Ret(Pair((-1/7)*x-1,3))):
d2r := {Weight(7, Ret(3))}:

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

norm1r := {}:

easyRoad:=
  Bind(Uniform(3, 8), noiseT,
  Bind(Uniform(1, 4), noiseE,
  Bind(Gaussian(0, noiseT), x1,
  Bind(Gaussian(x1, noiseE), m1,
  Bind(Gaussian(x1, noiseT), x2,
  Bind(Gaussian(x2, noiseE), m2,
  Ret(Pair(Pair(m1,m2), Pair(noiseT,noiseE)))
  ))))))
:
easyRoadr:=  
  Bind(Uniform(3, 8), noiseT,
  Bind(Uniform(1, 4), noiseE,
  Bind(Gaussian(0, noiseT), x1,
  Bind(Weight(density[Gaussian](x1, noiseE)(t1), Ret(_Unit)), _,
  Bind(Gaussian(x1, noiseT), x2,
  Weight(density[Gaussian](x2, noiseE)(t2), Ret(Pair(noiseT, noiseE)))
  )))))
: 
helloWorld:=
  Bind(Gaussian(0,1), mu,
  Bind(Plate(n, _, Gaussian(mu, 1)), nu,
  Ret(Pair(nu, mu))
  ))
:
helloWorldr:= 
  Bind(Gaussian(0,1), mu,
  Plate(n, i, Weight(density[Gaussian](mu, 1)(idx(t,i)), Ret(mu)))
  )
:  

TestDisint(d1, d1r, label = "(d1) Disintegrate linear function");
TestDisint(d2, d2r, label = "(d2) Disintegrate linear function II");
TestDisint(d3, d3r, label = "(d3) Disintegrate U(0,1) twice, over x-y");
TestDisint(d4, d4r, label = "(d4) Disintegrate U(0,1) twice, over x/y");
TestDisint(d5, d5r, label = "(d5) Disintegrate N(0,1)*N(x,1), over y");
TestDisint(d6, d6r, label = "(d6) Disintegrate N(0,1)*N(x,1), over x");
TestDisint( normalFB1, normalFB1r,
     label = "(d7_normalFB1) Disintegrate N(0,1)*N(x,1), over (y+y)+x"
);
TestDisint(norm0a, norm0r,
     label = "(norm0a) U(0,1) >>= \x -> U(x,1) >>= \y -> Ret(y,x)"
);
TestDisint(norm1a, norm1r,
     label = "(norm1a) U(0,1) into Ret of pw"
);
TestDisint(norm1b, norm1r,
     label = "(norm1b) U(0,1) into pw of Ret"
);
TestDisint(
     easyRoad, easyRoadr,
     label= "(easyRoad) Combo of Normals with distinct Uniform noises"
);
TestDisint(
     helloWorld, helloWorldr, ctx= [n::integer, n > 0],
     label= "(helloWorld) Plate of Normals"
);
