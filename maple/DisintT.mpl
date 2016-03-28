kernelopts(assertlevel=2): # be strict on all assertions while testing
kernelopts(opaquemodules=false): # allow testing of internal routines
if not (NewSLO :: `module`) then
  WARNING("loading NewSLO failed");
  `quit`(3);
end if;

with(NewSLO):

#####################################################################
#
# disintegration tests
#
#####################################################################

# this uses a *global* variable 't'.
TestDisint := proc(m,n)
  global t;
  CodeTools[Test](map(fromLO@improve,disint(toLO(m),t)), n, 
                  set(measure(simplify)), _rest)
end proc:

d1 := Bind(Lebesgue(), x, Ret(Pair(-5*x,3/x))):
d1r := {Weight(1/5,Ret(-15/t))}:

# should try d2 with 1/c as well
d2 := Bind(Lebesgue(), x, Ret(Pair((-1/7)*x-1,3))):
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
d5r := {Weight((1/2)*exp(-(1/4)*t^2)/Pi^(1/2), 
        Gaussian((1/2)*t, (1/2)*2^(1/2)))}:
d6 := Bind(Gaussian(0,1), x, Bind(Gaussian(x,1), y, Ret(Pair(x,y)))):
d6r := {Weight(1/2*2^(1/2)/Pi^(1/2)*exp(-1/2*t^2),Gaussian(t,1))}:

# great test: scope extrusion!
normalFB1 := 
  Bind(Gaussian(0,1), x, 
  Bind(Gaussian(x,1), y, 
  Ret(Pair((y+y)+x, Unit)))):

normalFB1r := {Weight(1/26*exp(-1/26*t^2)/Pi^(1/2)*13^(1/2)*2^(1/2),Ret(Unit))}:

###########
#
#  Convenient short-hands.  These come in this way from Hakaru too.
#
###########

bern := proc(p) Msum(Weight(p, Ret(true)), Weight(1-p, Ret(false))) end proc:

###########

burgalarm := 
  Bind(bern(10^(-4)), burglary,
  Bind(bern(piecewise(burglary = true, 95/100, 1/100)), alarm,
  Ret(Pair(alarm, burglary)))):
burgalarmr := {}:

TestDisint(d1, d1r, label = "Disintegrate linear function");
TestDisint(d2, d2r, label = "Disintegrate linear function II");
TestDisint(d3, d3r, label = "Disintegrate U(0,1) twice, over x-y");
TestDisint(d4, d4r, label = "Disintegrate U(0,1) twice, over x/y");
TestDisint(d5, d5r, label = "Disintegrate N(0,1)*N(x,1), over y");
TestDisint(d6, d6r, label = "Disintegrate N(0,1)*N(x,1), over x");
TestDisint(normalFB1, normalFB1r, label = "Disintegrate N(0,1)*N(x,1), over (y+y)+x");

TestDisint(burgalarm, burgalarmr, label = "D Burgler Alarm example");
