kernelopts(assertlevel=2): # be strict on all assertions while testing
kernelopts(opaquemodules=false): # allow testing of internal routines
read "NewSLO.mpl":
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
  Bind(Uniform(0,1),`x丕丟`,
       piecewise(And(t < `x丕丟`,`x丕丟`-1 < t),Ret(f(`x丕丟`,`x丕丟`-t)),Msum())), 
  Bind(Uniform(0,1),`y专丛`,
       piecewise(And(t < 1-`y专丛`,-`y专丛` < t),Ret(f(`y专丛`+t,`y专丛`)),Msum()))
}:

d4 := Bind(Uniform(0,1), x, Bind(Uniform(0,1), y, Ret(Pair(x/y,x)))):
d4r := {
  Weight(1/abs(t)^2, 
  Bind(Uniform(0, 1), x丅丏, 
       Weight(Indicator({x丅丏 < t})*x丅丏, Ret(x丅丏)))), 
  Weight(Indicator({0 < t}), 
  Bind(Uniform(0, 1), y七下, 
       Weight(Indicator({t < 1/y七下})*y七下, Ret(t*y七下))))
}:

d5 := Bind(Gaussian(0,1), x, Bind(Gaussian(x,1), y, Ret(Pair(y,x)))):
d5r := {}:  # soon!
d6 := Bind(Gaussian(0,1), x, Bind(Gaussian(x,1), y, Ret(Pair(x,y)))):
d6r := {Weight(1/2*2^(1/2)/Pi^(1/2)*exp(-1/2*t^2),Gaussian(t,1))}:

TestDisint(d1, d1r, label = "Disintegrate linear function");
TestDisint(d2, d2r, label = "Disintegrate linear function II");
TestDisint(d3, d3r, label = "Disintegrate U(0,1) twice, over x-y");
TestDisint(d4, d4r, label = "Disintegrate U(0,1) twice, over x/y");
TestDisint(d5, d5r, label = "Disintegrate N(0,1)*N(x,1), over y");
TestDisint(d6, d6r, label = "Disintegrate N(0,1)*N(x,1), over x");
