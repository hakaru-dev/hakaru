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
  CodeTools[Test](map(fromLO,disint(toLO(m),t)), n, set(measure(simplify)), _rest)
end proc:

d1 := Bind(Lebesgue(), x, Ret(Pair(-5*x,3/x))):
d1r := {Weight(1/5,Ret(-15/t))}:

# should try d2 with 1/c as well
d2 := Bind(Lebesgue(), x, Ret(Pair((-1/7)*x-1,3))):
d2r := {Weight(7, Ret(3))}:

d3 := Bind(Uniform(0,1), x, Bind(Uniform(0,1), y, Ret(Pair(x-y,f(x,y))))):
d3r := {
 Bind(Uniform(0, 1), x丅丏, 
      piecewise(And(x丅丏-1 < t, t < x丅丏), Ret(f(x丅丏, x丅丏-t)), Msum())), 
 Bind(Uniform(0, 1), y七下, 
     piecewise(And(-y七下 < t, t < 1-y七下), Ret(f(y七下+t, y七下)), Msum()))
}:

d4 := Bind(Uniform(0,1), x, Bind(Uniform(0,1), y, Ret(Pair(x/y,x)))):
d4r := {
  Bind(Uniform(0, 1), x丕丟, 
    piecewise(And(x丕丟 < t, t < signum(x丕丟)*infinity), Weight(abs(x丕丟/t^2), Ret(x丕丟)), Msum())), 
  Bind(Uniform(0, 1), y专丛, 
    piecewise(And(0 < t, t < 1/y专丛), Weight(abs(y专丛), Ret(t*y专丛)), Msum()))
}:

d5 := Bind(Gaussian(0,1), x, Bind(Gaussian(x,1), y, Ret(Pair(y,x)))):
d5r := {}:  # soon!

TestDisint(d1, d1r, label = "Disintegrate linear function");
TestDisint(d2, d2r, label = "Disintegrate linear function II");
TestDisint(d3, d3r, label = "Disintegrate U(0,1) twice, over x-y");
TestDisint(d4, d4r, label = "Disintegrate U(0,1) twice, over x/y");
TestDisint(d5, d5r, label = "Disintegrate N(0,1)*N(x,1), over y");
