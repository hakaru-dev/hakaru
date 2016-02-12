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
 LO(h, Int(Indicator({t < x, x-1 < t})*applyintegrand(h, f(x, x-t)), x = 0 .. 1)),
 LO(h, Int(Indicator({t < 1-y, -y < t})*applyintegrand(h, f(y+t, y)), y = 0 .. 1))
 }:

d4 := Bind(Uniform(0,1), x, Bind(Uniform(0,1), y, Ret(Pair(x/y,x)))):
d4r := {
  LO(h, Int(piecewise(And(0 < t, t < 1/y), abs(y)*applyintegrand(h, t*y), 0), y = 0 .. 1)), 
  LO(h, Int(piecewise(And(x < t, t < signum(x)*infinity), abs(x/t^2)*applyintegrand(h, x), 0), x = 0 .. 1))
}:

d5 := Bind(NormalD(0,1), x, Bind(NormalD(x,1), y, Ret(Pair(y,x)))):
d5r := {}:  # soon!

TestDisint(d1, d1r, label = "Disintegrate linear function");
TestDisint(d2, d2r, label = "Disintegrate linear function II");
TestDisint(d3, d3r, label = "Disintegrate U(0,1) twice, over x-y");
TestDisint(d4, d4r, label = "Disintegrate U(0,1) twice, over x/y");
TestDisint(d5, d5r, label = "Disintegrate N(0,1)*N(x,1), over y");
