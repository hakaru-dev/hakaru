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

TestDisint(d1, d1r, label = "Disintegrate linear function");
