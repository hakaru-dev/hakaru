#
#     Test Suite for Reparam---integral and sum changes of variables
#
#Created by Carl 17Jun2016.

#common header for Hakaru-Maple test suites
kernelopts(assertlevel= 2): # be strict on all assertions while testing
kernelopts(opaquemodules= false): # allow testing of internal routines
if not NewSLO :: `module` then
  WARNING("loading NewSLO failed");
  `quit`(3)
end if:

with(Hakaru):
with(NewSLO):
########################

#common procedures for tests.
TestReparam:= proc(
     e_in::specfunc(Bind),
     e_out,   #Expected output, after postprocessing by `verify` and `&under`
     ver,   #::verification,
     {infolevels::list(nonnegint):= [0,infinity]}
)
global infolevel;
local 
     LOform:= toLO(e_in)  #preprocessed input
;
     infolevel[Reparam]:= infolevels[1];              
     if not CodeTools:-Test(Reparam(LOform), e_out, ver, boolout, quiet, _rest) then
          infolevel[Reparam]:= infolevels[2];
          CodeTools:-Test(Reparam(LOform), e_out, ver, boolout, quiet, _rest)
     end if            
end proc:

#VerifyTools is a undocumented Maple library package similiar to TypeTools.
VerifyTools:-AddVerification(`&under`= ((e1,e2,Ver,f)-> verify(f(e1,_rest), e2, Ver))):

#Need to overload Maple library `type/verification` so that expressions of the form 'v &under f'
#are considered verifications.
`type/verification/MapleLibrary`:= eval(`type/verification`):
`type/verification`:= overload([
     proc(Under::specfunc(`&under`))
     option overload;
          type(op(1,Under), `verification/MapleLibrary`)
     end proc,

     `type/verification/MapleLibrary`
]):

#
#   The tests 
#

# Constant multiple in integral
TestReparam(
     Bind(Lebesgue(), x, Weight(2, Ret(2*x))),
     Lebesgue(),
     equal &under fromLO,
     infolevels= [0,2],
     label= "Constant multiple in integral"
);
