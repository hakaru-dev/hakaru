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
with(KB):
with(NewSLO):
########################

#common procedures for these tests.
TestReparam:= proc(
     e_in,
     e_out,   #Expected output, after postprocessing by `verify` and `&under`
     #`verification` is slightly modified (below) from its standard definition.
     # &under is defined below.
     ver::verification, 
     #First infolevel is for initial test; second is for retest after failure.
     {infolevels::[{nonnegint,identical(infinity)},{nonnegint, identical(infinity)}]:= [0,infinity]},
     {ctx::list:= []} #Assumptions (not necessarily to be passed to `assuming`)
          
)
local 
     LOform:= toLO(e_in)  #preprocessed input
;
     :-infolevel[Reparam]:= infolevels[1];               
     if not CodeTools:-Test(reparam(LOform, :-ctx= ctx), e_out, ver, boolout, _rest) then
          #If test fails, do same test with diagnostic infolevel setting.
          if infolevels[2] > infolevels[1] then
               :-infolevel[Reparam]:= infolevels[2];
               return CodeTools:-Test(reparam(LOform, :-ctx= ctx), e_out, ver, boolout, _rest)
          else
               return false
          end if
     else
          return #If passed, quiet return. 
     end if            
end proc:

#VerifyTools is an undocumented Maple library package similiar to TypeTools.
#Add a verification &under analogous to type &under.
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

#Constant multiple in integral
TestReparam(
     Bind(Lebesgue(-infinity,infinity), x, Weight(2, Ret(2*x))),
     Lebesgue(-infinity,infinity),
     equal &under fromLO,
     infolevels= [infinity$2],
     label= "Constant multiple with Lebesgue" #passing
);

#Logarithm with Uniform
TestReparam(
     Bind(Uniform(0,1), x, Ret(-log(x))),
     GammaD(1,1),
     equal &under fromLO,
     infolevels= [infinity$2],
     label= "Logarithm with Uniform" #passing
);

#(t1) Symbolic affine transformation with Gaussian
TestReparam(
     Bind(Gaussian(mu,sigma), x, Ret((x-mu)/sigma)),
     Gaussian(0,1),
     equal &under fromLO,
     ctx= [sigma > 0],
     infolevels= [infinity$2],
     label= "(t1) Symbolic affine transformation with Gaussian" #passing
);

#(t2) ChiSquare with constant multiplier to Gamma
#This fails due to ChiSquare not being implemented yet.
TestReparam(
     ChiSquare(2*b),
     GammaD(b,2),
     equal &under fromLO,
     infolevels= [0,2],
     label= 
          "(t2) ChiSquare with constant multiplier to Gamma "
          "(currently failing)"
);

#(t3) Symbolic constant multiple with Gamma
TestReparam(
     Bind(GammaD(alpha,beta), x, Ret(2*x/beta)),
     GammaD(alpha, 2),
     equal &under (fromLO, _ctx= foldr(assert, empty, alpha > 0, beta > 0)),
     ctx= [alpha > 0, beta > 0],
     infolevels= [infinity$2],
     label= "(t3) Symbolic constant multiple with Gamma" #passing
);

#(t4) Two-variable LFT with Gamma
#This fails due to multivariate changes of variable not being implemented yet.
TestReparam(
     Bind(GammaD(a,t), x1, Bind(GammaD(b,t), x2, Ret(x1/(x1+x2)))),
     BetaD(a,b), 
     equal &under fromLO,
     infolevels= [infinity$2],
     label= "(t4) Two-variable LFT with Gamma (currently failing)"
);

#(t5) Logarithm with symbolic constant multiplier and Uniform
TestReparam(
     Bind(Uniform(0,1), x, Ret(-alpha*log(x))),
     GammaD(1,alpha),
     equal &under fromLO,
     ctx= [alpha >= 0],
     infolevels= [infinity$2],
     label= "(t5) Logarithm with symbolic constant multiplier and Uniform"
     #passing
);

#(t6) Poisson(mu) -> ? as mu -> infinity
#The concept of taking the limit at infinity of a distribution parameter isn't
#implemented yet.

#(t7) Quotient of standard normals to standard Cauchy
#This should be the first multivariate integration to implement, due to 
#simplicity; it might work as a simple multivariate substitution.
TestReparam(
     Bind(Gaussian(0,1), x1, Bind(Gaussian(0,1), x2, Ret(x1/x2))),
     Cauchy(0,1),
     equal &under fromLO,
     infolevels= [0,2],
     label= 
          "(t7) Quotient of standard normals to standard Cauchy "
          "(currently failing)"
);

#(t8) Affine translation of quotient of standard normals to Cauchy
#This is a trivial variation of t7.
TestReparam(
     Bind(Gaussian(0,1), x1, Bind(Gaussian(0,1), x2, Ret(a+alpha*x1/x2))),
     Cauchy(a,alpha),
     equal &under (fromLO, _ctx= foldr(assert, empty, alpha > 0)),
     ctx= [alpha > 0],
     infolevels= [0,2],
     label= 
          "(t8) Affine translation of quotient of standard normals to Cauchy "
          "(currently failing)"
);

#(t9) Bernoulli to Binomial with n=1
#Since neither Bernoulli or Binomial are implemented, this is difficult to test.
#A Bernoulli is a Categorical with two categories. Categorical is implemented.

#(t10) Beta(1,1) to Uniform(0,1)
#This one doesn't require `reparam`, but it passes using `reparam`. 
TestReparam(
     #Note: No use of `Bind`. This passes by direct recognition by fromLO
     #without any meaningful use of reparam, although reparam is called. 
     BetaD(1,1),
     Uniform(0,1),
     equal &under fromLO,
     infolevels= [0,2],
     label= "(t10) Beta(1,1) to Uniform(0,1)" #passing
);

#(t11) Laplace to difference of Gammas
#This one fails because Laplace isn't implemented. Also, there's nothing that
#reparam can do with this.
(*********** #Test commented out. 
TestReparam(
     Laplace(a1,a2),
     Bind(GammaD(1,a1), x1, Bind(GammaD(1,a2), x2, Ret(x1-x2))),
     equal &under (fromLO, _ctx= foldr(assert, empty, a1 > 0, a2 > 0)),
     ctx= [a1 > 0, a2 > 0],
     infolevels= [0,2],
     label= "(t11) Laplace to difference of Gammas (currently failing)"
);
***********)

#(t12) Sum of iid Exponentials to Gamma
#We have no Exponential. I can represent it as Gamma.
#This currently fails because it's two variable.
TestReparam(
     Bind(GammaD(1,b), x1, Bind(GammaD(1,b), x2, Ret(x1+x2))),
     GammaD(2,b),
     equal &under (fromLO, _ctx= foldr(assert, empty, b > 0)),
     ctx= [b > 0],
     infolevel= [0,2],
     label= "(t12) Sum of iid Exponentials to Gamma (currently failing)"
);
