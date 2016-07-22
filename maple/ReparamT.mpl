#
#     Test Suite for Reparam---integration and summation changes of variables
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
     #`&under` is defined below.
     #Type `verification` is slightly modified (below) from its standard definition.
     ver::verification,
     #First infolevel is for initial test; second is for retest after failure.
     {infolevels::[nonnegative, nonnegative]:= [0, Float(infinity)]},
     {ctx::list:= []}   #Assumptions (not necessarily to be passed to `assuming`)
)
# For 'production' runs, we want things to be as quiet
# as possible.  We would like to do
# maple -q < ReparamT.mpl | grep -v "passed"
# and get 0 lines of output. If global `pretty`	is true, some extra lines are
# printed for readability. You may want to set this in a worksheet session.
local
     LOform:= toLO(e_in),  #preprocess input
     r
;
     if :-pretty then printf("\n") end if;
     :-infolevel[reparam]:= infolevels[1];
     if not CodeTools:-Test(reparam(LOform, :-ctx= ctx), e_out, ver, boolout, _rest) then
          #If test fails, do same test with diagnostic infolevel setting.
          if infolevels[2] > infolevels[1] then
               printf("\n@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@"  );
               printf("\n*** Rerun at higher infolevel: ***\n"); 
               :-infolevel[reparam]:= infolevels[2];
               r:= CodeTools:-Test(reparam(LOform, :-ctx= ctx), e_out, ver, boolout, _rest);
               printf(  "@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@\n");
               return r
          else
               return false
          end if
     else
          return
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

#Automatic simplifications: When an easy transformation can be used to
#transform a distribution that we don't support to one that we do, then a
#procedure in this section does it. These may be moved to NewSLO.

#Bernoulli
Bern:= proc(p)
     local i;
     Bind(Counting(0,1), i, Weight(idx([p,1-p],i) * Ret(i)))
end proc:

#Exponential
Exponential:= mu-> GammaD(1,mu):

#Control printing of extra lines for readability.
if not assigned(pretty) then pretty:= false end if: 

#
#   The tests
#

#Constant multiple in integral
TestReparam(
     Bind(Lebesgue(-infinity,infinity), x, Weight(2, Ret(2*x))),
     Lebesgue(-infinity,infinity),
     equal &under fromLO,
     label= "(t0a) Constant multiple with Lebesgue" #passing
):

#Logarithm with Uniform
TestReparam(
     Bind(Uniform(0,1), x, Ret(-log(x))),
     GammaD(1,1),
     equal &under fromLO,
     label= "(t0b) Logarithm with Uniform" #passing
):

#(t1) Symbolic affine transformation with Gaussian
TestReparam(
     Bind(Gaussian(mu,sigma), x, Ret((x-mu)/sigma)),
     Gaussian(0,1),
     equal &under fromLO,
     ctx= [sigma > 0],
     label= "(t1) Symbolic affine transformation with Gaussian" #passing
):

#(t2) ChiSquared to Gamma
#(inverse of relationship given in Relationships.hs)
# Special case of Gamma now recognized as being ChiSquared
TestReparam(
     ChiSquared(2*b),
     GammaD(b,2),
     equal &under (fromLO, _ctx= foldr(assert, empty, b > 0)),
     ctx= [b > 0],
     label= "(t2) ChiSquared to Gamma" #passing
):

#(t3) Symbolic constant multiple with Gamma
TestReparam(
     Bind(GammaD(alpha,beta), x, Ret(2*x/beta)),
     GammaD(alpha, 2),
     equal &under (fromLO, _ctx= foldr(assert, empty, alpha > 0, beta > 0)),
     ctx= [alpha > 0, beta > 0],
     label= "(t3) Symbolic constant multiple with Gamma" #passing
):

#(t4) Two-variable LFT with Gamma
#This fails due to multivariate changes of variable not being implemented yet.
TestReparam(
     Bind(GammaD(a,t), x1, Bind(GammaD(b,t), x2, Ret(x1/(x1+x2)))),
     BetaD(a,b),
     equal &under fromLO,
     infolevels= [2,2],
     label= "(t4) Two-variable LFT with Gamma (currently failing)"
):

#(t5) Logarithm with symbolic constant multiplier and Uniform
TestReparam(
     Bind(Uniform(0,1), x, Ret(-alpha*log(x))),
     GammaD(1,alpha),
     equal &under fromLO,
     ctx= [alpha >= 0],
     label= "(t5) Logarithm with symbolic constant multiplier and Uniform"
     #passing
):

#(t6) Poisson(mu) -> ? as mu -> infinity
#The concept of taking the limit at infinity of a distribution parameter isn't
#implemented yet.

#(t7) Quotient of standard normals to standard Cauchy
#Fails because it's multivariate.
#This should be the first multivariate integration to implement, due to
#simplicity; it might work as a simple multivariate substitution.
TestReparam(
     Bind(Gaussian(0,1), x1, Bind(Gaussian(0,1), x2, Ret(x1/x2))),
     Cauchy(0,1),
     equal &under fromLO,
     infolevels= [2,2],
     label=
          "(t7) Quotient of standard normals to standard Cauchy "
          "(currently failing)"
):

#(t8) Affine translation of quotient of standard normals to Cauchy
#This is a trivial variation of t7.
#Fails because it's multivariate.
TestReparam(
     Bind(Gaussian(0,1), x1, Bind(Gaussian(0,1), x2, Ret(a+alpha*x1/x2))),
     Cauchy(a,alpha),
     equal &under (fromLO, _ctx= foldr(assert, empty, alpha > 0)),
     ctx= [alpha > 0],
     infolevels= [2,2],
     label=
          "(t8) Affine translation of quotient of standard normals to Cauchy "
          "(currently failing)"
):

#(t9) Bernoulli to Binomial with n=1
#Fails because Binomial isn't implemented.
#Doesn't use reparam in a meaningful way.
TestReparam(
     Bern(p),
     Binomial(1,p),
     equal &under (fromLO, _ctx= foldr(assert, empty, 0 <= p, p <= 1)),
     ctx= [0 <= p, p <= 1],
     infolevels= [2,2],
     label= "(t9) Bernoulli to Binomial with n=1 (currently failing)"
):

#(t10) Beta(1,1) to Uniform(0,1)
#This one doesn't require reparam, but it passes using reparam.
TestReparam(
     #Note: No use of `Bind`. This passes by direct recognition by fromLO
     #without any meaningful use of reparam, although reparam is called.
     BetaD(1,1),
     Uniform(0,1),
     equal &under fromLO,
     label= "(t10) Beta(1,1) to Uniform(0,1)" #passing
):

#(t11) Laplace to difference of Gammas
#This one fails because Laplace isn't implemented. Also, there's nothing that
#reparam can do with this. It's up to fromLO to recognize the compound
#expression.
#Perhaps this should be an automatic simplification.
TestReparam(
     Laplace(a1,a2),
     Bind(GammaD(1,a1), x1, Bind(GammaD(1,a2), x2, Ret(x1-x2))),
     equal &under (fromLO, _ctx= foldr(assert, empty, a1 > 0, a2 > 0)),
     ctx= [a1 > 0, a2 > 0],
     infolevels= [2,2],
     label= "(t11) Laplace to difference of Gammas (currently failing)"
):

#(t12) Sum of iid Exponentials to Gamma
#This currently fails because it's multivariate.
TestReparam(
     Bind(Exponential(b), x1, Bind(Exponential(b), x2, Ret(x1+x2))),
     GammaD(2,b),
     equal &under (fromLO, _ctx= foldr(assert, empty, b > 0)),
     ctx= [b > 0],
     infolevels= [2,2],
     label= "(t12) Sum of iid Exponentials to Gamma (currently failing)"
):

#(t13) Weibull(1,b) to Exponential(1/b)
#This test is wrong in Relationships.hs!
#It should be Weibull(a,1) to Exponential(1/a).
#Fails because Weibull isn't implemented.
TestReparam(
     #Straightforward recognition; doesn't use reparam in a meaningful way.
     Weibull(a,1),
     Exponential(1/a),
     equal &under (fromLO, _ctx= foldr(assert, empty, a > 0)),
     ctx= [a > 0],
     infolevels= [2,2],
     label= "(t13) Weibull(a,1) to Exponential(1/a) (currently failing)"
):

#(t14) Standard normal over sqrt(ChiSquared) to StudentT
#Fails because it's multivariate.
TestReparam(
     Bind(Gaussian(0,1), x, Bind(ChiSquared(nu), y, Ret(x/sqrt(y/nu)))),
     StudentT(nu, 0, 1),
     equal &under (fromLO, _ctx= foldr(assert, empty, nu > 0)),
     ctx= [nu > 0],
     infolevels= [2,2],
     label= "(t14) Std normal over sqrt(Chi2) to StudentT (currently failing)"
):

#(t15) 1/InverseGamma(k,1/t) to GammaD(k,t)
TestReparam(
     Bind(InverseGammaD(k, 1/t), x, Ret(1/x)),
     GammaD(k,t),
     equal &under (fromLO, _ctx= foldr(assert, empty, k > 0, t > 0)),
     ctx= [k > 0, t > 0],
     label= "(t15) 1/InverseGammaD(k,1/t) to GammaD(k,t)" #passing
):

#(t16) Sum of std normals to normal(0,sqrt(2))
#Fails because it requires a multivariate change of vars.
TestReparam(
     Bind(Gaussian(0,1), x1, Bind(Gaussian(0,1), x2, Ret(x1+x2))),
     Gaussian(0,sqrt(2)),
     equal &under fromLO,
     infolevels= [2,2],
     label= "(t16) Sum of std normals to normal(0,sqrt(2)) (currently failing)"
):

#(t17) Sum of std normal and normal to normal
#Fails because it requires a multivariate change of vars.
TestReparam(
     Bind(Gaussian(0,1), x1, Bind(Gaussian(mu,sigma), x2, Ret(x1+x2))),
     Gaussian(mu, sqrt(1+sigma^2)),
     equal &under (fromLO, _ctx= foldr(assert, empty, sigma > 0)),
     ctx= [sigma > 0],
     infolevels= [2,2],
     label= "(t17) Sum of std normal and normal to normal (currently failing)"
):

#(t18) Sum of symbolic multiples of std normals to normal
#Fails because it requires a multivariate change of vars.
TestReparam(
     Bind(Gaussian(0,1), x1, Bind(Gaussian(0,1), x2, Ret(a1*x1 + a2*x2))),
     Gaussian(0, sqrt(a1^2 + a2^2)),
     equal &under fromLO,
     infolevels= [2,2],
     label=
          "(t18) Sum of symbolic multiples of std normals to normal "
          "(currently failing)"
):

#(t19) Sum of equiprobable binomials to binomial
#Fails for three reasons: it's multivariate, it's discrete, and Binomial isn't
#implemented.
TestReparam(
     Bind(Binomial(n1,p), x1, Bind(Binomial(n2,p), x2, Ret(x1+x2))),
     Binomial(n1+n2, p),
     equal &under (fromLO,
          _ctx= foldr(
               assert, empty,
               n1::integer, n1 > 0, n2::integer, n2 > 0, 0 <= p, p <= 1
          )
     ),
     ctx= [n1::integer, n1 > 0, n2::integer, n2 > 0, 0 <= p, p <= 1],
     infolevels= [2,2],
     label=
          "(t19) Sum of equiprobable binomials to binomial "
          "(currently failing)"
):

#(t20) Sum of n Bernoullis to Binomial
#Fails because Binomial isn't implemented.
TestReparam(
     Bind(Plate(n, i, Bern(p)), xs, Ret(sum(idx(xs,i),i=0..n-1))),
     Binomial(n,p),
     equal &under (fromLO,
          _ctx= foldr(assert, empty, n::integer, n > 0, 0 <= p, p <= 1)
     ),
     ctx= [n::integer, n > 0, 0 <= p, p <= 1],
     infolevels= [2,2],
     label= "(t20) Sum of n Bernoullis to Binomial (currently failing)"
):

#(t21) Sum of Poissons to Poisson
#Fails because reparam doesn't yet handle summations.
TestReparam(
     Bind(PoissonD(lambda1), x1, Bind(PoissonD(lambda2), x2, Ret(x1+x2))),
     PoissonD(lambda1 + lambda2),
     equal &under (fromLO,
          _ctx= foldr(assert, empty, lambda1 > 0, lambda2 > 0)
     ),
     ctx= [lambda1 > 0, lambda2 > 0],
     infolevels= [2,2],
     label= "(t21) Sum of Poissons to Poisson (currently failing)"
):

#(t22) Sum of Gammas to Gamma
#Fails because it's multivariate.
TestReparam(
     Bind(GammaD(a1,b), x1, Bind(GammaD(a2,b), x2, Ret(x1+x2))),
     GammaD(a1+a2, b),
     equal &under (fromLO, _ctx= foldr(assert, empty, a1 > 0, a2 > 0, b > 0)),
     ctx= [a1 > 0, a2 > 0, a3 > 0],
     infolevels= [2,2],
     label= "(t22) Sum of Gammas to Gamma (currently failing)"
):

#(t23) Sum of n Exponentials to Gamma
#Fails because it involves a Plate.
TestReparam(
     Bind(Plate(n, i, Exponential(b)), xs, Ret(sum(idx(xs,i), i= 0..n-1))),
     GammaD(n,b),
     equal &under (fromLO, _ctx= foldr(assert, empty, n::integer, n > 0, b > 0)),
     ctx= [n::integer, n > 0, b > 0],
     infolevels= [2,2],
     label= "(t23) Sum of n Exponentials to Gamma (currently failing)"
):

#(t24) Weibull "scaling" property.
#I can find no evidence that this is true; indeed, it seems trivial to disprove
#it.

#(t25) Product of lognormals is lognormal
#Fails because it's multivariate.
TestReparam(
     Bind(
          Gaussian(mu1,sigma1), x1,
          Bind(Gaussian(mu2,sigma2), x2, Ret(exp(x1)*exp(x2)))
     ),
     Bind(Gaussian(mu1+mu2, sqrt(sigma1^2 + sigma2^2)), x3, Ret(exp(x3))),
     equal &under (fromLO, _ctx= foldr(assert, empty, sigma1 > 0, sigma2 > 0)),
     ctx= [sigma1 > 0, sigma2 > 0],
     infolevels= [2,2],
     label= "(t25) Product of lognormals is lognormal (currently failing)"
):

#(t26) Cauchy of reciprocal to Cauchy
#Fails due to improper handling of the discontinuity in the substitution.
TestReparam(
     Bind(Cauchy(0, sigma), x, Ret(1/x)),
     Cauchy(0, 1/sigma),
     equal &under (fromLO, _ctx= foldr(assert, empty, sigma > 0)),
     ctx= [sigma > 0],
     infolevels= [2,2],
     label= "(t26) Cauchy of reciprocal to Cauchy (currently failing)"
):

#(t27) Symbolic constant multiple of Gamma to Gamma
TestReparam(
     Bind(GammaD(r,lambda), x, Ret(a*x)),
     GammaD(r, a*lambda),
     equal &under (fromLO,
          _ctx= foldr(assert, empty, r > 0, lambda > 0, a > 0)
     ),
     ctx= [r > 0, lambda > 0, a > 0],
     label= "(t27) Symbolic constant multiple of Gamma to Gamma" #passing
):

#(t28) Beta of 1-x to Beta
TestReparam(
     Bind(BetaD(a,b), x, Ret(1-x)),
     BetaD(b,a),
     equal &under (fromLO, _ctx= foldr(assert, empty, a > 0, b > 0)),
     ctx= [a > 0, b > 0],
     label= "(t28) Beta with 1-x to Beta" #passing
):

#(t29) Binomial of n-x to Binomial
#Fails because Binomial isn't implemented.
TestReparam(
     Bind(Binomial(n,p), x, Ret(n-x)),
     Binomial(n, 1-p),
     equal &under (fromLO,
          _ctx= foldr(assert, empty, n::integer, n > 0, 0 <= p, p <= 1)
     ),
     ctx= [n::integer, n > 0, 0 <= p, p <= 1],
     infolevels= [2,2],
     label= "(t29) Binomial of n-x to Binomial (currently failing)"
):

#(t30) Square of std normal to ChiSquared(1)
#Fails due to non-invertibility of substitution u= x^2.
TestReparam(
     Bind(Gaussian(0,1), x, Ret(x^2)),
     ChiSquared(1),
     equal &under fromLO,
     infolevels= [2,2],
     label= "(t30) Square of std normal to ChiSquared(1) (currently failing)"
):

#(t31) Sum of squares of n iid std normals to ChiSquared(n)
#Fails because it involves a Plate.
TestReparam(
     Bind(Plate(n, i, Gaussian(0,1)), xs, Ret(sum(idx(xs,i)^2, i= 0..n-1))),
     ChiSquared(n),
     equal &under (fromLO, _ctx= foldr(assert, empty, n::integer, n > 0)),
     ctx= [n::integer, n > 0],
     infolevels= [2,2],
     label= 
          "(t31) Sum of squares of n iid std normals to ChiSquared(n) "
          "(currently failing)"
):

#(t32) Sum of ChiSquareds is ChiSquared
#Fails because it's multivariate.
TestReparam(
     Bind(ChiSquared(k1), x1, Bind(ChiSquared(k2), x2, Ret(x1+x2))),
     ChiSquared(k1+k2),
     equal &under (fromLO, _ctx= foldr(assert, empty, k1 > 0, k2 > 0)),
     ctx= [k1 > 0, k2 > 0],
     infolevels= [2,2],
     label= "(t32) Sum of ChiSquareds is ChiSquared (currently failing)"
):
