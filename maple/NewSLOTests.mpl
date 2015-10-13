kernelopts(assertlevel=2): # be strict on all assertions while testing
kernelopts(opaquemodules=false): # allow testing of internal routines
read "NewSLO.mpl":
if not (NewSLO :: `module`) then
  WARNING("loading NewSLO failed");
  `quit`(3);
end if;

with(NewSLO):

# covers primitive constructs
model1 := 
  Bind(Gaussian(0,1), x,
  Bind(Msum(Ret(0),Weight(1,Lebesgue())), y,
  Ret(1/exp(x^2+y^2)))):

# simplifies to
model1s :=
  Bind(Gaussian(0,1), x, 
  Msum(Ret(exp(-x^2)), 
       Bind(Lebesgue(), y, 
       Ret(exp(-(x^2+y^2)))))):

CodeTools[Test](value(integrate(model1,z->z)), (sqrt(Pi)+1)/sqrt(3), equal,
  label="primitive constructs + integrate + value");

TestHakaru(model1, model1s, label = "primitive constructs simplification");

# Unknown measures -- no changes
u1 := Bind(m, x, Ret(x^2)):
u2 := Bind(Gaussian(0,1), x, m(x)):

TestHakaru(u1, label = "binding unknown m");
TestHakaru(u2, u2, label = "sending to unknown m");

# example with an elaborate simplifier to do reordering of
# integration, which in turn integrates out a variable
model3 := Bind(Gaussian(0,1),x,Gaussian(x,1)):

TestHakaru(model3, Gaussian(0,sqrt(2)),
 simp = (lo -> evalindets(lo, 'specfunc(Int)',
  i -> evalindets(IntegrationTools[CollapseNested](
                  IntegrationTools[Combine](i)), 'Int(anything,list)',
  i -> subsop(0=int, applyop(ListTools[Reverse], 2, i))))),
  label = "use simplifier to integrate out variable");

# Kalman filter; note the parameter + assumption
kalman := 
  Bind(Gaussian(0,1),x,Weight(NewSLO:-density[Gaussian](x,1)(y),Ret(x))):

TestHakaru( kalman, 
  Weight(exp(-y^2/4)/2/sqrt(Pi),Gaussian(y/2,1/sqrt(2))),
  label = "Kalman filter") assuming y::real;

# piecewise
model4 := 
  Bind(Gaussian(0,1),x,
  Bind(piecewise(x<0,Ret(0),x>4,Ret(4),Ret(x)),y,
  Ret(y^2))):
model4s := Bind(Gaussian(0,1),x,piecewise(x<0,Ret(0),4<x,Ret(16),Ret(x^2))):

TestHakaru(model4, model4s, label = "piecewise test");

# test with uniform.  No change without simplifier, eliminates it with
# call to value.
introLO := 
  Bind(Uniform(0,1),x,
  Bind(Uniform(0,1),y,
  piecewise(x<y,Ret(true),x>=y,Ret(false)))):
introLOs := Msum(Weight(1/2, Ret(false)), Weight(1/2, Ret(true))):

TestHakaru(introLO, introLO, simp = (x -> x), label = "2 uniform - no change");
TestHakaru(introLO, introLOs, simp = value, label = "2 uniform + value = elimination");
TestHakaru(introLO, introLOs, label = "2 uniform + simplifier  elimination");

# a variety of other tests
TestHakaru(LO(h,(x*applyintegrand(h,5)+applyintegrand(h,3))/x), Weight(1/x, Msum(Weight(x, Ret(5)), Ret(3))));
TestHakaru(Bind(Gaussian(0,1),x,Weight(x,Msum())), Msum());
TestHakaru(Bind(Uniform(0,1),x,Weight(x^alpha,Ret(x))), Weight(1/(1+alpha),BetaD(1+alpha,1)));
TestHakaru(Bind(Uniform(0,1),x,Weight(x^alpha*(1-x)^beta,Ret(x))), Weight(Beta(1+alpha,1+beta),BetaD(1+alpha,1+beta)));
TestHakaru(Bind(Uniform(0,1),x,Weight((1-x)^beta,Ret(x))), Weight(1/(1+beta),BetaD(1,1+beta)));

# tests that basic densities are properly recognized
TestHakaru(Bind(Uniform(0,1),x,Weight(x*2,Ret(x))), BetaD(2,1));
TestHakaru(BetaD(alpha,beta));
TestHakaru(GammaD(a,b));
TestHakaru(LO(h, int(exp(-x/2)*applyintegrand(h,x),x=0..infinity)), Weight(2,GammaD(1,2)));
TestHakaru(LO(h, int(x*exp(-x/2)*applyintegrand(h,x),x=0..infinity)), Weight(4,GammaD(2,2)));
TestHakaru(Bind(Lebesgue(), x, Weight(1/x^2, Ret(x))));
TestHakaru(Cauchy(loc,scale)) assuming scale>0;
TestHakaru(StudentT(nu,loc,scale)) assuming scale>0;
TestHakaru(StudentT(1,loc,scale),Cauchy(loc,scale)) assuming scale>0;

# how far does myint get us?
TestHakaru(
  Bind(Uniform(0,1),x,Weight(x,Ret(Unit))), 
  Weight(1/2,Ret(Unit)),
  label = "eliminate Uniform");

# just the front-end is already enough to get this
TestHakaru(
  Bind(Weight(1/2,Ret(Unit)),x,Ret(Unit)), 
  Weight(1/2, Ret(Unit)),
  label = "integrate at work");

# and more various
model_exp := Bind(Uniform(-1,1),x,Ret(exp(x))):
TestHakaru(model_exp, model_exp, label = "uniform -1..1 into exp");
TestHakaru(IntegrationTools[Expand](LO(h, Int((1+y)*applyintegrand(h,y),y=0..1))), Msum(Uniform(0,1), Weight(1/2,BetaD(2,1))));
TestHakaru(Bind(Uniform(0,1),x,Bind(IntegrationTools[Expand](LO(h, Int((1+y)*applyintegrand(h,y),y=0..1))),y,Ret([x,y]))), Weight(3/2,Bind(Uniform(0,1),x,Msum(Weight(2/3,Bind(Uniform(0,1),y,Ret([x,y]))),Weight(1/3,Bind(BetaD(2,1),y,Ret([x,y])))))));

# easy-easy-HMM
eeHMM := Bind(GammaD(1,1),t,
                 Weight(NewSLO:-density[Gaussian](0,1/sqrt(t))(a),
                 Ret(t))):
ees := Weight(1/(a^2+2)^(3/2), GammaD(3/2, 1/((1/2)*a^2+1))):


TestHakaru(eeHMM, ees, label = "easy-easy-HMM") assuming a :: real;

# from an email conversation on Sept. 11
model6 := Bind(Gaussian(0,1),x, piecewise(x>4,Ret(4),Ret(x))):
TestHakaru(model6, model6, label = "clamped Gaussian");

# and now models (then tests) taken from Tests.RoundTrip
t1 := Bind(Uniform(0, 1), a0, Msum(Weight(a0, Ret(Unit)))):
t2 := BetaD(1,1):
t2s := Bind(Uniform(0, 1), a0, Ret(a0)):
t3 := Gaussian(0,10):
t4 := Bind(BetaD(1, 1), a0, 
      Bind(Msum(Weight(a0, Ret(true)), 
                Weight((1-a0), Ret(false))), a1, 
      Ret(Pair(a0, a1)))):
t4s := Bind(Uniform(0, 1), a0, 
       Msum(Weight(a0, Ret(Pair(a0, true))), 
            Weight((1+(a0*(-1))), Ret(Pair(a0, false))))):
t5 := Bind(Msum(Weight((1/2), Ret(Unit))), a0, Ret(Unit)):
t5s := Weight((1/2), Ret(Unit)):
t6 := Ret(5):
t7 := Bind(Uniform(0, 1), a0, 
  Bind(Msum(Weight((a0+1), Ret(Unit))), a1, Ret((a0*a0)))):
t7s := Bind(Uniform(0,1),a3,Weight(a3+1,Ret(a3^2))):
t7n := Bind(Uniform((-1), 0), a0, 
  Bind(Msum(Weight((a0+1), Ret(Unit))), a1, Ret((a0*a0)))):
t7ns := Bind(Uniform(-1,0),a3,Weight(a3+1,Ret(a3^2))):
t8 := Bind(Gaussian(0, 10), a0, Bind(Gaussian(a0, 20), a1, Ret(Pair(a0, a1)))):
t9 := Bind(Lebesgue(), a0, 
  Bind(Msum(Weight(piecewise(And((3<a0), (a0<7)), (1/2), 0), Ret(Unit))), a1, Ret(a0))):
t9a := Bind(Lebesgue(), a0,
  piecewise(3>=a0, Msum(), a0>=7, Msum(), Weight(1/2, Ret(a0)))):
t9s := Weight(2, Uniform(3,7)):

#t23, "bayesNet", to show exact inference.  Original used bern, which
# is here expanded.
t23 := 
  Bind(Msum(Weight((1/2), Ret(true)), Weight((1-(1/2)), Ret(false))), a0, 
  Bind(Msum(Weight(piecewise(a0 = true, (9/10), (1/10)), Ret(true)), 
            Weight((1-piecewise(a0 = true, (9/10), (1/10))), Ret(false))), a1, 
  Bind(Msum(Weight(piecewise(a0 = true, (9/10), (1/10)), Ret(true)), 
            Weight((1-piecewise(a0 = true, (9/10), (1/10))), Ret(false))), a2, 
  Ret(Pair(a1, a2))))):
t23s := Msum(Weight(41/100,Ret(Pair(true,true))),
             Weight(9/100,Ret(Pair(true,false))),
             Weight(9/100,Ret(Pair(false,true))),
             Weight(41/100,Ret(Pair(false,false)))):

# to exercise myint_pw
model_pw := Bind(Uniform(0,4), x,
  piecewise(x<1, Ret(x), x<2, Ret(2*x), x<3, Ret(3*x), Ret(5*x))):
model_pw2 := Bind(Uniform(0,4), x, Weight(piecewise(x<1, 1, x<2, 2, x<3, 3, 5),Ret(x))):
model_pw3 := Bind(Uniform(0,4), x,
  piecewise(x<1, Ret(x), x<2, Weight(2,Ret(x)), x<3, Weight(3,Ret(x)), x>=3, Weight(5,Ret(x)))):
model_pw5 := Bind(Uniform(0,4), x, Weight(piecewise(x<1, 1, x<2, 2, x<3, 3, x>=3, 5),Ret(x))):
TestHakaru(model_pw, model_pw, label = "multi-branch choice");
TestHakaru(model_pw3, model_pw3, label = "fake multi-branch weight");
TestHakaru(model_pw2, model_pw5, label = "proper multi-branch weight");

# t43 without the explicit lam
t43 := piecewise(x0=true, Uniform(0, 1), Bind(BetaD(1, 1), a1, Ret(a1))):
t43s := Uniform(0, 1):

t80 := Bind(GammaD(1, 1), a0, Gaussian(0, a0)):

TestHakaru(t1, t5s, label = "t1");
TestHakaru(t2, t2s, label = "t2");
TestHakaru(t3, t3, label = "t3");
TestHakaru(t4, t4s, label = "t4");
TestHakaru(t5, t5s, label = "t5");
TestHakaru(t6, t6, label = "t6");
TestHakaru(t7, t7s, label = "t7");
TestHakaru(t7n, t7ns, label = "t7n");
TestHakaru(t8, t8, label = "t8");
TestHakaru(t9, t9s, label = "t9");
TestHakaru(t9a, t9s, label = "t9a");
TestHakaru(t23, t23s, label = "t23");
TestHakaru(t43, t43s, label = "t43"):

TestHakaru(t80, t80, label = "t80");

###
# From disintegration paper
disint1 := 
Bind(Lebesgue(),y, Weight(piecewise(0<y and y<1, 1, 0), Weight(y/2, Ret(y)))):

TestHakaru(disint1, Weight(1/4,BetaD(2,1)), label="minor miracle");

ind1  := Bind(Uniform(0,1),x, Weight(piecewise(x>0,1,0), Weight(piecewise(x>1/2,0,1), Weight(piecewise(0<x,1,0), Ret(x))))):
ind1s := Weight(1/2, Uniform(0,1/2)):
ind2  := Bind(Lebesgue(),x, Weight(piecewise(x<0,0,x<1,x,0), Ret(x))):
ind2s := Weight(1/2, BetaD(2,1)):
ind3  := Bind(Uniform(0,1),x, Weight(piecewise(1<x and x<0,1,0), Ret(x))):
ind3s := Msum():
TestHakaru(ind1, ind1s, label="exponentiated indicator");
TestHakaru(ind2, ind2s, label="negated and conjoined indicator");
TestHakaru(ind3, ind3s, label="bounds ordering");
TestHakaru(Msum(ind1,ind2), Msum(ind1s,ind2s), label="simplify under sum");
TestHakaru(piecewise(c>0,ind1,ind2), piecewise(c>0,ind1s,ind2s), label="simplify under piecewise");

# test how banish handles piecewise
m1 := Uniform(0,1):
m2 := BetaD(2,1):
m3 := BetaD(1,2):
bp := proc() Bind(Gaussian(0,1), x,
             Bind(Gaussian(0,1), y,
             piecewise(_passed))) end proc:
TestHakaru(bp(x>y, m1, m2         ), Msum(Weight(1/2, m1), Weight(1/2, m2)                 ), label="banish piecewise 1");
TestHakaru(bp(x>0, m1, m2         ), Msum(Weight(1/2, m1), Weight(1/2, m2)                 ), label="banish piecewise 2");
TestHakaru(bp(y>0, m1, m2         ), Msum(Weight(1/2, m1), Weight(1/2, m2)                 ), label="banish piecewise 3");
TestHakaru(bp(x>y, m1, x>0, m2, m3), Msum(Weight(1/2, m1), Weight(1/8, m2), Weight(3/8, m3)), label="banish piecewise 4");
TestHakaru(bp(x>0, m1, x>y, m2, m3), Msum(Weight(1/2, m1), Weight(1/8, m2), Weight(3/8, m3)), label="banish piecewise 5");
TestHakaru(bp(y>x, m1, y>0, m2, m3), Msum(Weight(1/2, m1), Weight(1/8, m2), Weight(3/8, m3)), label="banish piecewise 6");
TestHakaru(bp(y>0, m1, y>x, m2, m3), Msum(Weight(1/2, m1), Weight(1/8, m2), Weight(3/8, m3)), label="banish piecewise 7");

# Simplify is not yet idempotent
TestHakaru(Bind(Uniform(0,1), x, Weight(x, Uniform(0,x))), Weight(1/2, BetaD(1, 2)));

# Test for change of variables; see Tests/Relationships.hs
# t1
# cv1 := Bind(Gaussian(mu, sigma), x, Ret((x-mu)/sigma)):
# cv1s := Gaussian(0,1):
# TestHakaru(cv1, cv1s, label = "renormalize Gaussian") assuming sigma>0;

# t28
# cv2 := Bind(BetaD(a,b), x, Ret(1-x)):
# cv2s := BetaD(b,a):
# TestHakaru(cv2, cv2s, label = "swap BetaD") assuming a>0,b>0;

unk_pw := Bind(m, y, Bind(Gaussian(0,1), x, piecewise(x<0, Ret(-x), Ret(x)))):
unk1   := Bind(Gaussian(0,1), x, Bind(m, y, Bind(Gaussian(x,1), z, Ret([y,z])))):
unk1s  := Bind(m, y, Bind(Gaussian(0,sqrt(2)), z, Ret([y,z]))):
unk2   := Bind(Gaussian(0,1), x, Bind(Gaussian(x,1), z, Bind(m, y, Ret([y,z])))):
unk2s  := Bind(Gaussian(0,sqrt(2)), z, Bind(m, y, Ret([y,z]))):
unk3   := Bind(Gaussian(0,1), x, Bind(m(x), y, Bind(Gaussian(x,1), z, Ret([y,z])))):
unk4   := Bind(Gaussian(0,1), x, Bind(Gaussian(x,1), z, Bind(m(x), y, Ret([y,z])))):
TestHakaru(unk_pw, unk_pw, label="Don't simplify Integrand willy-nilly");
TestHakaru(unk1, unk1s, label="Banish into Integrand 1");
TestHakaru(unk2, unk2s, label="Banish into Integrand 2");
TestHakaru(unk3, unk3, label="Banish into Integrand 3");
TestHakaru(unk4, unk4, label="Banish into Integrand 4");

# Disintegration of easierRoadmapProg1 -- variables to be integrated out
rmProg1 := Msum(Weight(1, Msum(Weight(1, Msum(Weight(1, Msum(Weight(1, Bind(Lebesgue(), a4, Msum(Weight(1, Msum(Weight(1, Bind(Lebesgue(), a5, Msum(Weight(1, Bind(Lebesgue(), a6, Msum(Weight(((exp((-(((p3-a6)*(p3-a6))*(1/(2*exp((ln(a5)*2)))))))*(1/a5))*(1/exp((ln((2*Pi))*(1/2))))), Msum(Weight(1, Bind(Lebesgue(), a7, Msum(Weight(((exp((-(((a6-a7)*(a6-a7))*(1/(2*exp((ln(a4)*2)))))))*(1/a4))*(1/exp((ln((2*Pi))*(1/2))))), Msum(Weight(((exp((-(((p2-a7)*(p2-a7))*(1/(2*exp((ln(a5)*2)))))))*(1/a5))*(1/exp((ln((2*Pi))*(1/2))))), Msum(Weight(((exp((-((a7*a7)*(1/(2*exp((ln(a4)*2)))))))*(1/a4))*(1/exp((ln((2*Pi))*(1/2))))), Msum(Weight((1/3), Msum(Weight(1, piecewise((a5<4), piecewise((1<a5), Msum(Weight((1/5), Msum(Weight(1, piecewise((a4<8), piecewise((3<a4), Ret(Pair(a4, a5)), Msum()), Msum())), Weight(1, Msum())))), Msum()), Msum())), Weight(1, Msum())))))))))))))))))))))), Weight(1, Msum())))))), Weight(1, Msum())))))):
TestHakaru(rmProg1, Weight(1/(2*Pi), Bind(Uniform(3, 8), a4, Bind(Uniform(1, 4), a5, Weight(exp(-(1/2)*(2*p2^2*a4^2+p2^2*a5^2-2*p2*p3*a4^2+p3^2*a4^2+p3^2*a5^2)/(a4^4+3*a4^2*a5^2+a5^4))/sqrt(a4^4+3*a4^2*a5^2+a5^4), Ret(Pair(a4, a5)))))), label="Tests.RoundTrip.rmProg1");
# easierRoadmapProg4 -- MH transition kernel with unclamped acceptance ratio
module()
  local unpair, fst, snd, rmProg4;
  unpair := proc(f,p)
    f(fst(p),snd(p))
  end proc;
  fst := proc(p)
    if p :: Pair(anything,anything) then op(1,p)
    elif p :: specfunc(piecewise) then map_piecewise(fst,p)
    else 'procname(_passed)' end if
  end proc:
  snd := proc(p)
    if p :: Pair(anything,anything) then op(2,p)
    elif p :: specfunc(piecewise) then map_piecewise(snd,p)
    else 'procname(_passed)' end if
  end proc:
  rmProg4 := lam(x0, app(lam(x1, lam(x2, Bind(unpair(( (p3 , p4) -> Msum(Weight((1/2), Bind(Uniform(3, 8), a5, Ret(Pair(a5, p4)))), Weight((1/2), Bind(Uniform(1, 4), a6, Ret(Pair(p3, a6)))))), x2), a7, Ret(Pair(a7, (app(x1,a7)/app(x1,x2))))))),lam(x8, unpair(( (p151 , p152) -> app(p152,lam(x153, 1))), app(app(lam(x9, lam(x10, unpair(( (p11 , p12) -> app(lam(x13, app(lam(x14, Pair(Msum(Weight(x13, unpair(( (p15 , p16) -> p15), x14))), lam(x17, (0+(x13*app(unpair(( (p18 , p19) -> p19), x14),x17)))))),app(lam(x20, app(lam(x21, Pair(Msum(Weight(x20, unpair(( (p22 , p23) -> p22), x21))), lam(x24, (0+(x20*app(unpair(( (p25 , p26) -> p26), x21),x24)))))),app(lam(x27, app(lam(x28, app(lam(x29, app(lam(x30, Pair(Msum(Weight(x27, unpair(( (p31 , p32) -> p31), x28)), Weight(x29, unpair(( (p33 , p34) -> p33), x30))), lam(x35, ((0+(x27*app(unpair(( (p36 , p37) -> p37), x28),x35)))+(x29*app(unpair(( (p38 , p39) -> p39), x30),x35)))))),Pair(Msum(), lam(x40, 0)))),1)),app(lam(x41, app(lam(x42, Pair(Msum(Weight(x41, unpair(( (p43 , p44) -> p43), x42))), lam(x45, (0+(x41*app(unpair(( (p46 , p47) -> p47), x42),x45)))))),app(lam(x48, app(lam(x49, app(lam(x50, app(lam(x51, Pair(Msum(Weight(x48, unpair(( (p52 , p53) -> p52), x49)), Weight(x50, unpair(( (p54 , p55) -> p54), x51))), lam(x56, ((0+(x48*app(unpair(( (p57 , p58) -> p58), x49),x56)))+(x50*app(unpair(( (p59 , p60) -> p60), x51),x56)))))),Pair(Msum(), lam(x61, 0)))),1)),app(lam(x62, app(lam(x63, Pair(Msum(Weight(x62, unpair(( (p64 , p65) -> p64), x63))), lam(x66, (0+(x62*app(unpair(( (p67 , p68) -> p68), x63),x66)))))),unpair(( (p69 , p70) -> unpair(( (p71 , p72) -> unpair(( (p73 , p74) -> unpair(( (p75 , p76) -> unpair(( (p77 , p78) -> unpair(( (p79 , p80) -> unpair(( (p81 , p82) -> unpair(( (p83 , p84) -> unpair(( (p85 , p86) -> unpair(( (p87 , p88) -> app(lam(x89, app(lam(x90, Pair(Msum(Weight(x89, unpair(( (p91 , p92) -> p91), x90))), lam(x93, (0+(x89*app(unpair(( (p94 , p95) -> p95), x90),x93)))))),app(lam(x96, app(lam(x97, Pair(Msum(Weight(x96, unpair(( (p98 , p99) -> p98), x97))), lam(x100, (0+(x96*app(unpair(( (p101 , p102) -> p102), x97),x100)))))),app(lam(x103, app(lam(x104, app(lam(x105, app(lam(x106, Pair(Msum(Weight(x103, unpair(( (p107 , p108) -> p107), x104)), Weight(x105, unpair(( (p109 , p110) -> p109), x106))), lam(x111, ((0+(x103*app(unpair(( (p112 , p113) -> p113), x104),x111)))+(x105*app(unpair(( (p114 , p115) -> p115), x106),x111)))))),Pair(Msum(), lam(x116, 0)))),1)),piecewise((p12<4), piecewise((1<p12), app(lam(x117, app(lam(x118, Pair(Msum(Weight(x117, unpair(( (p119 , p120) -> p119), x118))), lam(x121, (0+(x117*app(unpair(( (p122 , p123) -> p123), x118),x121)))))),app(lam(x124, app(lam(x125, app(lam(x126, app(lam(x127, Pair(Msum(Weight(x124, unpair(( (p128 , p129) -> p128), x125)), Weight(x126, unpair(( (p130 , p131) -> p130), x127))), lam(x132, ((0+(x124*app(unpair(( (p133 , p134) -> p134), x125),x132)))+(x126*app(unpair(( (p135 , p136) -> p136), x127),x132)))))),Pair(Msum(), lam(x137, 0)))),1)),piecewise((p11<8), piecewise((3<p11), app(lam(x138, app(lam(x139, Pair(Msum(Weight(x138, unpair(( (p140 , p141) -> p140), x139))), lam(x142, (0+(x138*app(unpair(( (p143 , p144) -> p144), x139),x142)))))),app(lam(x145, Pair(Ret(x145), lam(x146, app(x146,x145)))),Pair(p11, p12)))),5), Pair(Msum(), lam(x147, 0))), Pair(Msum(), lam(x148, 0))))),1))),(1/5)), Pair(Msum(), lam(x149, 0))), Pair(Msum(), lam(x150, 0))))),1))),(1/3)))),((((1/Pi)*exp((((((((((p69*p71)*(p11*p11))*2)+((((p11*p11)*p73)*p76)*(-2)))+((p78*p80)*(p11*p11)))+((p12*p12)*(p81*p83)))+((p12*p12)*(p86*p88)))*(1/((((p11*p11)*(p11*p11))+(((p12*p12)*(p11*p11))*3))+((p12*p12)*(p12*p12)))))*(-(1/2)))))*exp((ln(((exp(((x -> piecewise(x<0, -337, ln(x)))(p11)*4))+((exp(((x -> piecewise(x<0, -337, ln(x)))(p12)*2))*exp(((x -> piecewise(x<0, -337, ln(x)))(p11)*2)))*3))+exp(((x -> piecewise(x<0, -337, ln(x)))(p12)*4))))*(-(1/2)))))*(1/10)))), x9)), x9)), x9)), x9)), x9)), x9)), x9)), x9)), x9)), x9))),1))),1))),1))),1))),1))),1)), x10))),x0),x8))))):
  TestHakaru(app(app(rmProg4,Pair(r1,r2)),Pair(p1,p2)), Msum(Weight(1/2, Bind(Uniform(3, 8), a5, Ret(Pair(Pair(a5, p2), exp((1/2)*(-p1+a5)*(a5+p1)*(p1^2*p2^2*r1^2+p1^2*p2^2*r2^2+2*p1^2*r1^2*a5^2-2*p1^2*r1*r2*a5^2+p1^2*r2^2*a5^2+p2^4*r1^2+2*p2^4*r1*r2+2*p2^4*r2^2+p2^2*r1^2*a5^2+p2^2*r2^2*a5^2)/((p2^4+3*p2^2*a5^2+a5^4)*(p1^4+3*p1^2*p2^2+p2^4)))*sqrt(p1^4+3*p1^2*p2^2+p2^4)/sqrt(p2^4+3*p2^2*a5^2+a5^4))))), Weight(1/2, Bind(Uniform(1, 4), a6, Ret(Pair(Pair(p1, a6), exp((1/2)*(-p2+a6)*(a6+p2)*(5*p1^4*r1^2-6*p1^4*r1*r2+2*p1^4*r2^2+2*p1^2*p2^2*r1^2-2*p1^2*p2^2*r1*r2+p1^2*p2^2*r2^2+2*p1^2*r1^2*a6^2-2*p1^2*r1*r2*a6^2+p1^2*r2^2*a6^2+p2^2*r1^2*a6^2+p2^2*r2^2*a6^2)/((p1^4+3*p1^2*a6^2+a6^4)*(p1^4+3*p1^2*p2^2+p2^4)))*sqrt(p1^4+3*p1^2*p2^2+p2^4)/sqrt(p1^4+3*p1^2*a6^2+a6^4)))))), label="rmProg4") assuming 3<p1, p1<8, 1<p2, p2<4;
end module:

TestHakaru(Bind(Ret(ary(n,i,i*2)), v, Ret(idx(v,42))), Ret(84), label="basic array indexing");

ary0 := Bind(Plate(ary(k, i, Gaussian(0,1))), xs, Ret([xs])):
TestHakaru(ary0, ary0, label="plate roundtripping");

ary1  := Bind(Gaussian(0,1), x,
         Bind(Plate(ary(n, i, Weight(density[Gaussian](x,1)(idx(t,i)), Ret(Unit)))), ys,
         Ret(x))):
ary1w := 2^(-(1/2)*n+1/2)*exp((1/2)*((sum(idx(t,i),i=1..n))^2-(sum(idx(t,i)^2,i=1..n))*n-(sum(idx(t,i)^2,i=1..n)))/(n+1))*Pi^(-(1/2)*n)/sqrt(2+2*n):
TestHakaru(ary1, Weight(ary1w, Gaussian((sum(idx(t, i), i = 1 .. n))/(n+1), 1/sqrt(n+1))), label="Wednesday goal") assuming n::nonnegint;
TestHakaru(Bind(ary1, x, Ret(Unit)), Weight(ary1w, Ret(Unit)), label="Wednesday goal total") assuming n::nonnegint;
ary2  := Bind(Gaussian(0,1), x,
         Bind(Plate(ary(n, i, Bind(Gaussian(idx(t,i),1),z, Weight(density[Gaussian](x,1)(idx(t,i)), Ret(z+1))))), ys,
         Ret(ys))):
TestHakaru(ary2, Weight(ary1w, Bind(Plate(ary(n, i, Gaussian(idx(t,i),1))), zs, Ret(ary(n, i, idx(zs,i)+1)))), label="Reason for fission") assuming n::nonnegint;
ary3  := Bind(Gaussian(0,1), x,
         Bind(Plate(ary(n, i, Bind(Gaussian(idx(t,i),1),z, Weight(density[Gaussian](x,1)(idx(t,i)), Ret(z))))), zs,
         Ret(zs))):
TestHakaru(ary3, Weight(ary1w, Plate(ary(n, i, Gaussian(idx(t,i),1)))), label="Array eta") assuming n::nonnegint;

bry1  := Bind(BetaD(alpha,beta), x,
         Bind(Plate(ary(n, i, Weight(x    ^piecewise(idx(y,i)=true ,1) *
                                     (1-x)^piecewise(idx(y,i)=false,1),
                              Ret(Unit)))), ys,
         Ret(x))):
bry1s := Weight(Beta(alpha+sum(piecewise(idx(y,i)=true ,1), i=1..n),
                     beta +sum(piecewise(idx(y,i)=false,1), i=1..n))/Beta(alpha,beta),
         BetaD(alpha+sum(piecewise(idx(y,i)=true ,1), i=1..n),
               beta +sum(piecewise(idx(y,i)=false,1), i=1..n))):
TestHakaru(bry1, bry1s, label="first way to express flipping a biased coin many times") assuming n::nonnegint;

bry2  := Bind(BetaD(alpha,beta), x,
         Bind(Plate(ary(n, i, Weight(x    ^(  idx(y,i)) *
                                     (1-x)^(1-idx(y,i)),
                              Ret(Unit)))), ys,
         Ret(x))):
bry2s := Weight(Beta(alpha+  sum(idx(y,i),i=1..n),
                     beta +n-sum(idx(y,i),i=1..n))/Beta(alpha,beta),
         BetaD(alpha+  sum(idx(y,i),i=1..n),
               beta +n-sum(idx(y,i),i=1..n))):
TestHakaru(bry2, bry2s, label="second way to express flipping a biased coin many times") assuming n::nonnegint;

fission     := Bind(Plate(ary(k, i, Gaussian(0,1))), xs, Plate(ary(k, i, Gaussian(idx(xs,i),1)))):
fusion      := Plate(ary(k, i, Bind(Gaussian(0,1), x, Gaussian(x,1)))):
conjugacies := Plate(ary(k, i, Gaussian(0, sqrt(2)))):
TestHakaru(fission, conjugacies, label="Reason for fusion");
TestHakaru(fusion,  conjugacies, label="Conjugacy in plate");

# Simplifying gmm below is a baby step towards index manipulations we need
gmm := Bind(Plate(ary(k, c, Gaussian(0,1))), xs,
       Bind(Plate(ary(n, i, Weight(density[Gaussian](idx(xs,idx(cs,i)),1)(idx(t,i)), Ret(Unit)))), ys,
       Ret(xs))):
