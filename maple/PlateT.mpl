kernelopts(assertlevel=2): # be strict on all assertions while testing
kernelopts(opaquemodules=false): # allow testing of internal routines
if not (NewSLO :: `module`) then
  WARNING("loading NewSLO failed");
  `quit`(3);
end if;

with(NewSLO):

#####################################################################
#
# plate/array tests
#
#####################################################################

triv := Plate(k, i, Ret(i)):
TestHakaru(triv, Ret(ary(k, i, i)), label="Dirac Plate");

ary0 := Bind(Plate(k, i, Gaussian(0,1)), xs, Ret([xs])):
TestHakaru(ary0, ary0, label="plate roundtripping", ctx = KB:-assert(k::nonnegint,KB:-empty));

ary1  := Bind(Gaussian(0,1), x,
         Bind(Plate(n, i, Weight(density[Gaussian](x,1)(idx(t,i)), Ret(Unit))), ys,
         Ret(x))):
ary1w := 2^(-(1/2)*n+1/2)*exp((1/2)*((sum(idx(t,i),i=0..n-1))^2-(sum(idx(t,i)^2,i=0..n-1))*n-(sum(idx(t,i)^2,i=0..n-1)))/(n+1))*Pi^(-(1/2)*n)/sqrt(2+2*n):
TestHakaru(ary1, 
  Weight(ary1w, Gaussian((sum(idx(t, i), i = 0 .. n-1))/(n+1), 1/sqrt(n+1))),
  label="Wednesday goal", ctx = KB:-assert(n::nonnegint,KB:-empty));
TestHakaru(Bind(ary1, x, Ret(Unit)), Weight(ary1w, Ret(Unit)), 
  label="Wednesday goal total", ctx = KB:-assert(n::nonnegint,KB:-empty));
ary2  := Bind(Gaussian(0,1), x,
         Bind(Plate(n, i, Bind(Gaussian(idx(t,i),1),z, Weight(density[Gaussian](x,1)(idx(t,i)), Ret(z+1)))), ys,
         Ret(ys))):
TestHakaru(ary2, 
  Weight(ary1w, Bind(Plate(n, i, Gaussian(idx(t,i),1)), zs, Ret(ary(n, i, idx(zs,i)+1)))), 
  label="Reason for fission", ctx = KB:-assert(n::nonnegint,KB:-empty));
ary3  := Bind(Gaussian(0,1), x,
         Bind(Plate(n, i, Bind(Gaussian(idx(t,i),1),z, Weight(density[Gaussian](x,1)(idx(t,i)), Ret(z)))), zs,
         Ret(zs))):
TestHakaru(ary3, Weight(ary1w, Plate(n, i, Gaussian(idx(t,i),1))),
  label="Array eta", ctx = KB:-assert(n::nonnegint,KB:-empty));
TestHakaru(Ret(ary(n,i,idx(f(i),i))), label="Don't overdo array eta");

bry1  := Bind(BetaD(alpha,beta), x,
         Bind(Plate(n, i, Weight(x    ^piecewise(idx(y,i)=true ,1) *
                                 (1-x)^piecewise(idx(y,i)=false,1),
                          Ret(Unit))), ys,
         Ret(x))):
bry1s := Weight(Beta(alpha+sum(piecewise(idx(y,i)=true ,1), i=0..n-1),
                     beta +sum(piecewise(idx(y,i)=false,1), i=0..n-1))/Beta(alpha,beta),
         BetaD(alpha+sum(piecewise(idx(y,i)=true ,1), i=0..n-1),
               beta +sum(piecewise(idx(y,i)=false,1), i=0..n-1))):
TestHakaru(bry1, bry1s, 
  label="first way to express flipping a biased coin many times",
  ctx = KB:-assert(n::nonnegint,KB:-empty));

bry2  := Bind(BetaD(alpha,beta), x,
         Bind(Plate(n, i, Weight(x    ^(  idx(y,i)) *
                                 (1-x)^(1-idx(y,i)),
                          Ret(Unit))), ys,
         Ret(x))):
bry2s := Weight(Beta(alpha+  sum(idx(y,i),i=0..n-1),
                     beta +n-sum(idx(y,i),i=0..n-1))/Beta(alpha,beta),
         BetaD(alpha+  sum(idx(y,i),i=0..n-1),
               beta +n-sum(idx(y,i),i=0..n-1))):
TestHakaru(bry2, bry2s, 
  label="second way to express flipping a biased coin many times", 
  ctx = KB:-assert(n::nonnegint,KB:-empty));

fission     := Bind(Plate(k, i, Gaussian(z^i,1)), xs, Plate(k, i, Gaussian(idx(xs,i),1))):
fusion      := Plate(k, i, Bind(Gaussian(z^i,1), x, Gaussian(x,1))):
conjugacies := Plate(k, i, Gaussian(z^i, sqrt(2))):
conjugacies5:= Bind(Gaussian(z^0, sqrt(2)), x0,
               Bind(Gaussian(z^1, sqrt(2)), x1,
               Bind(Gaussian(z^2, sqrt(2)), x2,
               Bind(Gaussian(z^3, sqrt(2)), x3,
               Bind(Gaussian(z^4, sqrt(2)), x4,
               Ret(ary(5, i, piecewise(i=1,x1, i=2,x2, i=3,x3, i=4,x4, x0)))))))):
TestHakaru(eval(fission,{    z=1}), eval(conjugacies ,z=1), verify=normal, label="Conjugacy across iid plates");
TestHakaru(eval(fusion ,{    z=1}), eval(conjugacies ,z=1), verify=normal, label="Conjugacy in iid plate");
TestHakaru(eval(fission,{k=5,z=1}), eval(conjugacies5,z=1), verify=normal, label="Conjugacy across iid plates unrolled");
TestHakaru(eval(fusion ,{k=5,z=1}), eval(conjugacies5,z=1), verify=normal, label="Conjugacy in iid plate unrolled");
TestHakaru(     fission           ,      conjugacies      , verify=normal, label="Conjugacy across plates", ctx=KB:-assert(z>0,KB:-empty));
TestHakaru(     fusion            ,      conjugacies      , verify=normal, label="Conjugacy in plate", ctx=KB:-assert(z>0,KB:-empty));
TestHakaru(eval(fission,{k=5    }),      conjugacies5     , verify=normal, label="Conjugacy across plates unrolled", ctx=KB:-assert(z>0,KB:-empty));
TestHakaru(eval(fusion ,{k=5    }),      conjugacies5     , verify=normal, label="Conjugacy in plate unrolled", ctx=KB:-assert(z>0,KB:-empty));

# Simplifying gmm below is a baby step towards index manipulations we need
gmm := Bind(Plate(k, c, Gaussian(0,1)), xs,
       Bind(Plate(n, i, Weight(density[Gaussian](idx(xs,idx(cs,i)),1)(idx(t,i)), Ret(Unit))), ys,
       Ret(xs))):
gmm_s := Weight(2^(-(1/2)*n)*Pi^(-(1/2)*n)*exp(-(1/2)*(sum(idx(t,i)^2, i=0..n-1))),
         Bind(Plate(k, c, Gaussian(0, 1)), xs,
         Weight(exp(sum(idx(t,i)*idx(xs,idx(cs,i)), i=0..n-1))*exp(-(1/2)*(sum(idx(xs,idx(cs,i))^2, i=0..n-1))),
         Ret(xs)))):
TestHakaru(gmm, gmm_s, label="gmm");

# Detecting Dirichlet-multinomial conjugacy when unrolled
dirichlet := proc(as)
  Bind(Plate(size(as)-1, i, BetaD(sum(idx(as,j), j=0..i), idx(as,i+1))), xs,
  Ret(ary(size(as), i,
          product(idx(xs,j), j=i..size(as)-2)
          * piecewise(0=i, 1, 1-idx(xs,i-1)))))
end proc:
categorical := proc(ps)
  Bind(Counting(0, size(ps)-1), i, Weight(idx(ps,i), Ret(i)))
end proc:
# The next line eta-expands CodeTools[Test] so that its arguments get evaluated
(proc() CodeTools[Test](_passed) end proc)
  (op(2, [unweight(
     fromLO(improve(toLO(
       Plate(n,k,
         Bind(dirichlet(ary(5,i,1)),ps,
           Weight(product(idx(ps,i)^idx(idx(t,k),i),i=0..size(ps)-1),
             Ret(ps))))))))]),
   fromLO(toLO(
     Plate(n,k,
       dirichlet(ary(5,i,1+idx(idx(t,k),i)))))),
   measure(simplify),
   label="Dirichlet-multinomial conjugacy when unrolled");
# We'd like the test above to pass even if the count 5 becomes symbolic.
