kernelopts(assertlevel=2): # be strict on all assertions while testing
kernelopts(opaquemodules=false): # allow testing of internal routines
if not (NewSLO :: `module`) then
  WARNING("loading NewSLO failed");
  `quit`(3);
end if;

with(Hakaru):
with(NewSLO):

#####################################################################
#
# plate/array tests
#
#####################################################################

triv := Plate(k, i, Ret(i)):
TestHakaru(triv, Ret(ary(k, i, i)), label="Dirac Plate");

ary0 := Bind(Plate(k, i, Gaussian(0,1)), xs, Ret([xs])):
TestHakaru(ary0, ary0, label="plate roundtripping", ctx = [k::nonnegint]);

ary1  := Bind(Gaussian(0,1), x,
         Bind(Plate(n, i, Weight(density[Gaussian](x,1)(idx(t,i)), Ret(Unit))), ys,
         Ret(x))):
ary1w := 2^(-(1/2)*n+1/2)*exp((1/2)*((sum(idx(t,i),i=0..n-1))^2-(sum(idx(t,i)^2,i=0..n-1))*n-(sum(idx(t,i)^2,i=0..n-1)))/(n+1))*Pi^(-(1/2)*n)/sqrt(2+2*n):
TestHakaru(ary1, 
  Weight(ary1w, Gaussian((sum(idx(t, i), i = 0 .. n-1))/(n+1), 1/sqrt(n+1))),
  label="Wednesday goal", ctx = [n::nonnegint]);
TestHakaru(Bind(ary1, x, Ret(Unit)), Weight(ary1w, Ret(Unit)), 
  label="Wednesday goal total", ctx = [n::nonnegint]);
ary2  := Bind(Gaussian(0,1), x,
         Bind(Plate(n, i, Bind(Gaussian(idx(t,i),1),z, Weight(density[Gaussian](x,1)(idx(t,i)), Ret(z+1)))), ys,
         Ret(ys))):
TestHakaru(ary2, 
  Weight(ary1w, Bind(Plate(n, i, Gaussian(idx(t,i),1)), zs, Ret(ary(n, i, idx(zs,i)+1)))), 
  label="Reason for fission", ctx = [n::nonnegint]);
ary3  := Bind(Gaussian(0,1), x,
         Bind(Plate(n, i, Bind(Gaussian(idx(t,i),1),z, Weight(density[Gaussian](x,1)(idx(t,i)), Ret(z)))), zs,
         Ret(zs))):
TestHakaru(ary3, Weight(ary1w, Plate(n, i, Gaussian(idx(t,i),1))),
  label="Array eta", ctx = [n::nonnegint]);
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
  ctx = [n::nonnegint]);

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
  ctx = [n::nonnegint]);

fission     := Bind(Plate(k, i, Gaussian(f(i),1)), xs, Plate(k, i, Gaussian(idx(xs,i),1))):
fusion      := Plate(k, i, Bind(Gaussian(f(i),1), x, Gaussian(x,1))):
conjugacies := Plate(k, i, Gaussian(f(i), sqrt(2))):
conjugacies5:= Bind(Gaussian(f(0), sqrt(2)), x0,
               Bind(Gaussian(f(1), sqrt(2)), x1,
               Bind(Gaussian(f(2), sqrt(2)), x2,
               Bind(Gaussian(f(3), sqrt(2)), x3,
               Bind(Gaussian(f(4), sqrt(2)), x4,
               Ret(ary(5, i, idxl([x0,x1,x2,x3,x4],i)))))))):
TestHakaru(     fission                  ,      conjugacies                   , verify=normal, label="Conjugacy across plates (function)");
TestHakaru(     fusion                   ,      conjugacies                   , verify=normal, label="Conjugacy in plate (function)");
TestHakaru(eval(fission,{k=5           }),      conjugacies5                  , verify=normal, label="Conjugacy across plates unrolled (function)");
TestHakaru(eval(fusion ,{k=5           }),      conjugacies5                  , verify=normal, label="Conjugacy in plate unrolled (function)");
TestHakaru(eval(fission,{    f=1       }), eval(conjugacies ,{    f=1       }), verify=normal, label="Conjugacy across iid plates");
TestHakaru(eval(fusion ,{    f=1       }), eval(conjugacies ,{    f=1       }), verify=normal, label="Conjugacy in iid plate");
TestHakaru(eval(fission,{k=5,f=1       }), eval(conjugacies5,{    f=1       }), verify=normal, label="Conjugacy across iid plates unrolled");
TestHakaru(eval(fusion ,{k=5,f=1       }), eval(conjugacies5,{    f=1       }), verify=normal, label="Conjugacy in iid plate unrolled");
TestHakaru(eval(fission,{    f=(i->z^i)}), eval(conjugacies ,{    f=(i->z^i)}), verify=normal, label="Conjugacy across plates", ctx=[z>0]);
TestHakaru(eval(fusion ,{    f=(i->z^i)}), eval(conjugacies ,{    f=(i->z^i)}), verify=normal, label="Conjugacy in plate", ctx=[z>0]);
TestHakaru(eval(fission,{k=5,f=(i->z^i)}), eval(conjugacies5,{k=5,f=(i->z^i)}), verify=normal, label="Conjugacy across plates unrolled", ctx=[z>0]);
TestHakaru(eval(fusion ,{k=5,f=(i->z^i)}), eval(conjugacies5,{k=5,f=(i->z^i)}), verify=normal, label="Conjugacy in plate unrolled", ctx=[z>0]);

# Simplifying gmm below is a baby step towards index manipulations we need
gmm := Bind(Plate(k, c, Gaussian(0,1)), xs,
       Bind(Plate(n, i, Weight(density[Gaussian](idx(xs,idx(cs,i)),1)(idx(t,i)), Ret(Unit))), ys,
       Ret(xs))):
gmm_s := Weight(2^(-(1/2)*n)*Pi^(-(1/2)*n)*exp(-(1/2)*(sum(idx(t,i)^2, i=0..n-1)))*exp((1/2)*(sum((sum(piecewise(c=idx(cs,i), idx(t,i), 0), i=0..n-1))^2/(sum(piecewise(c=idx(cs,i), 1, 0), i=0..n-1)+1), c=0..k-1)))*(1/(product(sum(piecewise(c=idx(cs,i), 1, 0), i=0..n-1)+1, c=0..k-1)))^(1/2),
         Plate(k, c, Gaussian((sum(piecewise(c=idx(cs,i), idx(t,i), 0), i=0..n-1))/(sum(piecewise(c=idx(cs,i), 1, 0), i=0..n-1)+1), (1/(sum(piecewise(c=idx(cs,i), 1, 0), i=0..n-1)+1))^(1/2)))):
TestHakaru(gmm, gmm_s, label="gmm (currently failing -- due to alpha-equivalence)");

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
   label="Conjugacy between unrolled symmetric Dirichlet and multinomial");
# We'd like the test above to pass even if the count 5 becomes symbolic.
# Below is some progress towards this goal:
TestHakaru(dirichlet(as), label="Dirichlet symbolic prior roundtrip");
TestHakaru(Context(size(as)>0,
             Bind(dirichlet(as),ps,
               Weight(product(idx(ps,i)^idx(t,i),i=0..size(ps)-1),
                 Ret(ps)))),
           Context(size(as)>0,
             Weight(product(Beta(idx(as,i+1)+idx(t,i+1),idx(t,0)+sum(idx(as,k),k=0..i)+sum(idx(t,k),k=1..i)),i=0..size(as)-2)
                    /product(Beta(idx(as,i+1),sum(idx(as,k),k=0..i)),i=0..size(as)-2),
               Bind(Plate(size(as)-1,i,BetaD(idx(t,0)+sum(idx(as,k),k=0..i)+sum(idx(t,k),k=1..i),idx(as,i+1)+idx(t,i+1))),xs,
                 Ret(ary(size(as),i,piecewise(i=0,product(idx(xs,j),j=0..size(as)-2),product(idx(xs,j),j=i..size(as)-2)*(1-idx(xs,i-1)))))))),
           label="Conjugacy between rolled Dirichlet and multinomial");
