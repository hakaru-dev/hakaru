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

fission     := Bind(Plate(k, i, Gaussian(0,1)), xs, Plate(k, i, Gaussian(idx(xs,i),1))):
fusion      := Plate(k, i, Bind(Gaussian(0,1), x, Gaussian(x,1))):
conjugacies := Plate(k, i, Gaussian(0, sqrt(2))):
TestHakaru(fission, conjugacies, label="Conjugacy across plates");
TestHakaru(fusion,  conjugacies, label="Conjugacy in plate");

# Simplifying gmm below is a baby step towards index manipulations we need
# gmm is not tested?
gmm := Bind(Plate(k, c, Gaussian(0,1)), xs,
       Bind(Plate(n, i, Weight(density[Gaussian](idx(xs,idx(cs,i)),1)(idx(t,i)), Ret(Unit))), ys,
       Ret(xs))):
