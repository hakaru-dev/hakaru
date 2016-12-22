#
#  Currently, these are not 'tests' in the usual sense, in that they do
# not have correct answers encoded.  They are just meant to all be 
# runnable (and are part of the stuff serving as input for the array
# simplification paper we're writing).

kernelopts(assertlevel=2): # be strict on all assertions while testing
kernelopts(opaquemodules=false): # allow testing of internal routines
if not (NewSLO :: `module`) then
  WARNING("loading NewSLO failed");
  `quit`(3);
end if;

with(Hakaru):
with(NewSLO):
with(Loop):

kb := KB:-assert(n :: nonnegint, KB:-empty):
i, kb := KB:-genType(i, HInt(closed_bounds(1..n)), kb):

t1 := Product(idx(x,j),j=1..n):
r1 := unproduct(t1, x, i=1..n, [], `*`, kb, kb);

t2 := 2:
r2 := unproduct(t2, x, i=1..n, [], `*`, kb, kb);

t3 := 2^n:
r3 := unproduct(t3, x, i=1..n, [], `*`, kb, kb);

t4 := Product(2*idx(x,j),j=1..n);
r4 := unproduct(t4, x, i=1..n, [], `*`, kb, kb);

t5 := Product(2+idx(x,j),j=1..n);
r5 := unproduct(t5, x, i=1..n, [], `*`, kb, kb);

t6 := Product(f(idx(x,j)),j=1..n);
r6 := unproduct(t6, x, i=1..n, [], `*`, kb, kb);

t7 := exp(Sum(g(idx(x,k)),k=1..n));
r7 := unproduct(t7, x, i=1..n, [], `*`, kb, kb);

t8 := t6*t7;
r8 := unproduct(t8, x, i=1..n, [], `*`, kb, kb);

t9 := Product(f(idx(x,j+1)),j=0..n-1);
r9 := unproduct(t9, x, i=1..n, [], `*`, kb, kb);

t10 := Product(f(idx(x,j)),j=1..n-1);
r10 := unproduct(t10, x, i=1..n, [], `*`, kb, kb);

# oops, this ones doesn't !!  Going under (above) is
# ok, but over does not.  Neither of the following:
# t10a := Product(f(idx(x,j)),j=1..n+1);
# r10a := unproduct(t10, x, i=1..n, [], `*`, kb, kb);
# t10b := Product(f(idx(x,j)),j=0..n);
# r10b := unproduct(t10, x, i=1..n, [], `*`, kb, kb);

t11 := Product(exp(Sum(f(idx(x,j))+g(idx(x,k)),k=1..j)),j=1..n):
r11 := unproduct(t11, x, i=1..n, [], `*`, kb, kb);

t12 := Product(exp(Sum(f(idx(x,j),j,k)+g(idx(x,k),j,k),k=1..j)),j=1..n):
r12 := unproduct(t12, x, i=1..n, [], `*`, kb, kb);

# this is sort-of buggy as well.
t13 := Product(f(idx(x,5))*g(idx(x,7))*h(j),j=1..n):
r13 := unproduct(t13, x, i=1..n, [], `*`, kb, kb);

# Bug!
# t14 := Product(idx(x,2*j),j=1..n/2):
# r14 := unproduct(t14, x, i=1..n, [], `*`, kb, kb);

t15 := Product(f(idx(x,j),j)*g(idx(x,n+1-j),j)*h(j),j=1..n):
r15 := unproduct(t15, x, i=1..n, [], `*`, kb, kb);

t16 := Product(piecewise(a<b,f(idx(x,j),j),g(idx(x,n+1-j),j)),j=1..n):
r16 := unproduct(t16, x, i=1..n, [], `*`, kb, kb);

t17 := Product(5^idx(x,j)*f(idx(x,j))*g(idx(x,n+1-j)),j=1..n):
r17 := unproduct(t17, x, i=1..n, [], `*`, kb, kb);
