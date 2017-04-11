interface(screenwidth=9999):
if not (NewSLO :: `module`) then
  WARNING("loading NewSLO failed");
  `quit`(3);
end if;

with(Hakaru):
with(NewSLO):

#####################################################################
#
# Dirichlet conjugacy tests 
#
#####################################################################

# an encoding of drichlet in terms of BetaD
dirichlet := (lam(as, HArray(HReal(Bound(`>=`,0))), Bind(Plate((size(as) + (-(1))), i, BetaD(sum(idx(as, j), j=(i + 1)..(size(as))-1), idx(as, i))), xs, Ret(ary(size(as), i, eval((x * case(((i + 1) = size(as)), Branches(Branch(PDatum(true,PInl(PDone)), 1), Branch(PDatum(false, PInr(PInl(PDone))), (1 + (-(idx(xs, i)))))))), x=(product(idx(xs, j), j=0..(i)-1)))))))):

dice_index := (lam(t, HArray(HArray(HInt(Bound(`>=`,0)))), Plate(size(t), k, Bind(app(dirichlet, ary(size(idx(t, k)), i, (1/1))),
ps, Bind(Plate(size(idx(t, k)), i, Msum(Weight(idx(ps, idx(idx(t, k), i)), Ret(Datum(unit, Inl(Done)))))), _, Ret(ps)))))): 
dice_index_t := HFunction(HArray(HArray(HInt(Bound(`>=`,0)))), HMeasure(HArray(HArray(HReal(Bound(`>=`,0)))))):


gmm_gibbs := eval(lam(as, HArray(HReal(Bound(`>=`,0))), lam(z, HArray(HInt(Bound(`>=`,0))), lam(t, HArray(HReal()), lam(docUpdate, HInt(Bound(`>=`,0)), case(And((size(z) = size(t)), docUpdate < size(z)), Branches(Branch(PDatum(true, PInl(PDone)), Bind(app(dirichlet, as), theta, Bind(Plate(size(as), k, Gaussian(0, 1)), phi, Bind(Categorical(ary(size(as), i, 1)), zNew, Bind(Plate(size(t), i, eval(Bind(Bind(Msum(Weight((idx(theta, zz) * 1/(sum(idx(theta, x0), x0=0..(size(theta))-1))), Ret(Datum(unit, Inl(Done))))), x20, Ret(zz)), zz, Bind(Msum(Weight((exp(((-(((idx(t, i) + (-(idx(phi, zz)))) ^ 2))) * 1/(((2/1) * (1 ^ 2))))) * 1/(1) * 1/(root(((2/1) * Pi), 2))), Ret(Datum(unit, Inl(Done))))), x21, Ret(idx(t, i)))), zz=(case((i = docUpdate), Branches(Branch(PDatum(true, PInl(PDone)), zNew), Branch(PDatum(false, PInr(PInl(PDone))), idx(z, i))))))), t, Ret(zNew)))))), Branch(PDatum(false, PInr(PInl(PDone))), Msum()))))))), dirichlet=(lam(as, HArray(HReal(Bound(`>=`,0))), Bind(Plate((size(as) + (-(1))), i, BetaD(sum(idx(as, j), j=(i + 1)..(size(as))-1), idx(as, i))), xs, Ret(ary(size(as), i, eval((x * case(((i + 1) = size(as)),Branches(Branch(PDatum(true, PInl(PDone)), 1), Branch(PDatum(false, PInr(PInl(PDone))), (1 + (-(idx(xs, i)))))))), x=(product(idx(xs, j), j=0..(i)-1))))))))):
gmm_gibbs_t := HFunction(HArray(HReal(Bound(`>=`,0))), HFunction(HArray(HInt(Bound(`>=`,0))), HFunction(HArray(HReal()), HFunction(HInt(Bound(`>=`,0)), HMeasure(HInt(Bound(`>=`,0))))))):


#####################################################################
TestEfficient( dice_index, dice_index_t, KB:-empty, label="dice index" ):
TestEfficient( gmm_gibbs, gmm_gibbs_t, KB:-empty, label="gmm gibbs" ):

