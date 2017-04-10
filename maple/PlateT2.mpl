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

TestEfficient( dice_index, dice_index_t, KB:-empty, label="dice index" ):
