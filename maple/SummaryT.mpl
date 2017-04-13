kernelopts(assertlevel=2): # be strict on all assertions while testing
with(Hakaru):
with(KB):
with(Summary):

module()
  local kb, b, mr, f, bkt;
  kb := empty;
  b, kb := genType(b, HInt(Bound(`>=`,0),Bound(`<=`,size(as)-1)), kb);
  mr, f := summarize(piecewise(b=idx(z,i), idx(t,i), 0),
                     kb, i, summary);
  CodeTools[Test](indets(mr, 'Add(anything)'), {Add(idx(t,i))},
                  label="Simple example from Summary.txt");
  f := simplify_factor_assuming(f, kb);
  bkt := bucket(mr, i=0..size(t)-1);
  CodeTools[Test](eval(f, summary=bkt),
                  sum(piecewise(b=idx(z,i), idx(t,i), 0), i=0..size(t)-1),
                  simplify);
end module:

module()
  local kb, zNew, b, mr, f, bkt;
  kb := empty;
  zNew, kb := genType(zNew, HInt(Bound(`>=`,0),Bound(`<=`,size(as)-1)), kb);
  b, kb := genType(b, HInt(Bound(`>=`,0),Bound(`<=`,size(as)-1)), kb);
  mr, f := summarize(piecewise(b=piecewise(i=docUpdate,zNew,idx(z,i)),
                               idx(t,i)),
                     kb, i, summary);
  CodeTools[Test](indets(mr, 'Add(anything)'), {Add(idx(t,i))},
                  label="First \"summate i\" in offshore under gmm_gibbs.hk");
  f := simplify_factor_assuming(f, kb);
  bkt := bucket(mr, i=0..size(t)-1);
  CodeTools[Test](eval(f, summary=bkt),
                  piecewise(b=zNew,
                            sum(piecewise(i=docUpdate, idx(t,i), 0),
                                i=0..size(t)-1),
                            0) +
                  sum(piecewise(And(b=idx(z,i), Not(i=docUpdate)),
                                idx(t,i),
                                0),
                      i=0..size(t)-1),
                  simplify);
end module:

module()
  local kb, docUpdate, zNew, k, i, mr, f, bkt;
  kb := empty;
  docUpdate, kb := genType(docUpdate, HInt(Bound(`>=`,0),Bound(`<=`,size(z)-1)), kb);
  zNew, kb := genType(zNew, HInt(Bound(`>=`,0),Bound(`<=`,size(topic_prior)-1)), kb);
  k, kb := genType(k, HInt(Bound(`>=`,0),Bound(`<=`,size(topic_prior)-1)), kb);
  i, kb := genType(i, HInt(Bound(`>=`,0),Bound(`<=`,size(word_prior)-1)), kb);
  mr, f := summarize(piecewise(idx(doc,j)=docUpdate,
                               piecewise(k=zNew,
                                         piecewise(i=idx(w,j),1,0),
                                         0),
                               0),
                     kb, j, summary);
  CodeTools[Test](indets(mr, 'Add(anything)'), {Add(1)},
                  label="First \"summate j\" in offshore under naive_bayes_gibbs.hk");
  f := simplify_factor_assuming(f, kb);
  bkt := bucket(mr, j=0..size(w)-1);
  CodeTools[Test](eval(f, summary=bkt),
                  piecewise(k=zNew,
                            sum(piecewise(And(i=idx(w,j),
                                              docUpdate=idx(doc,j)),
                                          1,
                                          0),
                                j=0..size(w)-1),
                            0),
                  simplify);
end module:

module()
  local kb, i18, mr, f, bkt;
  kb := empty;
  i18, kb := genType(i18, HInt(Bound(`>=`,0),Bound(`<=`,word_prior_size-1)), kb);
  mr, f := summarize(piecewise(docUpdate=idx(doc,i13),
                               piecewise(And(i=zNew8, i18=idx(w,i13)), 1, 0),
                               0),
                     kb, i13, summary);
  CodeTools[Test](indets(mr, 'Add(anything)'), {Add(1)},
                  label="Spenser's example from 2017-01-23 email");
  f := simplify_factor_assuming(f, kb);
  bkt := bucket(mr, i13=0..word_prior_size-1);
  CodeTools[Test](eval(f, summary=bkt),
                  piecewise(i=zNew8,
                            sum(piecewise(And(i18=idx(w,i13),
                                              docUpdate=idx(doc,i13)),
                                          1,
                                          0),
                                i13=0..word_prior_size-1), 0),
                  simplify);
end module:
