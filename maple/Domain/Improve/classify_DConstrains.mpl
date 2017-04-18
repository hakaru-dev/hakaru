local classify_DConstrains := module()
  export ModuleApply := proc(dbnds::DomBound,dsh::DomShape,$)
    subsindets(dsh, DomConstrain, x->classify_Rels([op(x)], dbnds));
  end proc;

  # Split relations into those we can incorporate
  # into bounds and others; this process also includes
  # some intermediate computations about the new bound:
  #  [ DInto(var), orig, upd_bound, bound_kind, numVars ]
  #    var         :=   variable to be modified
  #    orig        :=   the original relation
  #    upd_bound   :=   how to modify (a function)
  #    bound_kind  :=   {LO/HI}
  #    numVars     :=   how many variables are mentioned by the bound
  local classify_Rel := proc(r0,dbnd,$)
    local ret, r := r0;
    ret := [ DConstrain, r0 ];
    vars := {Domain:-Bound:-varsOf(dbnd)[]};
    if r :: {`<=`,`<`} then
      if rhs(r) in vars then
        r := op(0,r)(rhs(r),lhs(r));
        mk_k := flip_rel[op(0,r)]; bnd_k := B_LO;
      elif lhs(r) in vars then
        mk_k := op(0,r);           bnd_k := B_HI;
      else
        return ret;
      end if;

      i := Domain:-Bound:-varIx_mb(dbnd, lhs(r));
      if i >= 0 then
        var_k := op([1,i,3], dbnd);
        q := Domain:-ExtBound[var_k]:-RecogBound(mk_k,rhs(r));
        if q <> NULL then
          ret := [ DInto(lhs(r)), r0, q, bnd_k, countVs(vars,q) ];
        end if;
      end if;
    end if;
    ret;
  end proc;

  # Classifies a set of relations as potential bounds. The process
  # is as follows:
  #  - Classify each relation individually (see classify_Rel)
  #  - "Categorize" by the classification
  #  - Split relations which will be DConstrains, and those where we found
  #      more than one LO/HI bound or more than 2 bounds total.
  #  - Sort the relations which are to become bounds by the number of variables
  #      mentioned in the bound
  #  - Rebuild the continuations producing each new bound (see make_DInto)
  #  - Rebuild the leftover relations as a DConstrain.
  #  - Squash together ("foldr (.) id fs z") the continuations and leftover relations.
  local classify_Rels := proc(rs0,dbnd,$)
    local rs := rs0;
    rs := map(r->classify_Rel(r,dbnd), rs);
    rs := [ListTools[Categorize]( ((a,b) -> op(1,a)=op(1,b) ), rs )];
    cs1, rs := selectremove(x->op([1,1],x)=DConstrain, rs);
    rs, cs2 := selectremove(x->nops(x)=1 or (nops(x)=2 and op([1,4],x)<>op([2,4],x)), rs);
    rs := sort(rs, key=(x->-(`+`( seq(op(3,z),z=x) ))));
    rs := map(r->make_DInto(r,dbnd),rs);
    cs := DConstrain(map(c->map(q->op(2,q),c)[], [op(cs1),op(cs2)])[]);
    foldr((f,g)->f@g,x->x,op(rs))(cs);
  end proc;

  # Rebuild a classified (by classify_Rel) relation; this
  # takes a list of such classifications, all of whose variable should
  # be identical, and for which the different bound kinds are all distinct.
  # None of this is checked!
  # (since there are 2 bound kinds, this list is at most length 2)
  local make_DInto := proc(r::list([specfunc(DInto),anything,anything,identical(B_LO,B_HI),nonnegint]), dbnd, $)
    var_nm := op([1,1,1], r);
    var_ty := Domain:-Bound:-get(dbnd, var_nm)[1];
    var_ty := foldr( ((q,x)->op(3,q)(x)), var_ty, op(r) );
    (ctx -> DInto(var_nm, var_ty, ctx))
  end proc;
  local flip_rel := table([`=`=`=`,`<>`=`<>`,`<=`=`>=`,`<`=`>`,`>=`=`<=`,`>`=`<`]);
  local countVs := ((vs,c)-> nops(indets(c, DomBoundVar) intersect {op(vs)} ));
end module;
