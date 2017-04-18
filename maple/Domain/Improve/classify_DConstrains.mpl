local classify_DConstrains := module()
  export ModuleApply := proc(dbnds::DomBound,dsh::DomShape,$)
    subsindets(dsh, DomConstrain, x->classify_Rels([op(x)], dbnds));
  end proc;

  export classify_Rel := proc(r0,dbnd,$)
    local r := r0;
    vars := {Domain:-Bound:-varsOf(dbnd)[]};
    if r :: {`<=`,`<`} then

      if rhs(r) in vars then
        r := op(0,r)(rhs(r),lhs(r));
        mk_k := flip_rel[op(0,r)]; bnd_k := B_LO;
      elif lhs(r) in vars then
        mk_k := op(0,r);           bnd_k := B_HI;
      else
        return [ DConstrain, r0 ];
      end if;

      i := Domain:-Bound:-varIx_mb(dbnd, lhs(r));
      if i >= 0 then
        var_k := op([1,i,3], dbnd);
        q := Domain:-ExtBound[var_k]:-RecogBound(mk_k,rhs(r));
        if q = NULL then
          [ DConstrain, r0 ]
        else
          [ DInto(lhs(r)), r0, q, bnd_k, countVs(vars,q) ];
        end if;
      else
        [ DConstrain, r0 ]
      end if;
    else
      [ DConstrain, r0 ]
    end if;
  end proc;

  export classify_Rels := proc(rs0,dbnd,$)
    local rs := rs0;

    rs := map(r->classify_Rel(r,dbnd), rs);
    rs := [ListTools[Categorize]( ((a,b) -> op(1,a)=op(1,b) ), rs )];
    cs1, rs := selectremove(x->op([1,1],x)=DConstrain, rs);
    rs, cs2 := selectremove(x->nops(x)=1 or (nops(x)=2 and op([1,4],x)<>op([2,4],x)), rs);

    rs := map(r->make_DInto(r,dbnd),rs);

    cs := map(c->map(q->op(2,q),c)[], [op(cs1),op(cs2)]);
    cs := DConstrain(op(cs));

    rs := foldr((f,g)->f@g,x->x,op(rs))(cs);

    rs;
  end proc;

  export make_DInto := proc(r::list([specfunc(DInto),anything,anything,identical(B_LO,B_HI),nonnegint]), dbnd, $)
    var_nm := op([1,1,1], r);
    var_ty := Domain:-Bound:-get(dbnd, var_nm)[1];
    var_ty := foldr( ((q,x)->op(3,q)(x)), var_ty, op(r) );
    (ctx -> DInto(var_nm, var_ty, ctx))
  end proc;
  local flip_rel := table([`=`=`=`,`<>`=`<>`,`<=`=`>=`,`<`=`>`,`>=`=`<=`,`>`=`<`]);
  local countVs := ((vs,c)-> nops(indets(c, DomBoundVar) intersect {op(vs)} ));
end module;
