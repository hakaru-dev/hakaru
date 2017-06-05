# Convert Domain to a KB. Very partial, mainly for backwards compatibility
# for parts of the code which still work with KB.
export Bound := module ()
    uses Domain_Type;
    export toKB := proc(dom :: DomBound, $)::[t_kb_mb, list(name=name)];
        local kb := contextOf(dom), vs := op(1, dom), rn := []
            , vn, vt, make, lo, hi, vn_rn, rn_t, v ;
        for v in vs do
            vn, vt, make := op(v);
            lo, hi := ExtBound[make]:-SplitRange(vt);
            vn_rn, kb := ExtBound[make]:-MakeKB( vn, lo, hi, kb );
            rn := [ vn=vn_rn, op(rn) ];
        end do;
        [ kb, remove(type,rn,And({`=`(name,anything),`=`(anything,name)},satisfies(evalb))) ]
    end proc;

    export varsOf := proc(dom :: DomBound, output::identical("list","set","seq"):="list")
      local v := map(x->op(1,x), op(1, dom));
      op(table(["list"=[v],"set"=[{op(v)}],"seq"=v])[output]);
    end proc;

    export withVarsIxs := proc(dom :: DomBound, $) :: DomBound;
        DBound( op(1..2,dom), table([ seq(op([1,i,1],dom)=i,i=1..nops(op(1,dom))) ]) );
    end proc;

    export varIx := proc(dom0::DomBound, v::DomBoundVar, $)::nonnegint;
      local i := varIx_mb(dom0,v);
      if i = -1 then
        error "cannot find var %1 in %2", v, dom0;
      else i end if;
    end proc;

    export varIx_mb := proc(dom0::DomBound, v::DomBoundVar, $)::{nonnegint,identical(-1)};
      local dom := `if`(nops(dom0)>=3, (_->_), withVarsIxs)(dom0);
      if assigned(op(3,dom)[v]) then
        op(3,dom)[v]
      else
        -1
      end if;
    end proc;

    export isEmpty := proc(dom :: DomBound, $)::truefalse;
        evalb(nops(op(1,dom))=0);
    end proc;

    export get := proc(dom :: DomBound, var :: DomBoundVar, $)
        local th;
        th := select(x->op(1,x)=var, op(1,dom));
        if nops(th) = 1 then
            op([1,2], th), op([1,3], th)
        elif nops(th) = 0 then
            error "cannot find var %1 in %2", var, dom;
        else
            error "multiple references in %1", dom;
        end if;
    end proc;

    export upd := proc(dom0 :: DomBound, vr :: DomBoundVar, ty :: DomBoundRange, $)
        local dom := `if`(nops(dom0)>=3, (_->_), withVarsIxs)(dom0), i
            , old_lo,old_hi, lo,hi, old_ty, new_ty, _, vr_k;
        i := varIx(dom, vr);

        _, old_ty, vr_k := op(op([1,i], dom));
        old_lo,old_hi := Domain:-ExtBound[vr_k]:-SplitRange(old_ty);
        lo, hi        := Domain:-ExtBound[vr_k]:-SplitRange(ty);

        if lo :: realcons then
          lo := Domain:-ExtBound[vr_k]:-Max(old_lo, lo);
        end if;
        if hi :: realcons then
          hi := Domain:-ExtBound[vr_k]:-Min(old_hi, hi);
        end if;

        new_ty := Domain:-ExtBound[vr_k]:-MakeRange(lo,hi);

        subsop([1,i,2]=new_ty, dom);
    end proc;

    local constrain := proc( opts, vn::DomBoundVar, ty::DomBoundRange, mk :: DomBoundKind, $ )
                    :: set({relation, `::`});
        local lo, hi, noi, bt
            , noinf := evalb('no_infinity' in opts)
            , btys  := evalb('bound_types' in opts);
        lo,hi := Domain:-ExtBound[mk]:-SplitRange(ty);
        bt  := `if`(btys, { vn :: Domain:-ExtBound[mk]:-BoundType }, {});
        bt := { Domain:-ExtBound[mk]:-Constrain( lo, vn )
        , Domain:-ExtBound[mk]:-Constrain( vn, hi )
        , bt[]};
        `if`(noinf,x->remove(c->c::relation and ormap(s->s(c)::identical(infinity,-infinity),[lhs,rhs]), x),_->_)
            (bt);
    end proc;

    local toConstraints_opts := { 'no_infinity', 'bound_types' };
    local toConstraints_to_remove :=
      (c->c::`::` and rhs(c)=TopProp);
    export toConstraints := proc( bnd :: DomBound )
        local cs, opts, bad_opts, noinf;
        opts := { args[2..-1] } ;
        bad_opts := opts minus toConstraints_opts;
        if bad_opts <> {} then
            error "invalid arguments: %1", bad_opts;
        end if;
        remove(toConstraints_to_remove,
          {op(map(b->constrain(opts, op(b))[], op(1,bnd)))
          ,op(KB:-kb_to_assumptions(contextOf(bnd))) } );
    end proc;

    export contextOf := proc(x::DomBound,$)::t_kb;
      `if`(nops(x)>1,op(2,x),KB:-empty);
    end proc;
end module;#Bound
