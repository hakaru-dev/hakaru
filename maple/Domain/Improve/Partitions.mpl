single_case_Partition := module()
  uses Domain, Domain_Type;

  export SimplName  := "Single case partition";
  export SimplOrder := 11;

    export ModuleApply := proc(vs :: DomBound, sh :: DomShape, $)
        subsindets(sh, DomSplit, x->do_simp(op(x)));
    end proc;

    local do_simp := proc(p:: Partition,$)::DomShape;
        local r := Partition:-Simpl:-single_nonzero_piece_cps(
            proc(c,v) if v::DomConstrain then DConstrain(conv_bool(c),op(v)) else p end if
            end proc,p,_testzero=(x->x=DSum()));
        if r :: Partition then DSplit(r) else r end if;
    end proc;

    local conv_bool := proc(r, $)
        if r :: {specfunc(`And`), `and`} then
            op(map(conv_bool,r))
        else
            r
        end if;
    end proc;
end module;

redundant_Partition_Pieces := module()
  uses Domain, Domain_Type;

  export SimplName  := "Redundant Partition pieces";
  export SimplOrder := (10+1/2);

  local TRY := proc(bnds, kb, kb_rn, as, pr)
    local r, ns;
    r := subs(kb_rn, op(1,pr));

    ns := op(1,bnds);
    ns := select(b->op(3,b) in {`Int`,`Ints`}, ns);
    ns := map(curry(op,1), ns);

    r := Partition:-Simpl(r, kb, _name_cands=ns) assuming op(as);
    if not r :: Partition then r else pr end if;
  end proc;

  export ModuleApply := proc(vs :: DomBound, sh :: DomShape, $)
    local as := Domain:-Bound:-toConstraints(vs, 'bound_types');
    subsindets(sh, DomSplit, curry(TRY,vs, op(Domain:-Bound:-toKB(vs)),as));
  end proc;
end module;
