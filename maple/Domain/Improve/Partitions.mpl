single_case_Partition := module()
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
  export SimplName  := "Redundant Partition pieces";
  export SimplOrder := (10+1/2);

  export ModuleApply := proc(vs :: DomBound, sh :: DomShape, $)
    local as := Domain:-Bound:-toConstraints(vs, 'bound_types');
    subsindets(sh, DomSplit, proc(pr)
        local r; r := Partition:-Simpl(op(1,pr)) assuming op(as);
        if not r :: Partition then r else pr end if;
      end proc);
  end proc;
end module;
