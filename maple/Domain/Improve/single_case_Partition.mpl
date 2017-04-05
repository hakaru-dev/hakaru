local single_case_Partition := module()
    export ModuleApply := proc(vs :: DomBound, sh :: DomShape, $)
        subsindets(sh, DomSplit, do_simp);
    end proc;

    local do_simp := proc(p,$)
        Partition:-Simpl:-single_nonzero_piece_cps(
            proc(c,v) if v::DomConstrain then DConstrain(conv_bool(c),op(v)) else p end if
            end proc,op(1,p),_testzero=(x->x=DSum()))
    end proc;

    local conv_bool := proc(r, $)
        if r :: {specfunc(`And`), `and`} then
            op(map(conv_bool,r))
        else
            r
        end if;
    end proc;
end module;
