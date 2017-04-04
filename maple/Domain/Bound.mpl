# Convert Domain to a KB. Very partial, mainly for backwards compatibility
# for parts of the code which still work with KB.
export Bound := module ()
    export toKB := proc(dom :: DomBound, kb0 :: t_kb, $)::[t_kb_mb, list(name=name)];
        local kb := kb0, vs := op(1, dom), rn := []
            , vn, vt, make, lo, hi, vn_rn, rn_t, v ;
        for v in vs do
            vn, vt, make := op(v);
            lo, hi := ExtBound[make]:-SplitBound(vt);
            vn_rn, kb := ExtBound[make]:-MakeKB( vn, lo, hi, kb );
            rn := [ vn=vn_rn, op(rn) ];
        end do;
        [ kb, rn ]
    end proc;

    export varsOf := proc(dom :: DomBound, $)::list(name);
        map(x->op(1,x), op(1, dom));
    end proc;

    export isEmpty := proc(dom :: DomBound, $)::truefalse;
        evalb(nops(op(1,dom))=0);
    end proc;

    export get := proc(dom :: DomBound, var :: name, $)
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

    local constrain := proc( opts, vn::name, ty::range, mk :: DomBoundKind, $ )
                    :: set({relation, `::`});
        local lo, hi, noi, bt
            , noinf := evalb('no_infinity' in opts)
            , btys  := evalb('bound_types' in opts);
        lo,hi := Domain:-ExtBound[mk]:-SplitBound(ty);
        noi := `if`(noinf,mk->b->if b in {infinity,-infinity} then {} else {mk(b)} end if
                         ,mk->b->{mk(b)} );
        bt  := `if`(btys, { vn :: Domain:-ExtBound[mk]:-BoundType }, {});
        { noi(x->Domain:-ExtBound[mk]:-Constrain( x, vn ))(lo)[]
        , noi(x->Domain:-ExtBound[mk]:-Constrain( vn, x ))(hi)[]
        , bt[]}
    end proc;

    local toConstraints_opts := { 'no_infinity', 'bound_types' };
    export toConstraints := proc( bnd :: DomBound )
        local cs, opts, bad_opts, noinf;
        opts := { args[2..-1] } ;
        bad_opts := opts minus toConstraints_opts;
        if bad_opts <> {} then
            error "invalid arguments: %1", bad_opts;
        end if;
        {op(map(b->constrain(opts, op(b))[], op(1,bnd)))};
    end proc;
end module;#Bound
