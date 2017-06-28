SemiAlgebraic := module()
    uses Domain, Domain_Type, SolveTools;
    export SimplName  := "SemiAlgebraic";
    export SimplOrder := 6+(1/2);

    export ModuleApply := proc(dbnds :: DomBound, dshape :: DomShape, $)
        local vs;
        vs := ListTools[Reverse](Domain:-Bound:-varsOf(dbnds));
        vs := map(v->if v::list then op(1,v) else v end if, vs);
        do_sh( dshape , dbnds, vs );
    end proc;

    local extra_sol := (c -> c::`=` and (lhs(c)::DomBoundVar and evalb(lhs(c)=rhs(c))));
    local postproc := proc(sol, $)
      foldl((x,k)->subsindets(x,op(k)), sol
           ,[specfunc('piecewise')
            ,x->DSplit(Partition:-PWToPartition(x,'check_valid'))]
           ,[list(list),DSum@op]
           ,[list(relation),x->DConstrain(remove(extra_sol,x)[])]);
    end proc;

    local do_sh := proc( sh :: DomShape, ctx :: DomBound, vs, $)
        local sol;
        if sh :: DomConstrain then
            sol := do_Constrain(sh, ctx, vs);
            if sol :: DomShape then sol
            else postproc(sol) end if;
        elif sh :: DomSplit then
            DSplit(Partition:-Amap(
              [ (c,_)->c
              , (p,c)-> p->do_sh(p, applyop(cs->{c,op(cs)},2,ctx), vs)
              , c->c ], op(1, sh) ));
        elif sh :: DomSum then
            map(s->do_sh(s, ctx, vs), sh);
        else
            DNoSol(sprintf("Don't know how to solve DOMAIN(%a, %a)", ctx, sh));
        end if;
    end proc;

    local do_Constrain := proc( sh :: DomConstrain , ctx, vs_, $ )
        local ts, vs := vs_, cs;
        cs := { op( Domain:-Bound:-toConstraints(ctx,'no_infinity') ), op(sh) } ;
        ts, cs := selectremove(type, cs, `::`);
        ts := select(t->op(2,t)<>real, ts);
        if ts <> {} and has(cs,ts) then
          WARNING("Variables of unrecognized types being passed to SemiAlgebraic: %1",ts);
        end if;
        try SemiAlgebraic(cs, vs);
        catch: DNoSol(StringTools[FormatMessage](lastexception[2..-1]));
        end try;
    end proc;
end module; #SemiAlgebraic
