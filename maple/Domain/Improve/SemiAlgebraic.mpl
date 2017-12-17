SemiAlgebraic := module()
    uses Domain, Domain_Type, SolveTools, Utilities;
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

    # Check for trivial solutions, which are rejected because they are not an
    # improvement in terms of Hakaru semantics (but SemiAlgebraic doesn't know
    # anything about that)
    local trivial_sol := proc(sh :: DomShape, ctx :: DomBound, $)::truefalse;
      local ps, vs, vsc;
      if sh::DomConstrain then
        evalb(nops(sh)=0)
      elif sh::DomSplit then
        # we assume that the conditions of a solution of SemiAlgebraic cover the
        # entire domain, so it is left to check only the values
        ps := KB:-kb_Partition( op(1,sh), Domain:-Bound:-contextOf(ctx),
                               ((x_,y_)->true), #unused dummy to pass typechecks
                               ((v,kb)->trivial_sol
                                  (v,Domain:-Bound:-onContext(_->kb,ctx))) );
        `and`(op(map(evalb@Partition:-valOf,Partition:-piecesOf(ps))));
      elif sh::DomSum then
        if nops(sh)<>2 then return false end if;
        if ormap(s->not(s::DomConstrain) or nops(s)<>1,sh)
        then return false; end if;
        vs := Domain:-Bound:-varsOf(ctx,"set");
        vsc := map((v->(v,-v)), vs);
        ps := map2(op,1,[op(sh)]);
        ps := map(p->classify_relation(p,v->v in vsc), ps);
        if not(has(ps, {B_LO,B_HI})) then return false; end if;
        if not(the(map2(op,3,ps))) then return false; end if;
        if not(the(map(abs,map2(op,4,ps)))) then return; false end if;
        return true;
      elif sh::DomInto then
        error "solution should not have DIntos: %1", sh;
      else
        error "unrecognized DomShape: %1", sh;
      end if;
    end proc;

    local do_sh := proc( sh :: DomShape, ctx :: DomBound, vs, $)
        local sol;
        if sh :: DomConstrain then
            sol := do_Constrain(sh, ctx, vs);
            sol := `if`(sol::DomShape, sol, postproc(sol));
            if not(sol::DomNoSol) and trivial_sol(sol, ctx) then
              userinfo(3, Domain:-Improve,
                       printf("Discarding solution: %a\n", sol));
              sh;
            else sol end if;
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
