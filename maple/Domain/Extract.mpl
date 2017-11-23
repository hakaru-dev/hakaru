# Extract a domain from an expression
export Extract := module ()
  uses Domain_Type, Utilities;
  export ModuleApply := proc(e, kb, $) :: [ HDomain, anything, list(`=`) ];
    local b, eb, s, es, kb1, rn, ws;
    b, eb, ws := op(Bound(e));
    kb1, rn := Domain:-Bound:-toKB(b)[];
    b, eb, ws := subs(rn,[b,eb,ws])[];
    s, es := op(Shape(eb, kb1));
    [ DOMAIN(b, s), es, ws ];
  end proc;

  # Extract a domain bound from an expression
  # This pops off the integration constructors recursively, keeping
  # track of the bounds in a KB (which literally become the DBound).
  export Bound := module ()
    export ModuleApply := proc(e, $) :: [ DomBound, anything, list(`=`) ];
      local arg, vars, kb, ws, w0;
      arg, vars, ws := do_extract(e)[];
      vars := Domain:-Bound:-withVarsIxs(DBound(vars));
      ws := map(`*`@op,ws);
      w0 := op(1,ws); ws := subsop(1=NULL,ws);
      if not(nops(ws)=nops(op(1,vars))) then
        error "number of outer weights doesn't match number of vars: %1, %2",
              op(1,vars), ws;
      end if;
      [ vars , w0*arg, zip(`=`,map2(op,1,op(1,vars)),ws) ];
    end proc;

    local do_extract_arg := proc(kind, arg_)
      local x0, x, vars, ws,
            arg := op(1,arg_),
            rest := op(2..-1,arg_),
            rng;
      x0  := ExtBound[kind]:-ExtractVar(rest);   # variable name
      rng := ExtBound[kind]:-ExtractRange(rest); # variable range
      x   := DInto(x0, rng, kind);               # the variable spec
      arg, vars, ws := do_extract(arg)[];
      [ arg, [ op(vars), x ], [ op(ws), [] ]];
    end proc;

    local do_extract := proc(arg, $)
      local sub, prod, svars, vs, ssum, ws, wc;
      if arg :: `*` then
        sub := map(do_extract, [op(arg)]);
        prod, svars := selectremove(x->op(2,x)=[],sub);
        if nops(svars) = 1 then
          [   op([1,1],svars)
            , op([1,2],svars)
            , applyop(w-> [op(w),op(map2(op,1,prod))], -1,
                      op([1,3],svars)) ];
        else
          [ arg, [], [[]] ];
        end if;
      elif arg :: `+` then
        sub := map(do_extract, [op(arg)]);
        svars := map2(op,2,sub);
        if the(map(nops,svars)) then
          vs[0] := map(sv->map2(op,1,sv), svars);      # a list of lists of variables
          vs[1] := map2(op,1, op(1,svars));            # a list of 'fresh' variables
          vs[2] := map(v->zip(`=`,v,vs[1]), vs[0]);    # variable renamings
          svars := zip(subs,vs[2], svars);             # dombounds renamed
          if the(svars) then
            ssum := zip(subs,vs[2],map2(op,1,sub));    # sub-arg summands
            ws   := zip(subs,vs[2],map2(op,3,sub));    # sub-arg weights
            # factor out common weight
            ws   := map(x->{op(map(op,x))}, ws);
            wc   := `intersect`(op(ws));
            ws   := [op(map(w -> w minus wc, ws))];
            ws   := map(`[]`@op, ws);
            wc   := [op(wc)];
            # non-common weights are pushed down
            ssum := zip(((s,w)->`*`(s,op(w))), ssum, ws);
            [ `+`(op(ssum)),
              op(1, svars),
              [ wc$(nops(op(1,svars))), [] ] ];
          else
            [ arg, [], [[]] ]
          end if;
        else
          [ arg, [], [[]] ]
        end if;
      elif Domain:-Has:-Bound(arg) then
        do_extract_arg(op(0,arg), [op(arg)]);
      else
        [ arg, [], [[]] ]
      end if;
    end proc;
  end module;

  # Extract a domain shape from an expression
  # This extracts the domain shape from individual multiplicands of
  # expressions, and multiplies the subexpressions back together.
  # essentially this assumes a distributive law (of domain shapes over
  # products)
  export Shape := module ()
    export ModuleApply := proc(e, kb:=KB:-empty) :: [ anything, anything ];
      local ixs, w, e1;
      ixs := [indices(ExtShape, 'nolist')];
      w, e1 := do_gets(ixs, true, e, kb) [];
      if not ('no_simpl' in {_rest}) then
        w := simpl_shape(w);
      end if;
      [ w, e1 ];
    end proc;

    local do_get := proc(f, f_ty, e, kb, $)
      local sub, inds, rest;
      if e::`*` then
        sub := map(x->do_get(f, f_ty,x,kb), [op(e)]);
        [ `And`(op(map2(op,1,sub))), `*`(op(map2(op,2,sub))) ]
      elif e::`^` then
        inds, rest := do_get(f, f_ty, op(1,e), kb) [] ;
        [ inds, subsop(1=rest, e) ]
      elif e:: f_ty then
        f(e,((z,kb1)->ModuleApply(z,kb1,'no_simpl')),kb)
      else
        [ true, e ]
      end if
    end proc;

    # apply a list of extractors, in order, until all fail to produce
    # any output .
    local do_gets := proc(todo::list, w, e, kb, $)
      local t0, ts, w1, e1;
      if nops(todo) = 0 then
        [ w, e ]
      else
        t0 := op(1, todo);
        ts := op(subsop(1=NULL, todo));
        w1, e1 := do_get(ExtShape[t0]:-MakeCtx
                         ,ExtShape[t0]:-MapleType
                         ,e,kb) [] ;
        ts := `if`(is(w1), [ts], [ts, t0]);
        do_gets( ts, bool_And(w1, w), e1, kb );
      end if;
    end proc;

    # todo: simplify the shape
    local simpl_shape := proc(e0,$)
      local e := simpl_relation(e0);
      e := subsindets(e, specfunc(`Or`) , x->DSum(op(x)));
      e := subsindets(e, specfunc(`And`), x->DConstrain(op(x)));
      e;
    end proc;
  end module;
end module;
