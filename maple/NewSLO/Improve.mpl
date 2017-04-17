
# Step 2 of 3: computer algebra

  improve := proc(lo :: LO(name, anything), {_ctx :: t_kb := empty}, opts := [], $)
  local r, `&context`;
       userinfo(5, improve, "input: ", print(lo &context _ctx));
       r:= LO(op(1,lo), reduce(op(2,lo), op(1,lo), _ctx, opts));
       userinfo(5, improve, "output: ", print(r));
       r
  end proc;

  # Walk through integrals and simplify, recursing through grammar
  # h - name of the linear operator above us
  # kb - domain information
  reduce := proc(ee, h :: name, kb :: t_kb, opts := [], $)
    local e, elim, subintegral, w, ww, x, c, kb1, with_kb1, dom_specw, dom_specb
         , body, dom_spec, ed, mkDom, vars, rr
         , do_domain := evalb( not ( ['no', 'domain'] in {op(opts)} ) ) ;
    e := ee;

    if do_domain then
      rr := reduce_Integrals(e, h, kb, opts);
      if rr <> FAIL then return rr end if;
    end if;
    if e :: 'applyintegrand(anything, anything)' then
      map(simplify_assuming, e, kb)
    elif e :: `+` then
      map(reduce, e, h, kb, opts)
    elif e :: `*` then
      (subintegral, w) := selectremove(depends, e, h);
      if subintegral :: `*` then error "Nonlinear integral %1", e end if;
      subintegral := convert(reduce(subintegral, h, kb, opts), 'list', `*`);
      (subintegral, ww) := selectremove(depends, subintegral, h);
      nub_piecewise(simplify_factor_assuming(`*`(w, op(ww)), kb))
        * `*`(op(subintegral));
    elif e :: Or(Partition,t_pw) then
      if e :: t_pw then e := PWToPartition(e); end if;
      e := Partition:-Flatten(e);
      e := kb_Partition(e, kb, simplify_assuming,
                        ((rhs, kb) -> %reduce(rhs, h, kb, opts)));
      e := eval(e, %reduce=reduce);
      # big hammer: simplify knows about bound variables, amongst many
      # other things
      Testzero := x -> evalb(simplify(x) = 0);
      e := PartitionToPW(e);
      nub_piecewise(e);
    elif e :: t_case then
      subsop(2=map(proc(b :: Branch(anything, anything))
                     eval(subsop(2='reduce'(op(2,b),x,c,opts),b),
                          {x=h, c=kb})
                   end proc,
                   op(2,e)),
             e);
    elif e :: 'Context(anything, anything)' then
      kb1 := assert(op(1,e), kb);
      # A contradictory `Context' implies anything, so produce 'anything'
      # In particular, 42 :: t_Hakaru = false, so a term under a false
      # assumption should never be inspected in any way.
      if kb1 :: t_not_a_kb then
          return 42
      end if;
      applyop(reduce, 2, e, h, kb1, opts);
    elif e :: 'toLO:-integrate(anything, Integrand(name, anything), list)' then
      x := gensym(op([2,1],e));
      # If we had HType information for op(1,e),
      # then we could use it to tell kb about x.
      subsop(2=Integrand(x, reduce(subs(op([2,1],e)=x, op([2,2],e)), h, kb, opts)), e)
    else
      simplify_assuming(e, kb)
    end if;
  end proc;

  reduce_Integrals_post := proc(h,kb,opts,dvars,mkDom,body)
    local vars, e
      , ed := mkDom(body)
      , ee := subsindets(ed, specfunc(ELIMED), x->op(1,x));

    if ed = ee then
      vars := indets(Domain:-Bound:-varsOf(dvars), name);
      ed := reduce_on_prod(mkDom, body, vars, kb);
      kb_assuming_mb(x->subsindets(x, Partition, Partition:-Simpl))(ed, kb, x->x);
    else
      reduce(ee,h,kb,opts);
    end if
  end proc;

  # "Integrals" refers to any types of "integrals" understood by domain (Int,
  # Sum currently)
  reduce_Integrals := proc(expr, h, kb, opts, $)
    local rr;
    rr := Domain:-Fold(expr, kb
      ,proc() elim_intsum:-for_Domain(h,args) end proc
      ,((x,kb1)->reduce(x,h,kb1,opts))
      , proc() reduce_Integrals_post(h,kb,opts,args) end proc
      ,(_->:-DOM_FAIL));

    if has(rr, :-DOM_FAIL) then
      return FAIL;
    elif has(rr, FAIL) then
      error "Something strange happened in reduce_Integral(%a, %a, %a, %a)\n%a"
          , expr, kb, kb, opts, rr;
    else
      return rr;
    end if
  end proc;

  # Helper function for performing reductions
  # given an "ee" and a "var", pulls the portion
  # of "ee" not depending on "var" out, and applies "f"
  # to the portion depending on "var".
  # the 'weights' (factors not depending on "var") are simplified
  # under the given assumption context, "kb0"
  reduce_on_prod := proc(f,ee, var:: {name, list(name), set(name)} ,kb0::t_kb,$)
      local e := ee, w;
      e, w := selectremove(x->depends(x,var) or x :: realcons, list_of_mul(e));
      nub_piecewise(simplify_factor_assuming(`*`(op(w)), kb0)) * f(`*`(op(e))) ;
  end proc;

  int_assuming := proc(e, v::name=anything, kb::t_kb, $)
    simplify_factor_assuming('int'(e, v), kb);
  end proc;

  sum_assuming := proc(e, v::name=anything, kb::t_kb)
    simplify_factor_assuming('sum'(e, v), kb);
  end proc;

  nub_piecewise := proc(pw, $) # pw may or may not be piecewise
    foldr_piecewise(piecewise_if, 0, pw)
  end proc;

  piecewise_if := proc(cond, th, el, $)
    # piecewise_if should be equivalent to `if`, but it produces
    # 'piecewise' and optimizes for when the 3rd argument is 'piecewise'
    if cond = true then
      th
    elif cond = false or Testzero(th - el) then
      el
    elif el :: t_pw then
      if nops(el) >= 2 and Testzero(th - op(2,el)) then
        applyop(Or, 1, el, cond)
      else
        piecewise(cond, th, op(el))
      end if
    elif Testzero(el) then
      piecewise(cond, th)
    else
      piecewise(cond, th, el)
    end if
  end proc;

  # Int( .., var=var_ty ) == var &X var_ty
  isBound_IntSum := kind -> module()
    option record;

    export MakeKB := (`if`(kind=Sum,KB:-genSummation,KB:-genLebesgue));
    export ExtractVar := (e->op(1,e));
    export ExtractRange := (e->op(2,e));
    export MakeRange := `..`;
    export SplitRange := (e->op(e));
    export Constrain := `if`(kind=Sum,`<=`,`<`);
    export DoMk := ((e,v,t)->kind(e,v=t));
    export EvalInCtx    := `if`(kind=Sum,'sum_assuming','int_assuming');
    export Min := `min`; export Max := `max`;
    export VarType := 'name';
    export RangeType := 'range';
    export MapleType := 'And'('specfunc'(kind), 'anyfunc(anything,name=range)');
    export BoundType := `if`(kind=Sum,'integer','real');
  end module;

  # Ints( .., var::name, var_ty::range, dims::list(name=range) ) ==
  #        [ var   , map(lhs,dims) ] :: list(name)  &X
  #        [ var_ty, map(rhs,dims) ] :: list(range)
  isBound_IntsSums := kind -> module()
    option record;

    export MakeKB := proc(vars, lo, hi, kb, $)
      local var, dims, ty, rngs, x, kb1;
      var  := op(1, vars);
      rngs := zip(`..`,lo,hi);
      ty   := op(1, rngs);
      dims := subsop(1=NULL,zip(`=`,vars,rngs));

      x, kb1 := genType(var,
                        mk_HArray(`if`(kind=Ints,
                                       HReal(open_bounds(ty)),
                                       HInt(closed_bounds(ty))),
                                  dims),kb);
      if nops(dims) > 0 then
        kb1 := assert(size(x)=op([-1,2,2],dims)-op([-1,2,1],dims)+1, kb1);
      end if;
      x, kb1;
    end proc;
    export ExtractVar   := ((v,t,d)->[v,map(lhs,d)[]]);
    export ExtractRange := ((v,t,d)->[t,map(rhs,d)[]]);
    export MakeRange    := ((a,b)->zip(`..`,a,b));
    export SplitRange   := (rs->(map(x->op(1,x),rs), map(x->op(2,x),rs)));
    export Constrain    := ((a,b)->zip(`if`(kind=Ints, `<`, `<=`)),a,b);
    export DoMk         := ((e,v,t)->kind( e,op(1,v),op(1,t), subsop(1=NULL,zip(`=`,v,t)) ));
    export EvalInCtx    := `if`(kind=Ints,'ints','sums');
    export Min          := ((a,b)->zip(`min`,a,b));
    export Max          := ((a,b)->zip(`max`,a,b));
    export VarType      := 'And(list(name),satisfies(x->x<>[]))';
    export RangeType    := 'And(list(range),satisfies(x->x<>[]))';
    export MapleType    := 'And'('specfunc'(kind),'anyfunc'('anything', 'name', 'range', 'list(name=range)'));
    export BoundType    := TopProp;
  end module;

  # Try to find an eliminate (by evaluation, or simplification) integrals which
  # are free of `applyintegrand`s.
  elim_intsum := module ()
    export ModuleApply := proc(inert0, h :: name, kb :: t_kb, $)
       local ex, un_elim, e1, inert := inert0, done_e := false;

       un_elim := subsindets(inert, specfunc('ELIMED'), x->op(1,x));
       if un_elim <> inert then
         inert := un_elim; done_e := true;
       end if;

       ex := extract_elim(inert, h);
       e1 := apply_elim(h, kb, ex);
       e1 := check_elim(inert, e1);
       if e1 = FAIL then
         `if`(done_e,ELIMED,_->_)(inert)
       else
         ELIMED(e1)
       end if
    end proc;

    export for_Domain := proc(h, kind, e, vn, vt, kb, $)
       ModuleApply(Domain:-Apply:-do_mk(args[2..-1]), h, kb);
    end proc;

    local extract_elim := proc(e, h::name, $)
      local t, intapps, var, f, e_k, e_args;
      t := 'applyintegrand'('identical'(h), 'anything');
      intapps := indets(op(1,e), t);
      if intapps = {} then
        return FAIL;
      end if;
      e_k := op(0,e); e_args := op([2..-1],e);

      if Domain:-Has:-Bound(e) then
        var := Domain:-ExtBound[e_k]:-ExtractVar(e_args);
        ASSERT(var::DomBoundVar);
        if var :: list then var := op(1,var) end if;

        if not depends(intapps, var) then
          f := Domain:-ExtBound[e_k]:-EvalInCtx;
        else
          return FAIL;
        end if;
      end if;

      [ op(1,e), f, var, [e_args] ];
    end proc;

    local apply_elim := proc(h::name,kb::t_kb,todo::{list,identical(FAIL)})
      local body, f, var, rrest;
      if todo = FAIL then return FAIL; end if;
      body, f, var, rrest := op(todo);
      banish(body, h, kb, infinity, var,
             proc (kb1,g,$) do_elim_intsum(kb1, f, g, op(rrest)) end proc);
    end proc;

    local check_elim := proc(e, elim,$)
      if has(elim, {MeijerG, undefined, FAIL}) or e = elim or elim :: SymbolicInfinity then
        return FAIL;
      end if;
      return elim;
    end proc;

    local do_elim_intsum := proc(kb, f, ee, v::{name,name=anything})
      local w, e, x, g, t, r;
      w, e := op(Domain:-Extract:-Shape(ee));
      w := Domain:-Shape:-toConstraints(w);
      e := piecewise_And(w, e, 0);
      e := f(e,v,_rest,kb);
      x := `if`(v::name, v, lhs(v));
      g := '{sum, sum_assuming, sums}';
      if f in g then
        t := {'identical'(x),
              'identical'(x) = 'Not(range(Not({SymbolicInfinity, undefined})))'};
      else
        g := '{int, int_assuming, ints}';
        t := {'identical'(x),
              'identical'(x) = 'anything'};
        if not f in g then g := {f} end if;
      end if;
      for r in indets(e, 'specfunc'(g)) do
        if 1<nops(r) and op(2,r)::t then return FAIL end if
      end do;
      e
    end proc;

  end module;
