
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
    if do_domain and e :: 'And(specfunc({Ints,Sums}),
                   anyfunc(anything, name, range, list(name=range)))' then
      x, kb1 := genType(op(2,e),
                        mk_HArray(`if`(op(0,e)=Ints,
                                       HReal(open_bounds(op(3,e))),
                                       HInt(closed_bounds(op(3,e)))),
                                  op(4,e)),
                        kb);
      if nops(op(4,e)) > 0 then
        kb1 := assert(size(x)=op([4,-1,2,2],e)-op([4,-1,2,1],e)+1, kb1);
      end if;
      reduce_IntsSums(op(0,e), reduce(subs(op(2,e)=x, op(1,e)), h, kb1, opts), x,
        op(3,e), op(4,e), h, kb1, opts)
    elif e :: 'applyintegrand(anything, anything)' then
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

  reduce_Integrals_post := proc(kb,dom,mkDom,body)
    local vars, e, ed := mkDom(body);
    if ed = FAIL then
      vars := {op(Domain:-Bound:-varsOf(op(1,dom)))};
      e := reduce_on_prod(mkDom, e, vars, kb);
      kb_assuming_mb(x->subsindets(x, Partition, Partition:-Simpl))(e, kb, x->x);
    else
      ed
    end if
  end proc;

  # "Integrals" refers to any types of "integrals" understood by domain (Int,
  # Sum currently)
  reduce_Integrals := proc(expr, h, kb, opts, $)
    local rr;
    rr := Domain:-Fold(expr, kb
                ,proc() elim_intsum_Domain(h,args) end proc
                ,((x,kb1)->reduce(x,h,kb1,opts))
                # , proc(dom,mkDom,body) mkDom(body) end proc
                , proc() reduce_Integrals_post(kb,args) end proc
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
      e, w := selectremove(depends, list_of_mul(e), var);
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

  reduce_IntsSums := proc(makes, ee, var::name, rng, bds, h::name, kb::t_kb, opts, $)
    local e, elim;
    # TODO we should apply domain restrictions like reduce_IntSum does.
    e := makes(ee, var, rng, bds);
    elim := elim_intsum(e, h, kb);
    if elim = FAIL then e else reduce(elim, h, kb, opts) end if
  end proc;


  elim_intsum_Domain := proc(h, kind, e, vn, vt, kb, $)
    local ex, inert, e1;
    kernelopts(opaquemodules=false):

    inert := Domain:-Apply:-do_mk(args[2..-1]);
    ex := elim_intsum:-extract_elim(inert, h);
    e1 := elim_intsum:-apply_elim(h, kb, ex);
    if e1 = FAIL then
      inert
    else
      e1
    end if;
  end proc;


  # Try to find an eliminate (by evaluation, or simplification) integrals which
  # are free of `applyintegrand`s.
  elim_intsum := module ()
    export ModuleApply := proc(e, h :: name, kb :: t_kb, $)
      local todo, elim;
      todo := extract_elim(e,h,true);
      elim := apply_elim(h,kb,todo);
      check_elim(e, elim);
    end proc;

    local extract_elim := proc(e, h::name, toplevel :: truefalse := true, $)
      local t, var, mk_bnd, lo_bnd, hi_bnd, f, do_elim, mk_kb, todo0, body, todo;
      t := 'applyintegrand'('identical'(h), 'anything');
      if e :: Int(anything, name=anything) then
          var := op([2,1],e);
          mk_bnd := `<`;
          lo_bnd, hi_bnd := op(op([2,2],e));
        if not depends(indets(op(1,e), t), op([2,1],e)) then
          f := 'int_assuming';
        else
          f := proc(e,v) `Int`(e,v) end proc;
        end if;
      elif e :: Sum(anything, name=anything) then
        var := op([2,1],e);
        mk_bnd := `<=`;
        lo_bnd, hi_bnd := op(op([2,2],e));
        if not depends(indets(op(1,e), t), op([2,1],e)) then
          f := 'sum_assuming';
        else
          f := proc(e,v) `Sum`(e,v) end proc;
        end if;
      elif e :: Ints(anything, name, range, list(name=range)) then

        var := op(2,e);
        mk_bnd := `<`;
        lo_bnd, hi_bnd := op(op(3,e));

        if not depends(indets(op(1,e), t), op(2,e)) then
          f := 'ints';
        else
          f := `Ints`;
        end if;

      elif e :: Sums(anything, name, range, list(name=range)) then
        var := op(2,e);
        mk_bnd := `<=`;
        lo_bnd, hi_bnd := op(op(3,e));

        if not depends(indets(op(1,e), t), op(2,e)) then
          f := 'sums';
        else
          f := `Sums`;
        end if;
      else
        return `if`(toplevel, FAIL, [ e, [] ]);
      end if;

      do_elim := evalb(f in {'sums','ints','int_assuming','sum_assuming'});

      mk_kb := kb -> KB:-assert(And(mk_bnd(lo_bnd,var),mk_bnd(var,hi_bnd)), kb);

      todo0      := [ f, var, [op(2..-1,e)], mk_kb, do_elim ];
      body, todo := extract_elim(op(1,e), h, false)[];
      [ body, [ todo0, op(todo) ] ];
    end proc;

    local apply_elim := proc(h::name,kb::t_kb,todo::{list,identical(FAIL)})
      local body, todos, kbs, i, f, var, rrest, mk_kb, do_elim;
      if todo = FAIL or not(ormap(x->op(5,x),op(2,todo))) then
        return FAIL;
      end if;

      body, todos := op(todo); kbs[nops(todos)+1] := kb;

      for i from nops(todos) to 1 by -1 do
        f, var, rrest, mk_kb, do_elim := op(op(i,todos));
        kbs[i] := mk_kb(kbs[i+1]);

        if do_elim then
          body := banish(body, h, kbs[i], infinity, var,
                         proc (kb,g,$) do_elim_intsum(kb, f, g, op(rrest)) end proc);
        else
          body := f(body, op(rrest));
        end if;
      end do;

      body;
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
