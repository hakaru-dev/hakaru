
# Step 2 of 3: computer algebra

  improve := proc(lo :: LO(name, anything), {_ctx :: t_kb := empty}, $)
  local r, `&context`;
       userinfo(5, improve, "input: ", print(lo &context _ctx));
       r:= LO(op(1,lo), reduce(op(2,lo), op(1,lo), _ctx));
       userinfo(5, improve, "output: ", print(r));
       r
  end proc;

  # Walk through integrals and simplify, recursing through grammar
  # h - name of the linear operator above us
  # kb - domain information
  reduce := proc(ee, h :: name, kb :: t_kb, $)
    local e, elim, subintegral, w, ww, x, c, kb1, dom_specw, dom_specb
         , body, dom_spec, ed;
    e := ee;

    if Domain:-Has(e) then
        # First extract only the bounds, then simplify the body
        # This may discover other nested domains, simplify them,
        # and allow a further simplification to occur in this
        # step of domain improvement
        body, dom_specb := Domain:-Extract:-Bound(e, kb);
        kb1 := Domain:-ToKB:-Bound(dom_spec1);

        userinfo(3, 'disint_trace',
                 printf("domain extract:\n"
                        "  body : %a\n"
                        "  vars : %a\n"
                        "  kb   : %a\n\n"
                        , body, vars, kb1 ));

        e := reduce(body, h, kb1);

        # Extract the shape of the domain
        (dom_specw, e) := Domain:-Extract:-Shape(e);

        # Construct the domain from the bounds and the shape
        dom_spec := Domain:-DOMAIN(dom_specb, dom_specw);

        # Improve the domain
        dom_spec := Domain:-Improve(dom_spec);

        # Apply the domain back to the expression
        ed := Domain:-Apply(dom_spec, e, kb);

        # Some extra simplification may be needed
        elim := elim_intsum( ed, h, kb );

        if elim = FAIL then
            e := reduce_on_prod( mkDom, e, map(x->op(1,x), vars), kb);
            # simplify(e);
            # `simplify/PARTITION`(e) assuming (op(kb_to_assumptions(kb))) ;
            kb_assuming_mb(`simplify/PARTITION`)(e, kb, x->x);

        else
            reduce(elim, h, kb);
        end if;

    elif e :: 'And(specfunc({Ints,Sums}),
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
      reduce_IntsSums(op(0,e), reduce(subs(op(2,e)=x, op(1,e)), h, kb1), x,
        op(3,e), op(4,e), h, kb1)
    elif e :: 'applyintegrand(anything, anything)' then
      map(simplify_assuming, e, kb)
    elif e :: `+` then
      map(reduce, e, h, kb)
    elif e :: `*` then
      (subintegral, w) := selectremove(depends, e, h);
      if subintegral :: `*` then error "Nonlinear integral %1", e end if;
      subintegral := convert(reduce(subintegral, h, kb), 'list', `*`);
      (subintegral, ww) := selectremove(depends, subintegral, h);
      reduce_pw(simplify_factor_assuming(`*`(w, op(ww)), kb))
        * `*`(op(subintegral));
    elif e :: t_pw then
      e:= flatten_piecewise(e);
      e := kb_piecewise(e, kb, simplify_assuming,
                        ((rhs, kb) -> %reduce(rhs, h, kb)));
      e := eval(e, %reduce=reduce);
      # big hammer: simplify knows about bound variables, amongst many
      # other things
      Testzero := x -> evalb(simplify(x) = 0);
      e := reduce_pw(e);
      e;
    elif e :: t_case then
      subsop(2=map(proc(b :: Branch(anything, anything))
                     eval(subsop(2='reduce'(op(2,b),x,c),b),
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
      applyop(reduce, 2, e, h, kb1);
    elif e :: 'integrate(anything, Integrand(name, anything), list)' then
      x := gensym(op([2,1],e));
      # If we had HType information for op(1,e),
      # then we could use it to tell kb about x.
      subsop(2=Integrand(x, reduce(subs(op([2,1],e)=x, op([2,2],e)), h, kb)), e)
    else
      simplify_assuming(e, kb)
    end if;
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
      reduce_pw(simplify_factor_assuming(`*`(op(w)), kb0)) * f(`*`(op(e))) ;
  end proc;

  int_assuming := proc(e, v::name=anything, kb::t_kb, $)
    simplify_factor_assuming('int'(e, v), kb);
  end proc;

  sum_assuming := proc(e, v::name=anything, kb::t_kb)
    simplify_factor_assuming('sum'(e, v), kb);
  end proc;

  reduce_pw := proc(ee, $) # ee may or may not be piecewise
    local e;
    e := nub_piecewise(ee);
    if e :: t_pw then
      if nops(e) = 2 then
        return Indicator(op(1,e)) * op(2,e)
      elif nops(e) = 3 and Testzero(op(2,e)) then
        return Indicator(Not(op(1,e))) * op(3,e)
      elif nops(e) = 3 and Testzero(op(3,e)) then
        return Indicator(op(1,e))*op(2,e)
      elif nops(e) = 4 and Testzero(op(2,e)) then
        return Indicator(And(Not(op(1,e)),op(3,e))) * op(4,e)
      end if
    end if;
    return e
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

  reduce_IntsSums := proc(makes, ee, var::name, rng, bds, h::name, kb::t_kb, $)
    local e, elim;
    # TODO we should apply domain restrictions like reduce_IntSum does.
    e := makes(ee, var, rng, bds);
    elim := elim_intsum(e, h, kb);
    if elim = FAIL then e else reduce(elim, h, kb) end if
  end proc;

  elim_intsum := module ()
    export ModuleApply := proc(e, h :: name, kb :: t_kb, $)
      local t, var, f, elim;
      t := 'applyintegrand'('identical'(h), 'anything');
      if e :: Int(anything, name=anything) and
         not depends(indets(op(1,e), t), op([2,1],e)) then
        var := op([2,1],e);
        f := 'int_assuming';
      elif e :: Sum(anything, name=anything) and
         not depends(indets(op(1,e), t), op([2,1],e)) then
        var := op([2,1],e);
        f := 'sum_assuming';
      elif e :: Ints(anything, name, range, list(name=range)) and
           not depends(indets(op(1,e), t), op(2,e)) then
        var := op(2,e);
        f := 'ints';
      elif e :: Sums(anything, name, range, list(name=range)) and
           not depends(indets(op(1,e), t), op(2,e)) then
        var := op(2,e);
        f := 'sums';
      else
        return FAIL;
      end if;
      # try to eliminate unused var
      elim := banish(op(1,e), h, kb, infinity, var,
        proc (kb,g,$) do_elim_intsum(kb, f, g, op(2..-1,e)) end proc);
      if has(elim, {MeijerG, undefined, FAIL}) or e = elim or elim :: SymbolicInfinity then
        return FAIL;
      end if;
      elim
    end proc;

    local do_elim_intsum := proc(kb, f, ee, v::{name,name=anything})
      local w, e, x, g, t, r;
      w, e := getDomainSpec(ee);
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
