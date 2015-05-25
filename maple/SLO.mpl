# SLO = Simplify Linear Operator.
#
#  This assumes that the input is the output of Language.Hakaru.Syntax.tester
# No checking is done that this is actually the case.
#
# SLO : simplifier
# AST : takes simplified form and transform to AST
#

SLO := module ()
  export ModuleApply, AST, simp, flip_cond, condToProp,
    c; # very important: c is "global".
  local ToAST, t_binds, t_pw, t_rel,
    into_pw, myprod, do_pw, do_pw_weight, 
    mkProb, getCtx, instantiate, lambda_wrap, find_paths,
    mkReal,
    fill_table, toProp, toType,
    twiddle, myint, myint_pw,
    fix_Heaviside,
    adjust_types, compute_domain, analyze_cond, isPos,
    adjust_superpose,
    get_breakcond, merge_pw,
    MyHandler, getBinderForm, infer_type, join_type, join2type,
    infer_type_prod, infer_type_sop, check_sop_type,
    simp_sup, simp_if, into_sup, simp_rel,
    simp_pw, simp_pw_equal, simp_pw3, simp_Or,
    simp_props, simp_mono, on_rels, flip_rel,
    try_assume,
    comp2, comp_algeb, compare, comp_list,
    DomainOfDef,

    # density recognisation routines
    get_de, mkRealDensity, recognize_density, recognize_density_01,
    recognize_density_0inf, density;

  t_binds := 'specfunc(anything, {int, Int, sum, Sum})';
  t_pw := 'specfunc(anything, piecewise)';
  t_rel := {`<`,`<=`,`=`,`<>`};

  # SLO output goes into AST
  ModuleApply := proc(spec::Typed(anything,anything))
    local expr, typ, glob, gsiz, ctx, r, inp, meastyp, res, gnumbering;
    expr := op(1, spec);
    typ := op(2, spec);
    glob, gnumbering, gsiz, meastyp := getCtx(typ, {}, table(), 0);
    r := Record('htyp' = typ, 'mtyp' = meastyp,
                'gctx' = glob, 'gnum' = gnumbering, 'gsize' = gsiz);
    inp := instantiate(expr, r, 0, typ);

    # global option
    _EnvUseHeavisideAsUnitStep := true;
    try
      # be context sensitive for this pass too:
      _EnvBinders := {};
      _EnvPathCond := `union`(op(map(toProp, glob)));
      NumericEventHandler(division_by_zero = MyHandler);
      # simp first applied so piecewise is effective,
      # then again in case eval "undoes" work of first simp call
      res := inp(c);
      res := eval(res, 'if_'=piecewise);
      res := simp(res);
      res := eval(res, Int=myint);
      res := HAST(simp(res), r);
    catch "Wrong kind of parameters in piecewise":
      error "Bug in Hakaru -> Maple translation, piecewise used incorrectly.";
    finally :
      NumericEventHandler(division_by_zero = default);
    end try;
    res;
  end proc;

  # AST transforms the Maple to a representation of the mochastic AST
  # environment variables plus indexing functions make tracking info easy!
  AST := proc(inp::HAST(anything, Context))
    local res, ctx, t, i, rng;

    ctx := op(2,inp); # htyp, mtyp, gctx, gnum, gsize

    # global option
    _EnvUseHeavisideAsUnitStep := true;

    # right at the start, put the global context in scope.
    _EnvBinders := map2(op, 1, ctx:-gctx);
    _EnvTypes := `union`(op(map(toType, ctx:-gctx)));
    _EnvPathCond := `union`(op(map(toProp, ctx:-gctx)));
    res := ToAST(op(inp));
    res := adjust_types(res, ctx:-mtyp, ctx);
    res := adjust_superpose(res);
    lambda_wrap(res, 0, ctx);
  end proc;

  # recursive function which does the main translation
  ToAST := proc(inp, ctx)
    local a0, a1, var, vars, rng, ee, cof, d, ld, weight, binders,
      v, subst, inv_subst, ivars, ff, newvar, rest, a, b, e,
      inv_map;
    e := inp; # make e mutable
    if type(e, specfunc(name, c)) then
      return Return(op(e))
    # we might have recursively encountered a hidden 0
    elif (e = 0) then
      return Superpose()
    elif (e = infinity) then # yep, that's a measure!
      return WeightedM(infinity, Superpose())
    # we might have done something odd, and there is no x anymore (and not 0)
    elif type(e, 'numeric') then
      error "the constant %1 is not a measure", e
    # invariant: we depend on c
    else
      binders := indets(e, t_binds);
      if binders = {} then
        # this is a 'raw' measure, with no integrals
        vars := indets(e, specfunc(anything, c));
        subst := map(x-> x = gensym(`cc_`), vars);
        inv_map := zz -> op(eval(op(1,zz), 
            piecewise=(proc() do_pw_weight([args]) end)));
        inv_subst := map(z -> op(2,z) = inv_map(z), subst);
        ivars := map2(op, 2, subst);
        ee := subs(subst, e);
        if type(ee, 'polynom'(anything,ivars)) then
          ee := collect(ee, ivars, 'distributed', simplify);
          d := degree(ee, ivars);
          ld := ldegree(ee, ivars);
          cof := [coeffs(ee, ivars, 'v')]; # cof is a list, v expseq
          if (d = 1) and (ld = 1) then
            ff := (x,y) -> WeightedM(simplify(x), Return(subs(inv_subst, y)));
            Superpose(op(zip(ff, cof, [v])));
          elif (ee=0) then # collect/simplify could have revealed this
            Superpose()
          elif (ld = 0) then
            error "non-zero constant (%1) encountered as a measure", ee
          else
            error "polynomial in c: %1", ee
          end if;
        elif type(ee, t_pw) then
          return do_pw(map(simplify, [op(e)]), ctx);
        elif type(ee, `+`) then
          Superpose(op(map(ToAST, [op(e)], ctx)));
        else
          error "(%1) has no binders, but is still not a polynomial?", ee
        end if;
      else
        if type(e, 'specfunc'(anything, {'int','Int'})) then
          var, rng := op(op(2,e));
          ee := op(1,e);
          weight := simplify(op(2,rng)-op(1,rng));
          if type(weight, 'SymbolicInfinity') then
            rest := ToAST(ee, ctx);
            mkRealDensity(rest, var, rng)
          else
            # span := RealRange(op(1,rng), op(2,rng));
            v := simplify(weight*ee) assuming AndProp(op(1,rng)<var, var<op(2,rng));
            rest := ToAST(v, ctx);
            # Bind(Uniform(op(rng)), var, rest);
            mkRealDensity(rest, var, rng)
          end if;
        elif type(e, 'specfunc'(anything, {'sum','Sum'})) then
          var, rng := op(op(2,e));
          ee := op(1,e);
          weight := simplify(op(2,rng)-op(1,rng));
          if type(weight, 'SymbolicInfinity') then
            rest := ToAST(ee, ctx);
            Bind(Counting, var = rng, rest)
          else
            # span := RealRange(op(1,rng), op(2,rng));
            v := simplify(weight*ee) assuming AndProp(op(1,rng)<var, var<op(2,rng));
            rest := ToAST(v, ctx);
            Bind(Counting, var = rng, rest)
          end if;
        elif type(e, t_pw) then
          return do_pw([op(e)], ctx);
        elif type(e, `+`) then
          Superpose(op(map(ToAST, [op(e)], ctx)));
        elif type(e, `*`) then
          # we have a binder in here somewhere
          a, b := selectremove(type, e, t_binds);
          # now casesplit on what a is
## from here
          if a=1 then  # no surface binders
            a, b := selectremove(type, e, t_pw);
            if a=1 then # and no piecewise either
              error "buried binder: %1", b
            elif type(a, `*`) then
              error "do not know how to multiply 2 pw: %1", a
            elif type(a, t_pw) then
              WeightedM(b, ToAST(a, ctx))
            else
              error "something weird happened: (%1) was supposed to be pw", a
            end if
          elif type(a, `*`) then
            error "product of 2 binders?!?: %1", a
          else
            WeightedM(b, ToAST(a, ctx))
          end if
## to here
        else
          error "Not sure what to do with %1", e
        end if;
      end if;
    end if;
  end proc;

  simp := proc(e)
    option remember, system;
    local binds, pw, substb, substp, subst, csubst, vbinds, vpw,
      ee, zz, vars, all_vars, num, den, push_in, i,
      cs, simp_poly, simp_prod, simp_npw;

    simp_npw := zz -> `if`(op(1,zz)::t_pw, into_pw(SLO:-c,op(1,zz)), zz);
    if e=undefined or e::numeric or e::SymbolicInfinity then return e end if;
    cs := indets(e, specfunc(anything, c));
    csubst := map(x -> x = simp_npw(map(simp, value(x))), cs);
    ee := eval(e, csubst);
    if not type(csubst, set(specfunc(anything, c) = specfunc(anything,c))) then
      return simp(ee)
    end if;

    binds := indets(ee, t_binds);
    pw := indets(ee, t_pw);

    substb := map(x-> x = freeze(x), binds);
    substp := map(x-> x = freeze(x), pw);
    subst := substb union substp;
    ee := subs(subst union csubst, ee); # simultaneous substitution
    vbinds := map(rhs, substb);
    vpw := map(rhs, substp);
    vars := [op(vbinds union vpw)]; # order does not matter; only subst
    all_vars := [op(vars),op(convert(cs,list))];

    push_in := proc(c, v)
      local actual, cof, ii, rest, res, var, dom;
      cof := c;
      if v=1 then return cof end if;
      actual := thaw(v);
      if type(actual, t_binds) then
        var := op([2,1], actual);
        _EnvBinders := _EnvBinders union {var};
        dom := op([2,2], actual);
        if dom::(extended_numeric..extended_numeric) then
          dom := DomainOfDef(op(1,actual), var, dom);
          _EnvPathCond := _EnvPathCond union {var :: RealRange(op(dom))};
        end if;
        op(0,actual)(simp(cof*op(1,actual)), var = dom);
      elif type(actual, t_pw) then
        `if`(actual::t_pw, into_pw((x -> cof * x), actual), cof*actual);
      elif degree(v, vars)>1 then
        if type(actual, '`*`'(t_pw)) then
          res := merge_pw([op(actual)], mul);
          `if`(res::t_pw, into_pw((x->cof*x), res), cof*res);
        else
          (ii, rest) := selectremove(type, actual, t_binds);
          if ii::`*` then error "product? (%1)", ii; end if;
          simp(subsop(1=op(1,ii)*rest, ii));
        end if;
      else
        error "how can (%1) not be a binder, pw or c?", v
      end if;
    end proc;

    simp_poly := proc(p)
      local coef_q, vars_q, q, c0, res, heads;
      q := collect(p, all_vars , 'distributed', simplify);
      if not type(q, polynom(anything, vars)) then 
        q := thaw(q);
        if q::`*` then
          return map(simp, q)
        elif q::`+` then
          return map(simp, q)
        else
          error "(%1) in simp_poly", q;
        end if;
      end if;
      if ldegree(q, vars)<1 then
        # need to 'push in' additive constant sometimes
        c0 := tcoeff(q, vars);
        q := q - c0; # this should work because of the collect
      else
        c0 := 0;
      end if;
      if q = undefined then return undefined end if;
      if q=0 then return c0; end if;
      coef_q := [coeffs(q, vars, 'vars_q')];
      vars_q := [vars_q];
      # need to merge things too
      res := add(i,i=zip(push_in, coef_q, vars_q));
      if nops(coef_q) > 1 then
        heads := map2(op, 0, {op(res)}); # res::`+`
        if heads = {piecewise} then
          res := merge_pw([op(res)], add);
        end if;
        c0+res
      elif not (c0 = 0) then
        # don't push additive constants into (usually infinite!) integrals
        if type(res, t_binds) then
          c0+res;
        elif type(res, t_pw) then
          into_pw((x -> c0 + x), res)
        else
          error "Expected a pw or binder, got (%1)", res
        end if;
      else # c0 = 0
        res;
      end if;

    end proc;

    simp_prod := proc(p)
      local den, num;
      den, num := selectremove(type, p, anything ^ negint);
      den := 1/den;
      if degree(den, all_vars)>=1 then
        num := simp_poly(num);
        den := simp_poly(den);
        if den::t_pw then
          den := into_pw((x -> 1/x), den);
          simp(num*den); # this should not loop!
        else
          num/den; # integrals in denominator
        end if;
      else
        num := num / den; # no need to make this fancy
        simp_poly(num);
      end if;

    end proc;

    # keep some of the structure intact
    if type(ee, `*`) then
      ee := simp_prod(ee);
    elif type(ee, polynom(anything, vars)) then
      ee := simp_poly(ee);
    elif type(ee, ratpoly(anything, vars)) then
      ee := normal(ee);
      if type(ee, `*`) then
        ee := simp_prod(ee);
      else
        ee := simp_poly(numer(ee))/simp_poly(denom(ee));
      end if;
    elif type(ee, 'Pair'(anything, anything)) then
      ee := map(x -> simp(thaw(x)), ee);
      # this is weird, looks like it might not deal with pw in 2nd 
      # part without recursing TODO
      if op(1,ee)::t_pw then
        ee := into_pw((x -> Pair(x, op(2,ee))), op(1,ee))
      elif op(2,ee)::t_pw then
        ee := into_pw((x -> Pair(op(1,ee), x)), op(2,ee))
      end if;
    elif type(ee, anyfunc(anything)) then
      ee := op(0,ee)(simp(thaw(op(1,ee))));
      if type(op(1,ee), t_pw) then
        ee := into_pw(op(0,ee), op(1,ee))
      end if;
    elif type(ee,`+`) then
      ee := map(simp, thaw(ee))
    elif type(ee, anything^(fraction)) then
      zz := simp(thaw(op(1,ee)));
      if type(zz, t_pw) then
        ee := into_pw((x -> x^op(2,ee)), zz);
      else
        ee := zz^op(2,ee);
      end if
    else
      error "(%1) involves unknown functions", ee;
    end if;

    ee;
  end proc;

  into_pw := proc(g, pw)
    local n, f;

    n := nops(pw);
    f := proc(j)
      if j=n then # last one is special, always a value
        simp(g(simp(op(j, pw))))
      elif type(j,'odd') then # a condition
        simp_rel( op(j, pw) )
      else # j even
        simp(g(simp(op(j, pw))))
      end if;
    end proc;
    simp_pw(piecewise(seq(f(i),i=1..n)))
  end proc;

  # myprod takes care of pushing a product inside a `+`
  myprod := proc(a, b)
    if type(b,`+`) then
      map2(myprod, a, b)
    else
      simp(a*b)
    end if;
  end proc;

  # a hack to make equations symmetric.  Session-dependent, but that's fine.
  twiddle := proc(x)
    local l;
    if type(x,`=`) then
      if rhs(x) = 0 then
        try
          if lhs(x)::`+` and nops(lhs(x))=2 then
            l := lhs(x);
            # Heuristic, as l may not be polynomial
            if sign(op(1,l))=-1 then
              twiddle(op(2,l) = -op(1,l))
            elif sign(op(2,l)) = -1 then
              twiddle(op(1,l) = -op(2,l))
            elif addressof(op(1,l)) > addressof(op(2,l)) then
              twiddle(op(2,l) = -op(1,l))
            else
              twiddle(op(1,l) = -op(2,l))
            end if;
          else
            x
          end if;
        catch:
          x
        end try;
      elif addressof(lhs(x)) > addressof(rhs(x)) then
        rhs(x) = lhs(x)
      else
        x
      end if;
    elif type(x,'list') then
      map(twiddle, x)
    else
      x
    end if;
  end proc;

  fix_Heaviside := proc(e, ee)
    try
      frontend(convert, [e], [{`+`,`*`}, '{Heaviside, Dirac}'], 'piecewise');
    catch "give the main variable as a second argument":
      ee
    end try;
  end proc;

  merge_pw := proc(l::list, f)
    local breakpoints, sbp, i, n, res, npw;

    breakpoints := convert(map(get_breakcond, l), 'set');
    sbp := map(twiddle, breakpoints);
    n := nops(l[1]);
    if nops(sbp)=1 then
      res := simp_pw(piecewise(seq(`if`(i::odd and i<n,
                                   op(i,l[1]),
                                   f(op(i,j),j=l)), i=1..n)));
      simp(res);
    else
      #error "multiple piecewises with different breakpoints %1", l
      # try with Heaviside
      res := f(i,i=l);
      try
        npw := simplify(convert(res, 'Heaviside'));
        npw := fix_Heaviside(npw, res);
      catch "give the main variable as a second argument":
        npw := res;
      end try;
      npw
    end if;
  end proc;

  get_breakcond := proc(pw::specfunc(anything, piecewise))
    local i, n;
    n := nops(pw);
    [seq(`if`(i::odd and i<n, op(i,pw), NULL), i=1..n)]
  end proc;

  simp_rel := proc(r)
    local res;
    if r::name then
      r
    elif r::t_rel then
      # special case
      if r = ('Right' = 'Left') then
        false
      elif lhs(r) = undefined or rhs(r) = undefined then
        false
      else
        res := is(r) assuming op(_EnvPathCond);
        if res = true then return true end if;
        res := coulditbe(r) assuming op(_EnvPathCond);
        if res = false then return false end if;
        map(simp, r); # let map take care of which operator it is
      end if;
    elif r::specfunc(anything, {And, Or, Not}) then
      map(simp_rel, r)
    else
      simp(r)
    end;
  end proc;

  simp_Or := proc(a,b)
    if type(a, anything = anything) and type(b, anything < anything)
      and op(1,a) = op(1,b) and op(2,a) = op(2, b) then
      op(1,a) <= op(2,a)
    elif type(b, anything = anything) and type(a, anything < anything)
      and op(1,a) = op(1,b) and op(2,a) = op(2, b) then
      op(1,a) <= op(2,a)
    else
      Or(a,b)
    end if;
  end proc;

  # takes the = conditions and applies & simplifies them
  simp_pw_equal := proc(pw)
    local n, rest, aa, f;
    n := floor(nops(pw)/2);
    rest := evalb(2*n < nops(pw));
    f := proc(cond, piece)
      if cond::(name = name) then
        if member(op(1,cond), _EnvBinders) or
           member(op(2,cond), _EnvBinders) then
          NULL
        else
          cond, eval(piece, cond)
        end if
      elif cond::(name = anything) then
        if member(op(1,cond), _EnvBinders) then
          NULL
        else
          cond, eval(piece, cond)
        end if;
      elif cond::(anything = name) then
        if member(op(2,cond), _EnvBinders) then
          NULL
        else
          cond, eval(piece, op(2,cond) = op(1,cond))
        end if
      else
        cond, piece
      end if
    end proc;
    aa := seq(f(op(2*i+1,pw), op(2*i+2,pw)), i = 0..n-1);
    if aa=NULL then
      if rest then
        op(-1, pw)
      else
        error "pw with all false conditions (%1)", pw
      end if
    else
      `if`(rest, piecewise(aa, op(-1,pw)), piecewise(aa));
    end if;
  end proc;

  # - takes pw conditions and distributes them, for n = 1
  # - simplifies simple cases of nested pw
  # [note that it can be called on a non-pw, at which time it just returns]
  simp_pw := proc(pw)
    local res, cond, l, r, b1, b2, b3, rel, new_cond;
    if not type(pw,t_pw) then return pw end if;
    res := simp_pw_equal(pw);
    if not res::t_pw then return res end if;
    if nops(res)=4 then
      b1 := flip_cond(op(1,res));
      if b1 = op(3,res) then
        res := piecewise(op(1,res), op(2, res), op(4,res));
      end if
    end if;

    if nops(res)=3 then
      # trivial case
      if normal(op(2,res)-op(3,res))=0 then return op(2,res) end if;
      # distribute conditions
      cond := op(1,res);
      if cond::t_rel and (op(1,cond)::t_pw or op(2,cond)::t_pw) then
        l := op(1, cond);
        r := op(2, cond);
        if (l::t_pw) and (r::t_pw) then
          error "double-pw condition (%1)", cond;
        end if;
        if l::t_pw then
          rel := x -> op(0,cond)(x,r);
          b1 := rel(op(2,l));
          b2 := op(1,l);
          b3 := rel(op(3,l));
          new_cond := Or(And(b2, b1), And(flip_cond(b2), b3));
          res := piecewise(new_cond, op(2, res), op(3, res))
        else
          rel := x -> op(0,cond)(l,x);
          b1 := rel(op(2,r));
          b2 := op(1,r);
          b3 := rel(op(3,r));
          new_cond := Or(And(b2, b1), And(flip_cond(b2), b3));
          res := piecewise(new_cond, op(2, res), op(3, res))
        end if;
      end if;

      # simplify simple nested cases
      if res::t_pw and op(2,res)::t_pw and nops(op(2,res))=3 and
         normal(op([2,3],res) - op(3,res)) = 0 then
          res := simp_pw(piecewise(And(op(1,res),op([2,1],res)), op([2,2],res), op(3,res)));
      end if;
      if res::t_pw and op(3,res)::t_pw and nops(op(3,res))=3 and
         normal(op([3,2],res) - op(2,res)) = 0 then
          b1 := simp_Or(op(1,res),op([3,1],res));
          res := simp_pw(piecewise(b1, op(2,res), op([3,3],res)));
      end if;
      if res::t_pw and op(3,res)::t_pw and nops(op(3,res))=3 and
         normal(op([3,3],res) - op(2,res)) = 0 then
          res := simp_pw(piecewise(And(op([3,1],res), flip_cond(op(1,res))), op(2,res), op([3,3],res)));
      end if;
    elif nops(res)=6 and op(2,res)=op(6,res) then
      # case of an if-else that has been complicated -- merge
      res := simp_pw(piecewise(And(flip_cond(op(1,res)), op(3,res)),
                               op(4,res), op(2,res)));
    end if;
    res;
  end proc;

  # this assumes we are doing pw of measures.
  do_pw := proc(l, ctx)
    local len, rel, prop_ctx, this, var;
    len := nops(l);
    if len = 0 then Superpose()
    elif len = 1 then ToAST(l[1], ctx)
    else # len>2.
      # special case - boolean
      if type(l[1], name = identical(true)) and len = 3 then
        var := op(1, l[1]);
        If(var, ToAST(eval(l[2], var=true), ctx),
                 ToAST(eval(l[3], var=false), ctx));
      # special case - Either
      elif type(l[1], name = identical(Left)) and len = 3 then
        if op(1,l[1]) = Right then
          ToAST(l[3], ctx)
        else
          error "Checking if %1 = Left ?", op(1,l[1]);
        end if;
      else
        # should analyze and simplify things depending on cond
        If(l[1], ToAST(l[2], ctx), thisproc(l[3..-1], ctx))
      end if;
    end if;
  end;

  # this assumes we are doing pw of weight.
  do_pw_weight := proc(l)
    local len;
    len := nops(l);
    if len = 0 then 0 # is this right?
    elif len = 1 then l[1]
    else # len>2.
      # should analyze and simplify things depending on cond
      If(l[1], l[2], thisproc(l[3..-1], ctx))
    end if;
  end;

  # conservative determination of the domain of definition wrt var
  DomainOfDef := proc(expr, var, rng)
    local rng2;
    if expr::t_binds and not depends(op(2,expr),var) then
      DomainOfDef(op(1,expr), var, rng)
    elif expr::t_pw then
      if nops(expr)=3 and op(3,expr) = 0 then
        DomainOfDef(op(1,expr), var, rng)
      else
        rng
      end if;
    elif expr::specfunc(anything, 'And') then 
      # intersect; And is always binary
      rng2 := DomainOfDef(op(1,expr), var, rng);
      DomainOfDef(op(2,expr), var, rng2);
    elif expr::(identical(var) < numeric) then
      op(1,rng)..min(op(2,rng), op(2,expr))
    elif expr::(numeric < identical(var)) then
      max(op(1,expr), op(1,rng))..op(2,rng)
    else
      rng
    end;
  end proc;

  mkProb := proc(w, ctx)
    local typ, pb, rl, pos, rest, base, expo;
    if type(w, {integer, rational}) then
      if w < 0 then
        error "mkProb a negative number (%1)", w
      else
        w
      end if;
    elif type(w, `*`) then
      pb, rl := selectremove(x->evalb(member(infer_type(x,ctx),{Prob,Nat})), w);
      # have to adjust pb anyways, in case of sqrt, etc.
      pb := `if`(type(pb, {integer, rational}), pb, maptype(`*`, mkProb, pb, ctx));
      if type(rl, `*`) then
        pos, rest := selectremove(isPos, rl);
        pos := pb * maptype(`*`, mkProb, pos, ctx);
        if rest = 1 then 
          pos
        else
          pos * unsafeProb(mkReal(rest, ctx))
        end if;
      else
        if type(rl,rational) and rl>0 then
          pb*rl
        else
          pb*unsafeProb(mkReal(rl, ctx)); # should check rl>0! TODO
        end if;
      end if;
    elif type(w, `+`) then
      # if not isPos(w) then WARNING("cannot insure it will not crash") end if;
      typ := infer_type(w, ctx);
      if typ=Prob then
        map(mkProb, w, ctx) # need to deal with exponents
      elif typ=Real then
        unsafeProb(mkReal(w,ctx));  # remember that we're in log-space, so this is cheapest
      elif typ = Mixed then # need to cast to real, then back to Prob
        unsafeProb(mkReal(w, ctx))
      else # uh?
        error "in mkProb, got that (%1) is of type %2.", w, typ;
      end if;
    elif type(w, 'exp'(anything)) then
      exp_(mkReal(op(1,w), ctx));
    elif type(w, 'erf'(anything)) then
      erf_(mkProb(op(1,w), ctx));
    elif type(w, 'ln'(anything)) then
      error "mkProb ln: %1", w;
    elif type(w, anything^{identical(1/2), identical(-1/2)}) then
      (base, expo) := op(w);
      `if`(expo=1/2, sqrt_, recip@sqrt_)(mkProb(base, ctx))
    elif type(w, anything^posint) then
      (base, expo) := op(w);
      typ := infer_type(base, ctx);
      # cases are to optimize (minimize) the placement of unsafeProb
      if typ = Number then
        IntPow(base, expo)
      elif typ = Prob then
        IntPow(mkProb(base,ctx), expo)
      elif member(typ, {Real, Mixed}) then
        unsafeProb(mkReal(base, ctx)^expo)
      else
        error "mkProb of (%1)", w
      end if
    elif type(w, anything^negint) then
      (base, expo) := op(w);
      typ := infer_type(base, ctx);
      # cases are to optimize the placement of unsafeProb
      if typ = Number then
        recip(IntPow(base, -expo))
      elif typ = Prob then
        recip(IntPow(mkProb(base,ctx), -expo))
      else
        recip(unsafeProb(IntPow(base, -expo)))
      end if;
    elif type(w, anything^fraction) then # won't be sqrt
      unsafeProb(w);
    elif type(w, 'unsafeProb'(anything)) then
      error "there should be no unsafeProb in %1", w
    else
      typ := infer_type(w, ctx);
      # Number is a cheat, as it might be negative!
      if member(typ, {'Prob', 'Nat', 'Number'}) then
        w
      elif typ = 'Real' or type = 'Int' then
        # we are going to need to cast.  Is it safe?
        # if not isPos(w) then WARNING("cannot insure it will not crash") end if;
        unsafeProb(w);
      else
        error "how do I make a Prob from %1 in %2", w, eval(_EnvTypes)
      end if;
    end if;
  end proc;

  mkReal := proc(w, ctx)
    local prob, rl, typ, expo;
    if type(w,{integer,fraction}) then
      w
    elif w::`*` then
      rl, prob := selectremove(
          x->evalb(member(infer_type(x,ctx),{Real,Number,Int})), w);
      rl := maptype(`*`, mkReal, rl, ctx);
      # all parts are Real (or so Haskell will think so)
      if prob = 1 then
        rl
      else
        typ := infer_type(prob, ctx);
        if typ=Prob then
          rl * fromProb(mkProb(prob, ctx)); # fixes up powering
        elif typ=Mixed then
          rl * maptype(`*`, mkReal, prob, ctx)
        elif typ=Nat then
          prob * rl;
        else
          error "(%1) is neither Mixed nor Prob!?!", prob;
        end if;
      end if;
    elif w::`+` then
      map(mkReal, w, ctx) # might want to optimize this as above
    elif type(w, 'specfunc'(anything, {cos, sin, exp,erf})) then
      map(mkReal, w, ctx)
    elif type(w, anything ^ integer) then
      expo := op(2,w);
      rl := mkReal(op(1,w), ctx);
      rl^expo
    elif type(w, anything ^ fraction) then
      expo := op(2,w);
      rl := mkReal(op(1,w), ctx);
      rl ^ expo;
    elif type(w, 'symbol') then
      typ := infer_type(w, ctx);
      if member(typ ,{'Real', 'Number', 'Int', 'Nat'}) then
        w
      elif typ = Prob then
        fromProb(w);
      else
        error "don't know how to make symbol (%1) real", w;
      end if;
    elif type(w, specfunc(anything, 'If')) then
      If(op(1,w), mkReal(op(2,w), ctx), mkReal(op(3,w),ctx))
    else
      typ := infer_type(w, ctx);
      if member(typ ,{'Number'}) then
        w
      else
        error "don't know how to make (%1) real", w;
      end if;
    end if;
  end proc;

  # use assumptions to figure out if we are actually positive, even
  # when the types say otherwise
  isPos := proc(w)
    local res;

    try
      res := signum(0, w, 1) assuming op(_EnvPathCond);
      evalb(res = 1);
    catch "when calling":
      false; # pessimistic
    end try;
  end proc;

  toProp := proc(x::`=`)
    local nm, typ, prop, rest, left, right, r1, r2;
    (nm, typ) := op(x);

    if type(typ, 'symbol') then
      if typ = 'Real' then (prop, rest) := 'real', {};
      elif typ = 'Prob' then (prop, rest) := RealRange(0,infinity), {};
      elif typ = 'Bool' then (prop, rest) := boolean, {};
      elif typ = 'Unit' then (prop, rest) := identical(Unit), {};
      elif typ = 'Int' then (prop, rest) := 'integer', {};
      else
        error "Unknown base type %1", x
      end if;
    elif nm :: Pair(anything, anything) and
         typ :: Pair(anything, anything) then
      (left, r1) := thisproc(op(1, nm) = op(1,typ));
      (right, r2) := thisproc(op(2, nm) = op(2,typ));
      (prop, rest) := Pair(op([1,2],left), op([1,2],right)),
                     (`union`(r1, r2, left, right));
    else
      error "How can I make a property from %1", x;
    end if;
    {nm :: prop}, rest
  end proc;

  condToProp := proc(cond)
    eval(cond,{And=AndProp, Or=OrProp})
  end proc;

  toType := proc(x::`=`)
    local nm, typ, prop, rest, r1, r2;
    (nm, typ) := op(x);

    if type(typ, 'symbol') then
      rest := {nm::typ}
    elif nm :: Pair(anything, anything) and
         typ :: Pair(anything, anything) then
      r1 := thisproc(op(1, nm) = op(1,typ));
      r2 := thisproc(op(2, nm) = op(2,typ));
      rest := `union`(r1, r2);
    else
      error "How can I make a property from %1", x;
    end if;
    rest
  end proc;

  fill_table := proc(t, nm, typ)
    if nm::name then
      if typ = 'Real' then
        t[nm] := RealRange(-infinity, infinity)
      elif typ = 'Prob' then
        t[nm] := RealRange(0, infinity)
      elif typ = 'Bool' then
        t[nm] := boolean
      elif typ = 'Unit' then
        # Do nothing, this does not need remembered
      elif type = 'Int' then
        t[nm] := 'integer'
      else
        error "Real/Prob/Bool/Int/Unit are the only base types: %1", typ;
      end if;
    elif typ :: 'Pair'(anything, anything) then
      fill_table(t, op(1, nm), op(1, typ));
      fill_table(t, op(2, nm), op(2, typ));
    elif typ :: 'Measure'(anything) then
      error "cannot handle first-class measure types yet"
    elif typ :: 'Arrow'(anything,anything) then
      error "cannot handle first-class -> types yet"
    else
      error "I don't know type %1", typ;
    end if;
  end proc;

  getBinderForm := proc(t)
    local left, right;
    if t = 'Real' then gensym('rr')
    elif t = 'Prob' then gensym('pp')
    elif t :: Pair(anything, anything) then
      left := getBinderForm(op(1,t));
      right := getBinderForm(op(2,t));
      Pair(left, right);
    elif t = 'Bool' then gensym('bb')
    elif t = 'Unit' then gensym('uu') # we really do need a name!
    elif t = 'Int' then gensym('ii')
    else
      error "Trying to form a name from a %1", t
    end if;
  end proc;

  getCtx := proc(typ, glob, globNum, ctr)
    local nm, t;
    if type(typ, 'Arrow'(anything, anything)) then
      t := op(1,typ);
      # 'nm' is a name-filled type structure, not necessarily a name
      nm := getBinderForm(t);
      globNum[ctr] := nm;
      getCtx(op(2,typ), glob union {nm = t}, globNum, ctr+1)
    elif type(typ, 'Measure'(anything)) then
      glob, globNum, ctr, typ
    else
      error "must have either Measure or Arrow, got %1", typ;
    end if;
  end proc;

  instantiate := proc(e, ctx, ctr, typ)
    local nm;
    if ctr = ctx:-gsize then
      e
    else
      nm := ctx:-gnum[ctr];
      instantiate(e(nm), ctx, ctr + 1, op(2,typ))
    end if;
  end proc;

  # note that the 'nm' is a path, not necessarily of type name
  find_paths := proc(struct, nm)
    local lv, rv, lsubs, rsubs;
    if struct::Pair(anything, anything) then
      (lv, rv) := op(struct);
      lsubs := `if`(lv::name, {lv = Fst(nm)}, find_paths(lv, Fst(nm)));
      rsubs := `if`(rv::name, {rv = Snd(nm)}, find_paths(rv, Snd(nm)));
      lsubs union rsubs
    else
      error "expected nested tuple of names, got (%1)", struct;
    end if;
  end proc;

  lambda_wrap := proc(expr, cnt, ctx)
    local var, ee, newvar, name_subst;
    if cnt = ctx:-gsize then
      expr
    else
      var := ctx:-gnum[cnt];
      if type(var, 'name') then
        Lambda(var, lambda_wrap(expr, cnt+1, ctx));
      # cheat, for now
      elif type(var, Pair(anything, anything)) then
        newvar := gensym('pr');
        name_subst := find_paths(var, newvar);
        ee := subs({var = newvar} union name_subst, expr);
        Lambda(newvar, lambda_wrap(ee, cnt+1, ctx));
      else
        error "cannot yet lambda_wrap a %1", var
      end if;
    end if;
  end proc;

  # should pass _EnvTypes in directly so that option remember can be used
  infer_type := proc(e, ctx)
    local typ, l, res, k, t, typ1, typ2;
    if type(e, boolean) then
      'Bool'
    elif e = 'Pi' then Prob
    elif e = 'Unit' then Unit
    elif e = 'Lebesgue' then Measure(Real)
    elif e = 'Counting' then Measure(Int)
    elif e = 'undefined' then Real
    elif e = infinity or e = -infinity then Real
    elif type(e, boolean) then
      'Bool'
    elif type(e, anything^integer) then
      infer_type(op(1,e), ctx);
    elif type(e, specfunc(anything, {'exp', 'sin','cos'})) then
      typ := infer_type(op(1,e), ctx); # need to make sure it is inferable
      'Real' # someone else will make sure to cast this correctly
    elif type(e, specfunc(anything, {'GAMMA' })) then
      typ := infer_type(op(1,e), ctx); # need to make sure it is inferable
      'Prob'
    elif type(e, anything^anything) then
      typ1 := infer_type(op(1,e), ctx);
      typ2 := infer_type(op(2,e), ctx);
      # Number means (proper) fraction in this context
      if member(typ1, {Prob, Nat}) and member(typ2, {Prob, Number}) then
        Prob
      elif typ1=Prob and typ2=Int then
        Prob
      elif member(typ1, {Real, Mixed}) and member(typ2, {Prob, Number}) then
        typ1; # yes, we know it is Prob, but that is not its type...
      else
        error "inferring (%1)^(%2)", typ1,typ2;
      end if;
    elif type(e, 'erf'(anything)) then
      infer_type(op(1,e), ctx); # erf is Real, erf_ is Prob
      'Real'
    elif type(e, 'Ei'(posint, anything)) then
      infer_type(op(1,e), ctx);
      'Real'
    elif type(e, 'ln'(anything)) then
      typ := infer_type(op(1,e), ctx); # need to make sure it is inferable
      'Real'
    elif type(e, 'symbol') then
      # first look in the global context
      res := select(type, ctx:-gctx, identical(e) = anything);
      if nops(res)=1 then
        op([1,2], res)
      else # then in the current path
        res := select(type, _EnvTypes, 'identical'(e) :: 'anything');
        if nops(res)=1 then
          typ := op([1,2], res);
          #if type(typ, {'RealRange'(anything, anything), identical(real)}) then
          #  if signum(0,op(1,typ),0)=1 then 'Prob' else 'Real' end if
          #else
            typ
          #end if;
        else
          error "Impossible: an untyped free variable %1 in local context %2, got (%3)",
            e, eval(_EnvTypes), res
        end if;
      end if;
    elif type(e, 'Pair'(anything, anything)) then
      map(infer_type, e, ctx);
    elif type(e, {`+`, `*`}) then
      l := map(infer_type, [op(e)], ctx);
      join_type(op(l));
    elif type(e, 'nonnegint') then
      Nat; # need to track >=0 as well as Int
    elif type(e, 'integer') then
      Int; # need to track integer specifically; polymorphism handled elsewhere
    elif type(e, 'fraction') then
      Number # constants are polymorphic!
    elif type(e, specfunc(anything, 'If')) then
      # infer_type(op(1,e)); # should be Boolean
      join_type(infer_type(op(2,e),ctx), infer_type(op(3,e), ctx));
    elif type(e, {specfunc(anything, 'NormalD')}) then
      Measure(Real)
    elif type(e, specfunc(anything, 'Superpose')) then
      res := map(infer_type, {op(e)}, ctx);
      if nops(res) = 1 then
        res[1]
      else
        error "Superpose with multiple types %1", e
      end if;
    elif type(e, specfunc(anything, 'WeightedM')) then
      infer_type(op(2, e), ctx)
    elif type(e, specfunc(anything, 'Uniform')) then
      Measure(Real)
    elif type(e, specfunc(anything, {'BetaD', 'GammaD'})) then
      Measure(Prob)
    elif type(e, 'Bind'(anything, name, anything)) then
      Measure(Real)
    elif type(e, 'Bind'(anything, name = range, anything)) then
      Measure(Real)
    elif type(e, 'Tag'(anything, anything)) then

      (k, t) := infer_type_sop(op(2,e), ctx);
      TagMaple(k, t);

    else
      error "how do I infer a type from %1", e;
    end if;
  end proc;

  infer_type_prod := proc(e, ctx)
    local t0, ts;
    if e = 'Nil' then
      [];
    elif op(0,e) = 'Cons' then
      t0 := infer_type(op(1,e), ctx);
      ts := infer_type_prod (op(2,e), ctx);
      [t0, op(ts)];
    else error "infer_type_prod: %1 is not a product type", e
    end if;
  end proc;

  infer_type_sop := proc(e, ctx)
    local k, t;
    if op(0,e) = 'Zero' then
      (0, infer_type_prod (op(1,e), ctx));
    elif op(0,e) = 'Succ' then
      k, t := infer_type_sop (op(1,e), ctx);
      (k+1, t);
    else error "infer_type_sop: %1 is not a sum of product type", e
    end if;
  end proc;

  check_sop_type := proc(inferredType, actualType)
    local compatible_types, k, t, sopType;

    compatible_types := proc(inf, act)
      if inf = 'Number' then
        member(act, {'Nat', 'Int', 'Real', 'Prob'})
      else
        inf = act
      end if;
    end proc;

    (k, t) := op(inferredType);
    sopType := op(2, actualType);

    `and` (op (zip (compatible_types, t, op(k+1,sopType))))
  end proc;


  join2type := proc(a,b)
    if a = b then a
    elif a = 'Number' then b
    elif b = 'Number' then a
    elif a = 'Mixed' or b = 'Mixed' then 'Mixed'
    elif (member(a, {'Real', 'Int'}) and b = 'Prob') or
         (member(b, {'Real', 'Int'}) and a = 'Prob') then 'Mixed' # we'll need to patch
    elif (a = 'Real' and member(b, {'Nat', 'Int'})) or
         (b = 'Real' and member(a, {'Nat', 'Int'})) then 'Real'
    elif (a = 'Prob' and b = 'Nat') or
         (b = 'Prob' and a = 'Nat') then 'Prob'
    elif (a = 'Nat' and b = 'Int') or
         (b = 'Nat' and a = 'Int') then 'Int'
    else error "join2type of %1, %2", a, b
    end if;
  end proc;

  # could foldl, but this will work too
  join_type := proc()
    if _npassed < 2 then error "join_type: cannot happen, nargs<2"
    elif _npassed = 2 then
      join2type(_passed[1], _passed[2])
    else
      join_type(join2type(_passed[1], _passed[2]), _passed[3..-1])
    end if;
  end proc;
  ####
  # Fix-up the types using contextual information.
# TODO: need to add unsafeProb around the Prob-typed input variables,
# and then fix-up things like log.
#
# The right way to do this is really to do
# - full 'type' inference of e
# - full 'range-of-value' inference of e
  adjust_types := proc(e, typ, ctx)
    local ee, dom, opc, res, var, left, right, inf_typ, typ2, cond, fcond, cl;
    if type(e, specfunc(anything, 'Superpose')) then
      map(thisproc, e, typ, ctx)
    elif type(e, 'WeightedM'(anything, anything)) then
      WeightedM(mkProb(op(1,e), ctx), thisproc(op(2,e), typ, ctx));
    elif type(e, 'Return'(anything)) and type(typ, 'Measure'(anything)) then
      typ2 := op(1, typ);
      inf_typ := infer_type(op(1,e), ctx);
      if typ2 = Unit and op(1,e) = Unit then
        e
      elif typ2 = Prob then
        ee := op(1,e);
        res := mkProb(ee, ctx);
        'Return'(res);
      elif typ2 = Real and type(op(1,e), 'ln'(anything)) then
        ee := op(1,e);
        inf_typ := infer_type(op(1, ee), ctx);
        if inf_typ = 'Prob' then
          'Return'(ln_(op(1,ee)))
        else
          'Return'(ee);
        end if;
      elif typ2 = Real and member(inf_typ, {'Real', 'Number', 'Nat', 'Int'}) then
        'Return'(op(1,e))
      elif typ2 = Real and member(inf_typ, {'Mixed', 'Prob'}) then
        'Return'(mkReal(op(1,e), ctx));
      elif typ2 :: Pair(anything, anything) and
           op(1,e) :: Pair(anything, anything) then
        left  := adjust_types('Return'(op([1,1],e)), Measure(op(1,typ2)), ctx);
        right := adjust_types('Return'(op([1,2],e)), Measure(op(2,typ2)), ctx);
        'Return'(Pair(op(1,left), op(1,right)));
      elif typ2 = Bool and member(op(1,e), {true,false}) then
        e
      # typ2 will be Int as that is what Haskell sends us
      elif typ2 = Int and member(inf_typ, {'Int','Nat'}) then
        e
      elif type(typ2, 'Tagged'(anything, anything)) then
        if check_sop_type(inf_typ, typ2) then
          e
        else
          error "Type check failed in Tagged (adjust_types); type{%1} inf_type{%2} expr{%3}", typ2, inf_typ, e;
        end if;
      else
         error "adjust_types with type %1, inf_typ %2, for %3", typ, inf_typ, e;
      end if;
    elif type(e, 'Bind'(identical(Lebesgue), name, anything)) then
      var := op(2,e);
      _EnvTypes := _EnvTypes union {var :: Real};
      _EnvPathCond := _EnvPathCond union {var :: real};
      Bind(Lebesgue, var, adjust_types(op(3,e), typ, ctx));
    elif type(e, 'Bind'(identical(Lebesgue), name = range, anything)) then
      dom := RealRange(op([2,2,1],e), op([2,2,2], e));
      var := op([2,1],e);
      _EnvTypes := _EnvTypes union {var :: Real};
      _EnvPathCond := _EnvPathCond union {var :: dom};
      Bind(op(1,e), op(2,e), adjust_types(op(3,e), typ, ctx));
    elif type(e, 'Bind'(anything, name = range, anything)) then
      dom := compute_domain(op(1,e), var);
      var := op([2,1],e);
      inf_typ := infer_type(op(1,e), ctx); # should assert Measure(..)
      _EnvTypes := _EnvTypes union {var :: op(1,inf_typ)};
      _EnvPathCond := _EnvPathCond union {dom};
      # need to adjust types on first op, to its own type, as that may require
      # tweaking which functions are used
      Bind(adjust_types(op(1,e), inf_typ, ctx), op(2,e), adjust_types(op(3,e), typ, ctx));
    elif type(e, 'Bind'(anything, name, anything)) then
      dom := compute_domain(op(1,e), var);
      var := op(2,e);
      inf_typ := infer_type(op(1,e), ctx); # should assert Measure(..)
      _EnvTypes := _EnvTypes union {var :: op(1,inf_typ)};
      _EnvPathCond := _EnvPathCond union {dom};
      # need to adjust types on first op, to its own type, as that may require
      # tweaking which functions are used
      Bind(adjust_types(op(1,e), inf_typ, ctx), op(2,e), adjust_types(op(3,e), typ, ctx));
    elif type(e, 'If'(name, anything, anything)) then
      # special case
      var := op(1,e);
      left := adjust_types(eval(op(2,e), var=true), typ, ctx);
      right := adjust_types(eval(op(3,e), var=false), typ, ctx);
      If(var, left, right);
    elif type(e, 'If'(anything, anything, anything)) then
      cond := op(1,e);
      fcond := flip_cond(cond);
      opc := _EnvPathCond;
      cl := simp_props(opc union {cond});
      if cl = false then  # cond is unsat
        cl := simp_props(opc union {fcond});
        if cl = false then # so is fcond, oh my!
          error "_EnvPathCond (%1) itself is unsat!", _EnvPathCond;
        end if;
        _EnvPathCond := cl;
        adjust_types(op(3,e), typ, ctx);
      else
        _EnvPathCond := cl;
        left := adjust_types(op(2,e), typ, ctx);
        cl := simp_props(opc union {fcond});
        if cl = false then # fcond is unsat, just return left
          return left;
        else
          _EnvPathCond := cl;
          right := adjust_types(op(3,e), typ, ctx);
          If(cond, left, right);
        end if;
      end if;
    elif e = Lebesgue and typ = 'Measure(Real)' then
      e
    elif type(e, 'Uniform'(anything, anything)) and typ = 'Measure(Real)' then
      e
    elif type(e, 'Uniform'(anything, anything)) and typ = 'Measure(Prob)' then
      var := gensym('pp');
      Bind(e, var, Return(unsafeProb(var)))
    elif type(e, 'BetaD'(anything, anything)) and typ = 'Measure(Prob)' then
      BetaD(mkProb(op(1,e), ctx), mkProb(op(2,e), ctx))
    elif type(e, 'BetaD'(anything, anything)) and typ = 'Measure(Real)' then
      var := gensym('pp');
      res := BetaD(mkProb(op(1,e), ctx), mkProb(op(2,e), ctx));
      Bind(res, var, Return(fromProb(var)))
    elif type(e, 'GammaD'(anything, anything)) and typ = 'Measure(Prob)' then
      GammaD(mkProb(op(1,e), ctx), mkProb(op(2,e), ctx))
    elif type(e, 'NormalD'(anything, anything)) and typ = 'Measure(Real)' then
      NormalD(mkReal(op(1,e),ctx), mkProb(op(2, e), ctx))
    elif e = 'Counting' and typ = 'Measure(Int)' then
      Counting
    else
     error "adjust_types of %1 at type %2", e, typ;
    end if;
  end proc;

  flip_cond := proc(cond)
    if type(cond, `<`) then op(2,cond) <= op(1,cond)
    elif type(cond, `<=`) then op(2,cond) < op(1,cond)
    elif type(cond, `=`) then op(1,cond) <> op(2,cond)
    elif type(cond, `<>`) then op(1,cond) = op(2,cond)
    elif cond::specfunc(anything, 'And') and nops(cond)=2 then
      Or(flip_cond(op(1,cond)), flip_cond(op(2,cond)))
    elif cond::specfunc(anything, 'Or') and nops(cond)=2 then
      And(flip_cond(op(1,cond)), flip_cond(op(2,cond)))
    elif cond::specfunc(anything, 'Not') then
      op(1,cond)
    elif cond::name then
      'Not'(cond)
    else
      error "Don't know how to deal with condition %1", cond
    end if;
  end proc;

  compute_domain := proc(e, v)
    local res;
    if type(e, 'Uniform'(anything, anything)) then
      # 'RealRange'(op(e));
      AndProp(v>=op(1,e), v<=op(2,e));
    elif type(e, 'GammaD'(anything, anything)) then
      v::'RealRange'(0,infinity);
    elif type(e, 'BetaD'(anything, anything)) then
      v::'RealRange'(0,1);
    elif type(e, {identical('Lebesgue'), specfunc(anything, 'NormalD')}) then
      v::'real'
    elif type(e, specfunc(anything, 'Superpose')) then
      res := map((x -> compute_domain(op(2,x),v)), {op(e)});
      if nops(res)=1 then
        res[1]
      else
        error "expression %1 has multiple domain: %2", e, res
      end if;
    elif type(e, 'Bind'(anything, name, anything)) then
      v::'real'
    elif type(e, 'Bind'(anything, name = range, anything)) then
      v::RealRange(op([2,2,1], e), op([2,2,2], e))
    elif type(e, 'WeightedM'(anything, anything)) then
      compute_domain(op(2,e))
    elif e = 'Counting' then
      v::'Int'
    else
      error "compute domain: %1", e;
    end if;
  end proc;

  # returns something of the right shape for assume
  analyze_cond := proc(c,ctx)
    if type(c, name = identical(true)) then
      error "analyze_cond should not be called with a boolean variable";
    else
      c
    end if;
  end proc;

  # while inside the evaluator, we want infinities
  MyHandler := proc(operator, operands, default_value)
    NumericStatus( division_by_zero = false);
    if operator='ln' then -infinity else default_value end if;
  end proc;

  # dirac < uniform < NormalD < bind < WeightedM < If < SUPERPOSE
  # returns false on equality
  comp2 := proc(x,y)
    if evalb(x=y) then false
    elif x::Return(anything) then
      if y::Return(anything) then
        comp_algeb(op(1,x), op(1,y))
      else
	true
      end if
    elif x::Uniform(numeric, numeric) then
      if y::Uniform(numeric, numeric) then
	evalb(op(1,x) < op(1,y))
      else
	evalb(not member(op(0,y), '{Return}'))
      end if
    elif x::specfunc(anything, NormalD) then
      if y::specfunc(anything, NormalD) then
        comp_list(zip( compare, [op(x)], [op(y)]));
      else
	evalb(not member(op(0,y), '{Return, Uniform}'));
      end if;
    elif x::specfunc(anything, 'Bind') then
      if y::specfunc(anything, 'Bind') then
	comp2(op(3, x), op(3, y))
      else
	evalb(not member(op(0,y), '{Return, Uniform, NormalD}'));
      end if
    elif x::specfunc(anything, 'WeightedM') then
      if y::specfunc(anything, 'WeightedM') then
        comp2(op(2, x), op(2, y))
      else
	evalb(not member(op(0,y), '{Return, Uniform, NormalD, WeightedM}'));
      end if;
    elif x::specfunc(anything, 'If') then
      if y::specfunc(anything, 'If') then
        # cheat!
        evalb( length(x) < length(y) )
      else
	evalb(not member(op(0,y), '{Return, Uniform, NormalD, WeightedM, If}'));
      end if;
    elif x::specfunc(anything, 'SUPERPOSE') then
      if y::specfunc(anything, 'SUPERPOSE') then
        error "cannot compare 2 SUPERPOSE %1, %2", x, y
      else
	evalb(not member(op(0,y), '{Return, Uniform, NormalD, WeightedM, If, SUPERPOSE}'));
      end if;
    else
      error "cannot compare: %1, %2", x, y
    end if;
  end proc;

  comp_algeb := proc(x, y)
    if x::numeric and y::numeric then
      evalb( x < y )
    elif {op(0,x), op(0,y)} = {Pair} then
      comp_list(zip( compare, [op(x)], [op(y)]));
    else # just cheat
      evalb( length(x) < length(y) )
    end if;
  end proc;

  comp_list := proc(l)
    if nops(l)=0 then
      false
    elif l[1]=LESS then
      true
    elif l[1]=GREATER then
      false
    else
      comp_list(l[2..-1])
    end if;
  end proc;

  compare := proc(x, y)
    if evalb(x=y) then
      EQUAL
    elif comp_algeb(x,y) then
      LESS
    elif comp_algeb(y,x) then
      GREATER
    else
      EQUAL # can this happen?
    end if;
  end proc;

  # helper routines for tweaking ASTs
  simp_sup := proc()
    SUPERPOSE(op(sort([_passed], 'strict'=comp2)))
  end proc;

  # simplify some properties.  In particular:
  # - weird routine to catch unsat, which means a condition list implies false
  # - simplify out monotone functions
  simp_props := proc(p)
    local res, X, pl, ii;
    pl := map2(on_rels, simp_mono, map(condToProp, p));
    ii := remove(type, indets(pl, 'name'), constant);
    try
      # dummy query for unsat only
      coulditbe(X(op(ii)) > 0) assuming op(pl);
      res := pl;
    catch "when calling '%1'. Received: 'contradictory assumptions'":
    # catch "the assumed property", "contradictory assumptions":
      res := false;
    catch "when calling": # all other errors
      res := pl;
    end try;
    res;
  end proc;

  # traverse into a Prop and apply to relations
  on_rels := proc(f, p)
    if p::specfunc(anything, {AndProp, OrProp}) then
      map2(on_rels, f, p)
    elif type(p, {'`<`','`<=`'}) then
      f(p)
    else
      p
    end if;
  end proc;

  flip_rel := proc(r)
    if   r = `<` then `>` elif r = `<=` then `>=` 
    elif r = `>` then `<` elif r = `>=` then `<=` else
      error "should only get inequality"
    end if;
  end proc;

  simp_mono := proc(p)
    local n, rel, e, m;

    if p :: {numeric < anything, numeric <= anything} then
      (n,e) := op(p); rel := op(0,p);
    elif p :: {anything < numeric, anything <= numeric} then
      (e,n) := op(p); rel := flip_rel(op(0,p));
    else
      return p;
    end if;

    if e :: (numeric &* anything) then
      m := op(1,e);
      if m<0 then
        simp_mono(flip_rel(rel)(n/m, op(2,e)))
      else
        simp_mono(rel(n/m, op(2,e)))
      end if;
    elif e :: ln(anything) then
      simp_mono(rel(exp(n), op(1,e)))
    elif e :: exp(anything) then
      simp_mono(rel(ln(n), op(1,e)))
    else
      rel(n, e)
    end if;
  end proc;

  into_sup := proc(wm, w) WeightedM(simplify(w*op(1,wm)), op(2,wm)) end proc;

  # sort, then fix things up to make printing easier
  adjust_superpose := proc(e)
    local f;
    f := proc()
      'SUPERPOSE'(seq(`if`(op(0,_passed[i])='WeightedM',
                          'WM'(op(_passed[i])),
                          'WM'(1,_passed[i])), i=1.._npassed))
    end proc;
    eval(eval(e, Superpose=simp_sup), SUPERPOSE = f);
  end proc;

  get_de := proc(dens, var, Dx)
    local de, init, diffop;
    try
      de := gfun[holexprtodiffeq](dens, f(var));
      if not (de = NULL) and not (de :: set) then
        de := gfun[diffeqtohomdiffeq](de, f(var));
      end if;
      if de::set then
        init, de := selectremove(type, de, `=`);
        if nops(de)=1 then
          de := de[1];
          diffop := DEtools[de2diffop](de, f(var), [Dx, var]);
          return Diffop(diffop, init)
        end if;
      elif not (de = NULL) then # no initial condition returned
        diffop := DEtools[de2diffop](de, f(var), [Dx, var]);
        return Diffop(diffop, {}); # should be {f(0)=0} ?
      end if;
    catch: # do nothing
    end try;
    Nothing
  end proc;

  # density recognizer for reals
  recognize_density := proc(diffop, init, Dx, var)
    local a0, a1, scale, at0, mu, sigma, ii;
    if degree(diffop, Dx) = 1 then
      a0 := coeff(diffop, Dx, 0);
      a1 := coeff(diffop, Dx, 1);
      if degree(a0, var) = 1 and degree(a1, var) = 0 and nops(init) = 1 then
        ii := rhs(init[1]);
        scale := coeff(a0, var, 1);
        mu := -coeff(a0, var, 0)/scale;
        sigma := sqrt(coeff(a1, var, 0)/scale);
        at0 := simplify(eval(ii/density[NormalD](mu, sigma)(0)));
        return WeightedM(at0, NormalD(mu,sigma));
      end if;
    end if;
    NULL;
  end proc;

  # density recognizer for 0..1
  recognize_density_01 := proc(full_diffop, init, Dx, var)
    local a0, a1, scale, at0, a, b, c0, ii, constraints, sol, diffop;

    # throw away the content, it does not help us!
    diffop := primpart(full_diffop, Dx);
    if degree(diffop, Dx) = 1 then
      ii := map(convert, init, 'diff');
      a0 := coeff(diffop, Dx, 0);
      a1 := coeff(diffop, Dx, 1);
      if degree(a0,var)=1 and degree(a1,var)=2 and normal(var^2-var - a1)=0 then
        a := coeff(a0, var, 0) + 1;
        b := -coeff(a0, var, 1) - a + 2;
        if init = {} then
          return BetaD(a,b);
        else
          constraints := eval(ii, f = (x -> c0*density[BetaD](a,b)(x)));
          sol := solve(constraints, c0);
          return WeightedM(eval(c0, sol), BetaD(a,b));
        end if;
      # degenerate case with b=1
      elif degree(a0,var)=0 and degree(a1,var)=1 and normal(var + a1)=0 then
        a := coeff(a0, var, 0) + 1;
        if init = {} then
          return BetaD(a,1);
        else
          constraints := eval(ii, f = (x -> c0*density[BetaD](a,1)(x)));
          sol := solve(constraints, c0);
          return WeightedM(eval(c0, sol), BetaD(a,1));
        end if;
      # degenerate case with a=1
      elif degree(a0,var)=0 and degree(a1,var)=1 and normal(a1 - (var-1))=0 then
        b := -(coeff(a0, var, 0) - 1);
        if init = {} then
          return BetaD(1,b);
        else
          constraints := eval(ii, f = (x -> c0*density[BetaD](1,b)(x)));
          sol := solve(constraints, c0);
          return WeightedM(eval(c0, sol), BetaD(1,b));
        end if
      # degenerate case with a=1, presented differently
      elif degree(a0,var)=0 and degree(a1,var)=1 and normal(a1 + (var-1))=0 then
        b := (coeff(a0, var, 0) + 1);
        if init = {} then
          return BetaD(1,b);
        else
          constraints := eval(ii, f = (x -> c0*density[BetaD](1,b)(x)));
          sol := solve(constraints, c0);
          return WeightedM(eval(c0, sol), BetaD(1,b));
        end if;
      end if;
    end if;
    NULL;
  end proc;

  # density recognizer for 0..infinity
  # warning: Maple's gamma distribution swaps its parameters wrt Hakaru's!
  recognize_density_0inf := proc(diffop, init, Dx, var)
    local a0, a1, scale, at0, b, c;
    if degree(diffop, Dx) = 1 then
      a0 := coeff(diffop, Dx, 0);
      a1 := coeff(diffop, Dx, 1);
      if degree(a0, var) = 1 and degree(a1, var) = 1 then
        if coeff(a1,var,0)= 0 then
          scale := coeff(a0,var,1);
          b := coeff(a1, var, 1)/scale;
          c := (b-(coeff(a0,var,0)/scale))/b;
          return GammaD(c, b);
        end if;
      # and Hakaru uses the 'alternate' definition of exponential...
      # TODO: take care of initial condition too
      elif degree(a0,var) = 0 and degree(a1, var) = 0 then
        scale := coeff(a1, var, 0);
        b := coeff(a0, var, 0)/scale;
        return GammaD(1,1/b);
      end if;
    end if;
    NULL;
  end proc;

  mkRealDensity := proc(dens, var, rng)
    local de, res, new_dens, Dx, diffop, init, c, d, finite;
    if dens :: specfunc(anything, 'WeightedM') then
      res := NULL;
      # no matter what, get the de.
      # TODO: might want to switch from var=0 sometimes
      de := get_de(op(1,dens),var,Dx);
      if de::specfunc(anything, 'Diffop') then
        (diffop, init) := op(de);
        # dispatch on rng
        if rng = 0..1 then
          res := recognize_density_01(diffop, init, Dx, var) assuming op(_EnvPathCond), var::RealRange(0,1);
        elif rng = 0..infinity then
          res := recognize_density_0inf(diffop, init, Dx, var) assuming op(_EnvPathCond), var>0;
          # need to fix up initial conditions
          if res <> NULL then
            (c,d) := op(res);
            new_dens := op(1,dens)/density[GammaD](c,d)(var);
            new_dens := simplify(new_dens) assuming op(_EnvPathCond),var>0;
            if depends(new_dens,var) then
              error "mkRealDensity problem";
            end if;
            res := WeightedM(new_dens, res);
          end if;
        else # actually use 'real' recognizer in all these cases
          res := recognize_density(diffop, init, Dx, var) assuming op(_EnvPathCond), var::real;
        end if;
      end if;

      if res<>NULL then
        Bind(res, var = rng, op(2,dens))
      else
        Bind(Lebesgue, var = rng, dens)
      end if;
    elif dens :: specfunc(anything, 'Bind') then
      new_dens := mkRealDensity(op(1, dens), var, rng);
      # uses associatibity of >>=
      Bind(op(1, new_dens), op(2, new_dens),
        Bind(op(3, new_dens), op(2, dens), op(3, dens)));
    else # don't worry about Uniform, Bind/Lebesgue will take care of it
      Bind(Lebesgue, var = rng, dens)
    end if
  end proc;

  density[NormalD] := proc(mu, sigma) proc(x)
    1/sigma/sqrt(2)/sqrt(Pi)*exp(-(x-mu)^2/2/sigma^2)
  end proc end proc;
  density[BetaD] := proc(a, b) proc(x)
    x^(a-1)*(1-x)^(b-1)/Beta(a,b)
  end proc end proc;
  # Hakaru uses the alternate definition of gamma, so the args are backwards
  density[GammaD] := proc(theta,k) proc(x)
    x^(theta-1)/k^(theta-1)*exp(-x/k)/k/GAMMA(theta);
  end proc end proc;

#############
# more hacks to get around Maple weaknesses
  myint := proc(expr, b)
    local var, inds, res, res0, res1, newe;
    _EnvBinders := _EnvBinders union {op(1,b)};
    var := op(1,b);
    inds := indets(expr, specfunc(anything,c));
    inds := select(depends, inds, var);
    if Normalizer(op([2,1],b)-op([2,2],b)) = 0 then 
      res := 0;
    elif inds={} then
      if type(expr, t_binds) then
        res := subsop(1=myint(op(1,expr),b), expr) assuming op(_EnvPathCond);
        res := simp(res);
      else
        res0 := simp(int(expr, b) assuming op(_EnvPathCond));
        if type(res0, t_binds) and op(2,res0)=b then # didn't work, try harder
          newe := simplify(convert(expr,Heaviside));
          res1 := int(newe, b) assuming op(_EnvPathCond);
          if not type(res1, t_binds) then # success!
            res := fix_Heaviside(res1, res0);
          else
            res := res0;
          end if;
        else
          res := res0;
        end if;
      end if;
    elif type(expr, t_pw) then
      # what is really needed here is to 'copy'
      # PiecewiseTools:-IntImplementation:-Definite
      try
        res := myint_pw(expr, b)
      catch "cannot handle condition":
        res := Int(expr, b)
      end try;
    elif type(expr, t_binds) then
      # go in!  This can take a lot of time.  Should really have special code
      if not depends(op([2,2],expr), var) then
        res := int(expr, b);
      else
        res := Int(expr, b)
      end if;
    else
      res := Int(expr, b)
    end if;
    if has(res, 'csgn') then 
      simplify(res) assuming op(_EnvPathCond)
    else
      res
    end if;
  end proc;

  # if the boundaries are not 'natural' for the piecewise, things might go weird
  myint_pw := proc(expr, b :: name = `..`)
    local rels, n, rest, i, res, res2, var, lower, upper, cond;
    n := floor(nops(expr)/2);
    rels := [seq(op(2*i-1, expr), i=1..n)];
    rest := evalb(2*n < nops(expr));
    upper := op([2,2],b);
    if type(rels, list({`<`, `<=`})) and indets(rels,'name') = {op(1,b)} then
      res := 0; lower := op([2,1], b); var := op(1,b);
      for i from 1 to n do
        cond := op(2*i-1, expr);
        if cond::{identical(var) < anything, identical(var) <= anything} and
          evalb(signum(op(2,cond) - lower) = 1) then # op2 > lower
          res := res + myint(op(2*i, expr), var = lower .. min(upper,op(2,cond)));
          lower := op(2,cond);
        elif cond::{anything < identical(var), anything <= identical(var)} and
          evalb(signum(upper - op(1,cond)) = 1) then # op1 < upper
          res := res + myint(op(2*i, expr), var = max(lower,op(1,cond)) .. upper);
          upper := op(1,cond);
        else
          error "cannot handle condition (%1) while integrating pw", cond;
        end if;
      end do;
      if rest then # note that lower=upper is possible, but ok
        if lower < upper then
          res := res + myint(op(-1, expr), var = lower..upper);
        end if;
      end if;
      res
    elif length(expr) < 200 then # what have we got to lose?
      res := int(expr, b);
      if type(res, t_binds) then
        res2 := int(convert(expr, Heaviside), b);
        if not (indets(res2, specfunc(anything, '{Dirac,Heaviside}')) = {}) then
          fix_Heaviside(res2, res)
        else
          res
        end if;
      else
        res
      end if;
    else # well, too much time!
      Int(expr, b)
    end if;
  end proc;
end;

# works, but could be made more robust
`evalapply/if_` := proc(f, t) if_(op(1,f), op(2,f)(t[1]), op(3,f)(t[1])) end;
`evalapply/Pair` := proc(f, t) Pair(op(1,f)(t[1]), op(2,f)(t[1])) end;


# Disabled until Pair is removed in Hakaru

# Pair := proc(a,b) Tag(P2, Zero(Cons(a, Cons(b, Nil )))) end proc;

# `type/Nil` := proc(val) evalb(val = 'Nil') end proc;

# `type/Pair` := proc(val, t0, t1)
#   type(val, Tag(identical(P2), Zero(Cons(t0, Cons (t1, Nil )))))
# end proc;

# PairType := proc(a,b) Tagged(P2(a,b), [[ a,b ]]); end proc;

# `type/PairType` := proc(val, t0, t1)
#   type(val, Tagged(P2(t0, t1), [[ t0, t1 ]] ));
# end proc;


fst := proc(e)
  if e::Pair(anything, anything) then
    op(1,e)
  elif e::specfunc(anything, if_) then
    if_(op(1,e), fst(op(2,e)), fst(op(3,e)))
  else
    'fst'(e)
  end if;
end proc;

snd := proc(e)
  if e::Pair(anything, anything) then
    op(2,e)
  elif e::specfunc(anything, if_) then
    if_(op(1,e), snd(op(2,e)), snd(op(3,e)))
  else
    'snd'(e)
  end if;
end proc;

# piecewise is horrible, so this hack takes care of some of it
if_ := proc(cond, tb, eb)
  if cond = true then
    tb
  elif cond = false then
    eb
  elif cond::name then
    if_(cond = true, tb, eb)
  elif (eb = false) then
    And(cond, tb)
  elif (tb = true) then
    Or(cond, eb)
  elif (eb = true) and (tb = false) then
    SLO:-flip_cond(cond)
  else
    'if_'(cond, tb, eb)
  end if;
end proc;

WeightedM := proc(w, m)
  if w=1 then
    m
  # we want to allow infinity as weight, but WeightedM(infinity, Superpose())
  # should not disappear.
  elif type(m, specfunc(anything, 'Superpose')) and not m = infinity then
    Superpose(op(map(into_sup, m, w)));
  elif type(m, specfunc(anything, 'WeightedM')) then
    WeightedM(w*op(1,m), op(2,m))
  else
    'WeightedM'(w,m)
  end if;
end;

Superpose := module()
  export ModuleApply;
  local bb;

  bb := proc(t, k, no_rng)
    local bds, var;
    bds := t[op(k)];
    var := gensym('xx');
    if bds::`+` then
      if no_rng then
        bds := map(x -> subs(op(2,x)=var, x), [op(bds)]); # rename uniformly
        Bind(k[1], var, Superpose(op(map2(op, 3, bds))))
      else
        bds := map(x -> subs(op([2,1],x)=var, x), [op(bds)]); # rename uniformly
        Bind(k[1], var = k[2], Superpose(op(map2(op, 3, bds))))
      end if;
    else
      bds
    end if;
  end proc;
  ModuleApply := proc()
    local wm, bind, bindrr, i, j, res, l;
    if _npassed = 1 then
      _passed[1]
    else
      wm := table('sparse'); bind := table('sparse'); bindrr := table('sparse');
      l := map(x -> `if`(op(0,x)='Superpose', op(x), x), [_passed]);
      for i in l do
        if i::'WeightedM'(anything, anything) then
          wm[op(2,i)] := wm[op(2,i)] + op(1,i);
        elif i::'Return'(anything) then
          wm[i] := wm[i] + 1;
        elif i::'Bind'(anything, name, anything) then
          bind[op(1,i)] := bind[op(1,i)] + i;
        elif i::'Bind'(anything, name = range, anything) then
          bindrr[op(1,i), op([2,2],i)] := bindrr[op(1,i), op([2,2], i)] + i;
        elif i::specfunc(anything, 'If') then
          wm[i] := wm[i] + 1;
        else
          # error "how do I superpose %1", i;
          # rather than error out, just pass it through
          wm[i] := wm[i] + 1;
        end if;
      end do;
      res := [
        seq(WeightedM(wm[j], j), j = [indices(wm, 'nolist')]),
        seq(bb(bind,j,true), j = [indices(bind)]),
        seq(bb(bindrr,j,false), j = [indices(bindrr)])];
      if nops(res)=1 then res[1] else 'Superpose'(op(res)) end if;
    end if;
  end proc;
end module;

Bind := proc(w, var, meas)
  if var::name and meas = Return(var) then
    w
#  elif var::name and
#    meas :: 'WeightedM'(anything, 'Return'(identical(var))) and
#    not depends(op(1, meas), var) then
#    WeightedM(op(1,meas), w)
  elif var::name and meas :: 'WeightedM'(anything, anything) and
    not depends(op(1, meas), var) then
    WeightedM(op(1,meas), Bind(w, var, op(2,meas)))
  elif var::name and meas :: 'Return'(identical(var)) then
    w
  elif var::`=` and op(2,var) = (-infinity)..infinity then
    Bind(w, op(1,var), meas)
  elif var::`=` and op(2,var) = 0..1 and w::specfunc(anything,'BetaD') then
    Bind(w, op(1,var), meas)
  elif var::`=` and op(2,var) = 0..infinity and w::specfunc(anything,'GammaD') then
    Bind(w, op(1,var), meas)
  elif w='Lebesgue' and var::`=` and not(op([2,1],var) :: SymbolicInfinity)
        and not(op([2,2],var) :: SymbolicInfinity) then
    Bind(Uniform(op([2,1],var), op([2,2],var)), op(1,var), meas)
  elif w :: 'WeightedM'(anything, anything) then
    WeightedM(op(1,w), Bind(op(2,w), var, meas));
  else
    'Bind'(w, var, meas)
  end if;
end proc;

If := module()
  export ModuleApply;
  local patch_eb;

  patch_eb := proc(eb2, cond2)
    local fcond, new_cond, rest_cond, t1, t2, rest;

    fcond := SLO:-flip_cond(cond2);
    new_cond := And(op(1,eb2), fcond);
    rest_cond := And(SLO:-flip_cond(op(1,eb2)), fcond);
    t1 := coulditbe(new_cond) assuming op(_EnvPathCond);
    t2 := simplify(piecewise(rest_cond, 1, 0));
    t2 := not (evalb(t2=0));
    if t1=false then
      rest := op(3,eb2);
      if op(0,rest) = 'If' then
        If(And(op(1,rest), rest_cond), op(2, rest), op(3, rest))
      else
        rest
      end if;
    elif t2 then
      eb2
    else
      op(2,eb2)
    end if;
  end proc;

  ModuleApply := proc(cond, tb, eb)
    local new_eb;
    if cond = true then
      tb
    elif cond = false then
      eb
    elif tb = 'Return'(undefined) then
      # must 'patch things up' if we had a nested If
      `if`(op(0,eb) = 'If', patch_eb(eb, cond), eb);
    elif eb = Return(undefined) then
      tb
    elif tb = eb then
      eb
    elif type(cond, anything = identical(true)) then
      If(op(1,cond), tb, eb)
    elif op(0,eb) = 'If' and op(3,eb)=Superpose() then
      new_eb := patch_eb(eb, cond);
      if normal(new_eb-eb) = 0 then
        'If'(cond, tb, new_eb)
      else
        If(cond, tb, new_eb)
      end if;
    else
      'If'(cond, tb, eb)
    end if;
  end proc;
end module;

# A Context contains
# - a (Maple-encoded) Hakaru type 'htyp' (H-types)
# - a Measure type
# - a global context of var = H-types
# - a global numbering context for var names
# - the size of the global context (in # of variables)
`type/Context` := 'record'('htyp', 'mtyp', 'gctx', 'gnum', 'gsize');

gensym := module()
  export ModuleApply;
  local gs_counter;
  gs_counter := 0;
  ModuleApply := proc(x::name)
    gs_counter := gs_counter + 1;
    x || gs_counter;
  end proc;
end module;

MVECTOR := proc(expr, bnd :: name = identical(0) .. anything)
  local j, nj;
  j := op(1,bnd);
  nj := gensym('`ind`');
  HVect(op(2, bnd), nj, eval(expr, j = nj));
end proc;

Reduce := proc(f, i, v)
  local accum, j, rng, lo, hi;

  if v :: HVect(integer..integer, name, anything) then
    accum := i;
    (lo,hi) := op(op(1,v));
    for j from 0 to hi-lo-1 do
      accum := f(vindex(v,j))(accum);
    end do;
    accum;
  else
    'Reduce'(f,i,v)
  end if;
end proc;

vindex := proc(v,i) 
  if i::integer and v::HVect(anything, name, anything) then 
    eval(op(3,v), op(2,v)=i)
  else 
    'vindex'(v,i) 
  end if 
end proc;

vsize := proc(v)
  if v :: HVect(integer..integer, name, anything) then
    op([1,2],v)-op([1,1],v)
  else
    'vsize'(v)
  end if
end proc;

unpair := proc(f, p)
  if p::Pair(anything, anything) then
    f(op(1,p), op(2,p))
  elif p::specfunc(anything, piecewise) and nops(p)=3 then # FIXME
    piecewise(op(1,p), unpair(f,op(2,p)), unpair(f, op(3,p)))
  elif p::specfunc(anything, if_) then # FIXME
    if_(op(1,p), unpair(f,op(2,p)), unpair(f, op(3,p)))
  else
    'unpair'(f,p)
  end if;
end proc;

uneither := proc(f1, f2, e)
  if e::Left(anything) then
    f1(op(1,e))
  elif e::Right(anything) then
    f2(op(1,e))
  else
    'uneither'(f1,f2,e)
  end if
end proc;
