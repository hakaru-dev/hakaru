# We create 4 new binding forms.  Teach Maple (through depends and eval)
# about them.
# Integrand, LO, and lam bind from 1st arg to 2nd arg, whereas Bind
# binds from 2nd arg to 3rd arg.

`depends/Integrand` := proc(h, e, x) depends(e, x minus {h}) end proc:
`depends/LO`        := proc(h, e, x) depends(e, x minus {h}) end proc:
`depends/lam`       := proc(h, e, x) depends(e, x minus {h}) end proc:

# note that v _can_ occur in m1.
`depends/Bind` := proc(m1, v, m2, x)
  depends(m1, x) or depends(m2, x minus {v})
end proc:

generic_evalat := proc(vv, mm, eqs)
  local v, m, eqsRemain, subsEq, eq, vRename, funs;
  v, m := vv, mm;
  funs := map2(op, 0, indets(mm, 'function'));
  eqsRemain := remove((eq -> op(1,eq) = op(2,eq)), eqs);
  eqsRemain, subsEq := selectremove((eq -> type(op(1,eq), 'name')), eqsRemain);
  eqsRemain := select((eq -> op(1,eq) <> v and
    (depends(mm, op(1,eq)) or member(op(1,eq), funs))), eqsRemain);
  if depends(eqsRemain, v) then
    vRename := gensym(v);
    m := subs(v=vRename, m);
    v := vRename;
  end if;
  m := subs(subsEq,m);
  if nops(eqsRemain) > 0 then
    m := eval(m,eqsRemain);
  end if;
  v, m;
end proc:

`eval/Integrand` := proc(e, eqs)
  local v, m2;
  v, m2 := op(e);
  eval(op(0,e), eqs)(generic_evalat(v, m2, eqs))
end proc:

`eval/LO` := proc(e, eqs)
  local v, m2;
  v, m2 := op(e);
  eval(op(0,e), eqs)(generic_evalat(v, m2, eqs))
end proc:

`eval/lam` := proc(e, eqs)
  local v, m2;
  v, m2 := op(e);
  eval(op(0,e), eqs)(generic_evalat(v, m2, eqs))
end proc:

`eval/Bind` := proc(e, eqs)
  local m1, v, m2;
  m1, v, m2 := op(e);
  eval(op(0,e), eqs)(eval(m1, eqs), generic_evalat(v, m2, eqs))
end proc:

#############################################################################

# make gensym global, so that it can be shared with other 'global' routines
gensym := module()
  export ModuleApply;
  local gs_counter;
  gs_counter := 0;
  ModuleApply := proc(x::name)
    gs_counter := gs_counter + 1;
    x || gs_counter;
  end proc;
end module: # gensym

#############################################################################

NewSLO := module ()
  option package;
  local t_pw, unweight, factorize,
        recognize, get_de, recognize_de, Diffop, Recognized,
        step2, simp_weight, simp_pw, simp_Int, get_indicators,
        indicator, extract_dom, bind_late,
        piecewise_if, nub_piecewise, foldr_piecewise,
        verify_measure;
  export Integrand, applyintegrand, app, lam,
         Lebesgue, Uniform, Gaussian, Cauchy, BetaD, GammaD, StudentT,
         Ret, Bind, Msum, Weight, LO, Indicator,
         HakaruToLO, integrate, LOToHakaru, unintegrate,
         TestHakaru, measure, density,
         Simplify;

  t_pw := 'specfunc(piecewise)';

# An integrand h is either an Integrand (our own binding construct for a
# measurable function to be integrated) or something that can be applied
# (probably proc, which should be applied immediately, or a generated symbol).

# TODO evalapply/Integrand instead of applyintegrand?
# TODO evalapply/{Ret,Bind,...} instead of integrate?!

  applyintegrand := proc(h, x)
    if h :: 'Integrand(name, anything)' then
      eval(op(2,h), op(1,h) = x)
    elif h :: procedure then
      h(x)
    else
      'procname(_passed)'
    end if
  end proc;

# Step 1 of 3: from Hakaru to Maple LO (linear operator)

  HakaruToLO := proc(m)
    local h;
    h := gensym('h');
    LO(h, integrate(m, h))
  end proc;

  integrate := proc(m, h)
    local x, n, i;
    if m :: 'Lebesgue()' then
      x := gensym('xl');
      Int(applyintegrand(h, x),
          x=-infinity..infinity)
    elif m :: 'Uniform(anything, anything)' then
      x := gensym('xu');
      Int(applyintegrand(h, x) / (op(2,m)-op(1,m)),
          x=op(1,m)..op(2,m))
    elif m :: '{Gaussian(anything, anything),
                Cauchy  (anything, anything),
                StudentT(anything, anything, anything)}' then
      x := gensym('xg');
      Int(density[op(0,m)](op(m))(x) * applyintegrand(h, x),
          x=-infinity..infinity)
    elif m :: 'BetaD(anything, anything)' then
      x := gensym('xb');
      Int(density[op(0,m)](op(m))(x) * applyintegrand(h, x),
          x=0..1)
    elif m :: 'GammaD(anything, anything)' then
      x := gensym('xr');
      Int(density[op(0,m)](op(m))(x) * applyintegrand(h, x),
          x=0..infinity)
    elif m :: 'Ret(anything)' then
      applyintegrand(h, op(1,m))
    elif m :: 'Bind(anything, name, anything)' then
      integrate(op(1,m), z -> integrate(eval(op(3,m), op(2,m) = z), h))
    elif m :: 'specfunc(Msum)' then
      `+`(op(map(integrate, [op(m)], h)))
    elif m :: 'Weight(anything, anything)' then
      op(1,m) * integrate(op(2,m), h)
    elif m :: t_pw then
      n := nops(m);
      piecewise(seq(`if`(i::even or i=n, integrate(op(i,m), h), op(i,m)),
                    i=1..n))
    elif m :: 'LO(name, anything)' then
      eval(op(2,m), op(1,m) = h)
    elif h :: procedure then
      x := gensym('xa');
      'integrate'(m, Integrand(x, h(x)))
    else
      'procname(_passed)'
    end if
  end proc;

# Step 2 of 3: computer algebra

  Simplify := proc(lo :: LO(name, anything))
    LO(op(1,lo), step2(op(2,lo), op(1,lo), []))
  end proc;

  # Walk through integrals and simplify, recursing through grammar
  # h - name of the linear operator above us
  # constraints - domain information
  # TODO unify constraints with unintegrate's context
  step2 := proc(e, h :: name, constraints :: list)
    local subintegral, w, n, ee;

    if e :: Int(anything, name=anything) then
      # first step through the integrand
      ee := step2(op(1,e), h, [op(2,e), op(constraints)]);
      simp_Int(ee, op([2,1],e), op([2,2],e), h, constraints)
    elif e :: `+` then
      map(step2, e, h, constraints)
    elif e :: `*` then
      (subintegral, w) := selectremove(depends, e, h);
      if subintegral :: `*` then error "Nonlinear integral %1", e end if;
      simp_weight(w) * step2(subintegral, h, constraints)
    elif e :: t_pw then
      n := nops(e);
      ee := piecewise(seq(`if`(i::even or i=n,
                               step2(op(i,e), h, constraints),
                                 # TODO: update_context like unintegrate does
                               simplify(op(i,e))),
                          i=1..n));
      # big hammer: simplify knows about bound variables, amongst many
      # other things
      Testzero := x -> evalb(simplify(x) = 0);
      simp_pw(ee)
    else
      simplify(e)
    end if;
  end proc;

  # if a weight term is piecewise, then
  # 1. check if all its branches are equal, if so simplify
  # 2. check if it is in  fact an indicator function, and if so, convert
  simp_weight := proc(e)
    if e :: `*` then
      map(simp_weight, e)
    elif e :: `^` then
      applyop(simp_weight, 1, e)
    elif e :: t_pw then
      simp_pw(e)
    else
      simplify(e)
    end if
  end proc;

  simp_pw := proc(ee)
    local e;
    e := nub_piecewise(ee);
    if e :: t_pw then
      if nops(e) = 2 then
        return indicator(op(1,e)) * op(2,e)
      elif nops(e) = 3 and Testzero(op(2,e)) then
        return indicator(Not(op(1,e))) * op(3,e)
      elif nops(e) = 4 and Testzero(op(2,e)) then
        return indicator(And(Not(op(1,e)),op(3,e))) * op(4,e)
      end if
    end if;
    return e
  end proc;

  simp_Int := proc(e, var :: name, rng, h :: name, constraints :: list)
    local ee, hh, dom_spec, new_rng, rest;

    if depends(indets(e, 'applyintegrand'('identical'(h), anything)), var) then
      ee := NULL;
    else
      # try to eliminate unused var
      hh := gensym('h');
      ee := bind_late(LO(hh, int(applyintegrand(hh,var), var=rng)), var, h, e);
      if depends(ee, {int, MeijerG}) then
        # Maple was either not good enough or too good at integration
        ee := NULL
      end if
    end if;
    if ee = NULL then
      # if there are domain restrictions, try to apply them
      (dom_spec, ee) := get_indicators(e);
      (new_rng, dom_spec) := extract_dom(dom_spec, var);
      new_rng := map((b -> min(max(b, op(1,new_rng)), op(2,new_rng))), rng);
      if Testzero(op(2,new_rng)-op(1,new_rng)) then
        # trivial integration bounds
        ee := 0
      else
        (dom_spec, rest) := selectremove(depends, dom_spec, var);
        if dom_spec <> {} then ee := Indicator(dom_spec) * ee end if;
        ee := Int(ee, var=new_rng);
        if rest <> {} then ee := Indicator(rest) * ee end if;
      end if
    end if;
    ee
  end proc;

  get_indicators := proc(e)
    local sub, inds, rest;
    if e::`*` then
      sub := map((s -> [get_indicators(s)]), [op(e)]);
      `union`(op(map2(op,1,sub))), `*`(op(map2(op,2,sub)))
    elif e::`^` then
      inds, rest := get_indicators(op(1,e));
      inds, subsop(1=rest, e)
    elif e::'Indicator(set)' then
      op(1,e), 1
    else
      {}, e
    end if
  end proc;

  extract_dom := proc(spec :: set, v :: name)
    local lo, hi, i, rest;
    lo, rest := selectremove(type, spec, '{numeric <  identical(v),
                                           numeric <= identical(v)}');
    hi, rest := selectremove(type, rest, '{identical(v) <  numeric,
                                           identical(v) <= numeric}');
    max(map2(op,1,lo)) .. min(map2(op,2,hi)), rest;
  end proc;

  indicator := proc(b)
    local to_set, co_set;

    to_set := proc(a) # Make a set whose conjunction is equivalent to a
      if a :: '{specfunc(And), specop(anything, `and`)}' then
        map(op @ to_set, {op(a)})
      elif a :: 'And(specfunc(Not), anyfunc(anything))' then
        co_set(op(1,a))
      else
        {a}
      end if;
    end proc;

    co_set := proc(a) # Make a set whose conjunction is equivalent to Not(a)
      if a :: '{specfunc(Or), specop(anything, `or`)}' then
        map(op @ co_set, {op(a)})
      elif a :: 'And(specfunc(Not), anyfunc(anything))' then
        to_set(op(1,a))
      elif a :: 'anything < anything' then
        {op(1,a) >= op(2,a)}
      elif a :: 'anything <= anything' then
        {op(1,a) > op(2,a)}
      else
        {Not(a)}
      end if;
    end proc;

    Indicator(to_set(b))
  end proc;

  bind_late := proc(m, x :: name, h :: name, g)
    # LO(h, bind_late(m, x, h, g)) should be equivalent to Bind(m, x, LO(h, g))
    # but performs integration over x innermost rather than outermost.
    local guard, subintegral, w, y, yRename, lo, hi, mm;
    guard := proc(m, c) Bind(m, x, piecewise(c, Ret(x), Msum())) end proc;
    if g = 0 then
      0
    elif not depends(g, x) then
      value(integrate(m, x->1)) * g
    elif g :: `+` then
      map[4](bind_late, m, x, h, g)
    elif g :: `*` then
      (subintegral, w) := selectremove(depends, g, h);
      if subintegral :: `*` then error "Nonlinear integral %1", g end if;
      bind_late(Bind(m, x, Weight(w, Ret(x))), x, h, subintegral)
    elif g :: 'And'('specfunc({Int,int})',
                    'anyfunc'('anything','name'='range'('freeof'(h)))) then
      subintegral := op(1, g);
      y           := op([2,1], g);
      lo, hi      := op(op([2,2], g));
      if x = y or depends(m, y) then
        yRename     := gensym(y);
        subintegral := subs(y=yRename, subintegral);
        y           := yRename;
      end if;
      mm := m;
      if depends(lo, x) then mm := guard(mm, lo<y); lo := -infinity end if;
      if depends(hi, x) then mm := guard(mm, y<hi); hi :=  infinity end if;
      op(0,g)(bind_late(mm, x, h, subintegral), y=lo..hi)
    elif g :: t_pw then
      foldr_piecewise(
        proc(cond, th, el) proc(m)
          if depends(cond, x) then
            bind_late(guard(m, cond), x, h, th) + el(guard(m, Not(cond)))
          else
            piecewise_if(cond, bind_late(m, x, h, th), el(m))
          end if
        end proc end proc,
        proc(m) 0 end proc,
        g)(m)
    else
      value(integrate(m, Integrand(x, g)))
    end if
  end proc;

  piecewise_if := proc(cond, th, el)
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

  nub_piecewise := proc(pw) foldr_piecewise(piecewise_if, 0, pw) end proc;

  foldr_piecewise := proc(cons, nil, pw)
    # View pw as a piecewise and foldr over its arms
    if pw :: t_pw then
      foldr(proc(i,x) cons(op(i,pw), op(i+1,pw), x) end proc,
            `if`(nops(pw)::odd, cons(true, op(-1,pw), nil), nil),
            seq(1..nops(pw)-1, 2))
    else
      cons(true, pw, nil)
    end if
  end proc;

# Step 3 of 3: from Maple LO (linear operator) back to Hakaru

  Bind := proc(m, x, n)
    if n = 'Ret'(x) then
      m # monad law: right identity
    elif m :: 'Ret(anything)' then
      eval(n, x = op(1,m)) # monad law: left identity
    else
      'procname(_passed)'
    end if;
  end proc;

  Weight := proc(p, m)
    if p = 1 then
      m
    elif p = 0 then
      Msum()
    elif m :: 'Weight(anything, anything)' then
      Weight(p * op(1,m), op(2,m))
    else
      'procname(_passed)'
    end if;
  end proc;

  LOToHakaru := proc(lo :: LO(name, anything))
    local h;
    h := gensym(op(1,lo));
    unintegrate(h, eval(op(2,lo), op(1,lo) = h), [])
  end proc;

  unintegrate := proc(h :: name, integral, context :: list)
    local x, lo, hi, m, w, w0, recognition, subintegral,
          n, i, next_context, update_context;
    if integral :: 'And'('specfunc({Int,int})',
                         'anyfunc'('anything','name'='range'('freeof'(h)))) then
      x := gensym(op([2,1],integral));
      (lo, hi) := op(op([2,2],integral));
      next_context := [op(context), lo<x, x<hi];
      # TODO: enrich context with x (measure class lebesgue)
      subintegral := eval(op(1,integral), op([2,1],integral) = x);
      (w, m) := unweight(unintegrate(h, subintegral, next_context));
      recognition := recognize(w, x, lo, hi) assuming op(next_context);
      if recognition :: 'Recognized(anything, anything)' then
        # Recognition succeeded
        (w, w0) := factorize(op(2,recognition), x);
        Weight(w0, Bind(op(1,recognition), x, Weight(w, m)))
      else
        # Recognition failed
        (w, w0) := factorize(w, x);
        m := Weight(w, m);
        if hi <> infinity then
          m := piecewise(x < hi, m, Msum())
        end if;
        if lo <> -infinity then
          m := piecewise(lo < x, m, Msum())
        end if;
        Weight(w0, Bind(Lebesgue(), x, m))
      end if
    elif integral :: 'applyintegrand'('identical'(h), 'freeof'(h)) then
      Ret(op(2,integral))
    elif integral = 0 then
      Msum()
    elif integral :: `+` then
      Msum(op(map2(unintegrate, h, convert(integral, 'list'), context)))
    elif integral :: `*` then
      (subintegral, w) := selectremove(depends, integral, h);
      if subintegral :: `*` then error "Nonlinear integral %1", integral end if;
      Weight(w, unintegrate(h, subintegral, context))
    elif integral :: t_pw
         and `and`(seq(not (depends(op(i,integral), h)),
                       i=1..nops(integral)-1, 2)) then
      n := nops(integral);
      next_context := context;
      update_context := proc(c)
        local then_context;
        then_context := [op(next_context), c];
        next_context := [op(next_context), Not(c)]; # Mutation!
        then_context
      end proc;
      piecewise(seq(piecewise(i::even,
                              unintegrate(h, op(i,integral),
                                          update_context(op(i-1,integral))),
                              i=n,
                              unintegrate(h, op(i,integral), next_context),
                              op(i,integral)),
                    i=1..n))
    elif integral :: 'integrate'('freeof'(h), 'anything') then
      x := gensym('x');
      # TODO is there any way to enrich context in this case?
      Bind(op(1,integral), x,
           unintegrate(h, applyintegrand(op(2,integral), x), context))
    else
      # Failure: return residual LO
      LO(h, integral)
    end if
  end proc;

  app := proc (func, argu)
    if func :: lam(name, anything) then
      eval(op(2,func), op(1,func)=argu)
    else
      'procname(_passed)'
    end if
  end proc;

  unweight := proc(m)
    local unweights, total;
    if m :: 'Weight(anything, anything)' then
      op(m)
    elif m :: 'specfunc(Msum)' then
      total := `+`(op(map((mi -> unweight(mi)[1]), m)));
      (total, map((mi -> Weight(1/total, mi)), m))
    else
      # TODO: Better weight estimate for piecewise & density-recognition cases?
      (1, m)
    end if;
  end proc;

  factorize := proc(weight, x)
    # return (weight, 1); # uncomment this to disable factorization
    if weight :: `*` then
      selectremove(depends, weight, x)
    elif depends(weight, x) then
      (weight, 1)
    else
      (1, weight)
    end if
  end proc;

  recognize := proc(weight, x, lo, hi)
    local de, Dx, f, w, res, rng;
    res := FAIL;
    de := get_de(weight, x, Dx, f);
    if de :: 'Diffop(anything, anything)' then
      res := recognize_de(op(de), Dx, f, x, lo, hi)
    end if;
    if res = FAIL then
      rng := hi - lo;
      w := simplify(weight * (hi - lo));
      # weight could be piecewise and simplify will hide the problem
      if not (rng :: 'SymbolicInfinity' or w :: {'SymbolicInfinity', 'undefined'}) then
        res := Recognized(Uniform(lo, hi), w)
      end if
    end if;
    res
  end proc;

  get_de := proc(dens, var, Dx, f)
    :: Or(Diffop(anything, set(function=anything)), identical(FAIL));
    local de, init;
    try
      de := gfun[holexprtodiffeq](dens, f(var));
      de := gfun[diffeqtohomdiffeq](de, f(var));
      if not (de :: set) then
        de := {de}
      end if;
      init, de := selectremove(type, de, `=`);
      if nops(de) = 1 then
        if nops(init) = 0 then
          # TODO: Replace {0, 1/2, 1} by PyMC's distribution-specific "testval"
          init := map((val -> f(val) = eval(dens, var=val)), {0, 1/2, 1})
        end if;
        return Diffop(DEtools[de2diffop](de[1], f(var), [Dx, var]), init)
      end if
    catch: # do nothing
    end try;
    FAIL
  end proc;

  recognize_de := proc(diffop, init, Dx, f, var, lo, hi)
    local dist, ii, constraints, w, a0, a1, a, b0, b1, c0, c1, c2, loc, nu;
    dist := FAIL;
    if lo = -infinity and hi = infinity
       and ispoly(diffop, 'linear', Dx, 'a0', 'a1') then
      a := normal(a0/a1);
      if ispoly(a, 'linear', var, 'b0', 'b1') then
        dist := Gaussian(-b0/b1, sqrt(1/b1))
      elif ispoly(numer(a), 'linear', var, 'b0', 'b1') and
           ispoly(denom(a), 'quadratic', var, 'c0', 'c1', 'c2') then
        loc := -c1/c2/2;
        if Testzero(b0 + loc * b1) then
          nu := b1/c2 - 1;
          if Testzero(nu - 1) then
            dist := Cauchy(loc, sqrt(c0/c2-loc^2))
          else
            dist := StudentT(nu, loc, sqrt((c0/c2-loc^2)/nu))
          end if
        end if
      end if;
    elif lo = 0 and hi = 1
         and ispoly(diffop, 'linear', Dx, 'a0', 'a1')
         and ispoly(normal(a0*var*(1-var)/a1), 'linear', var, 'b0', 'b1') then
      dist := BetaD(1-b0, 1+b0+b1)
    elif lo = 0 and hi = infinity
         and ispoly(diffop, 'linear', Dx, 'a0', 'a1')
         and ispoly(normal(a0*var/a1), 'linear', var, 'b0', 'b1') then
      dist := GammaD(1-b0, 1/b1)
    end if;
    if dist <> FAIL then
      try
        ii := map(convert, init, 'diff');
        constraints := eval(ii, f = (x -> w*density[op(0,dist)](op(dist))(x)));
        w := eval(w, solve(simplify(constraints), w));
        if not (has(w, 'w')) then
          return Recognized(dist, w)
        end if
      catch: # do nothing
      end try;
      WARNING("recognized %1 as %2 but could not solve %3", f, dist, init)
    end if;
    FAIL
  end proc;

  density[Gaussian] := proc(mu, sigma) proc(x)
    1/sigma/sqrt(2)/sqrt(Pi)*exp(-(x-mu)^2/2/sigma^2)
  end proc end proc;
  density[Cauchy] := proc(loc, scale) proc(x)
    1/Pi/scale/(1+((x-loc)/scale)^2)
  end proc end proc;
  density[StudentT] := proc(nu, loc, scale) proc(x)
    GAMMA((nu+1)/2) / GAMMA(nu/2) / sqrt(Pi*nu) / scale
    * (1 + ((x-loc)/scale)^2/nu)^(-(nu+1)/2)
  end proc end proc;
  density[BetaD] := proc(a, b) proc(x)
    x^(a-1)*(1-x)^(b-1)/Beta(a,b)
  end proc end proc;
  # Hakaru uses the alternate definition of gamma, so the args are backwards
  density[GammaD] := proc(shape, scale) proc(x)
    x^(shape-1)/scale^shape*exp(-x/scale)/GAMMA(shape);
  end proc end proc;

# Testing

  TestHakaru := proc(m,n:=m,{simp:=Simplify})
    CodeTools[Test](LOToHakaru(simp(HakaruToLO(m))), n,
      measure({boolean,equal}), _rest)
  end proc;

  verify_measure := proc(m, n, v:='boolean')
    local mv, x, i, j, k;
    mv := measure(v);
    if verify(m, n, 'Bind'(mv, true, true)) then
      x := gensym(cat(op(2,m), "_", op(2,n), "_"));
      thisproc(subs(op(2,m)=x, op(3,m)),
               subs(op(2,n)=x, op(3,n)), v)
    elif m :: 'specfunc(Msum)' and n :: 'specfunc(Msum)'
         and nops(m) = nops(n) then
      k := nops(m);
      verify(k, GraphTheory[BipartiteMatching](GraphTheory[Graph]({
                seq(seq(`if`(thisproc(op(i,m), op(j,n), v), {i,-j}, NULL),
                        j=1..k), i=1..k)}))[1]);
    elif m :: t_pw and n :: t_pw and nops(m) = nops(n) then
      k := nops(m);
      verify(m, n, 'piecewise'(seq(`if`(i::even or i=k, mv, v), i=1..k)))
    elif m :: 'LO(name, anything)' and n :: 'LO(name, anything)' then
      x := gensym(cat(op(1,m), "_", op(1,n), "_"));
      verify(subs(op(1,m)=x, op(2,m)),
             subs(op(1,n)=x, op(2,n)), v)
    else
      verify(m, n, {v,
        Lebesgue(),
        Uniform(v, v),
        Gaussian(v, v),
        Cauchy(v, v),
        StudentT(v, v, v),
        BetaD(v, v),
        GammaD(v, v),
        Ret(mv),
        Weight(v, mv)
      })
    end if
  end proc;

  VerifyTools[AddVerification](measure = verify_measure);

end module; # NewSLO
