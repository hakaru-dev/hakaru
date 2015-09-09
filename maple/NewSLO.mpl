# we create 3 new binding forms.  Teach Maple (through depends and eval)
# about them.
# Both LO and Integrand bind from 1st arg to 2nd arg, whereas Bind
# binds from 2nd arg to 3rd arg.
`depends/LO` := proc(h, e, x)
  if member(h, x) then false else depends(e, x) end if
end proc:

`depends/Integrand` := proc(h, e, x)
  if member(h, x) then false else depends(e, x) end if
end proc:

# v should not occur in m1
`depends/Bind` := proc(m1, v, m2, x)
  if member(v, x) then false else depends(m1,x) or depends(m2, x) end if;
end proc:

# Warning: these eval routines are not "general"; there are various
# corner cases not handled.  This is not an issue, as they are only
# used internally, and those cases do not arise (by construction).
`eval/LO` := proc(e, eq1)
  local eqs, eq, changed, vv, lft, op_e, tmp, a;

  # boilerplate to deal with set/list input
  if eq1::list then eqs := {op(eq1)}
  elif eq1::set then eqs := eq1
  else error "unexpected input type for eval/LO"
  end if;

  changed := false;
  eq := remove(t -> op(1,t) = op(2,t), eqs);

  # figure out which equations to use
  vv := op(1,e); # the variable
  # split off renaming of the bound variable to a fresh name -- this is allowed!
  tmp, eq := selectremove(t -> (op(1,t) = vv) and op(2,t)::'And(name, Not(constant))'
                          and not depends(e, op(2,t)), eq);
  # split off [renaming the bound variable] or [variable-capture potential]
  lft, eq := selectremove(t -> op(1,t) = vv or (type(op(1, t), 'name') and
                          depends(op(2,t), vv)), eq);
  if nops(lft) = 0 then
    eq := eq union tmp; # put renaming of bound var back in
  end if;

  op_e := [op(e)];
  a := eval(op_e, eq);
  if a <> op_e then changed := true end if;
  # if things were split off
  if nops(lft) = 0 then
    'NewSLO:-LO'(op(a))
  else
    if changed then
      eval(NewSLO:-LO(op(a)), lft)
    else
      'eval'(e, lft)
    end if
  end if
end proc:

`eval/Integrand` := proc(e, eq1)
  local eqs, eq, changed, vv, lft, op_e, tmp, a;

  # boilerplate to deal with set/list input
  if eq1::list then eqs := {op(eq1)}
  elif eq1::set then eqs := eq1
  else error "unexpected input type for eval/Integrand"
  end if;

  changed := false;
  eq := remove(t -> op(1,t) = op(2,t), eqs);

  # figure out which equations to use
  vv := op(1,e); # the variable
  # split off renaming of the bound variable to a fresh name -- this is allowed!
  tmp, eq := selectremove(t -> (op(1,t) = vv) and op(2,t)::'And(name, Not(constant))'
                          and not depends(e, op(2,t)), eq);
  # split off [renaming the bound variable] or [variable-capture potential]
  lft, eq := selectremove(t -> op(1,t) = vv or (type(op(1, t), 'name') and
                          depends(op(2,t), vv)), eq);
  if nops(lft) = 0 then
    eq := eq union tmp; # put renaming of bound var back in
  end if;

  op_e := [op(e)];
  a := eval(op_e, eq);
  if a <> op_e then changed := true end if;
  # if things were split off
  if nops(lft) = 0 then
    'NewSLO:-Integrand'(op(a))
  else
    if changed then
      eval(NewSLO:-Integrand(op(a)), lft)
    else
      'eval'(e, lft)
    end if
  end if
end proc:

# this currently assumes/asserts that in Bind(a,b,c), depends(a,b) = false
`eval/Bind` := proc(e, eq1)
  local eqs, eq, changed, vv, lft, op_e, tmp, a;

  # boilerplate to deal with set/list input
  if eq1::list then eqs := {op(eq1)}
  elif eq1::set then eqs := eq1
  else error "unexpected input type for eval/Integrand"
  end if;

  if depends(op(1,e), op(2,e)) then error "unexpected dependence in Bind" end if;

  changed := false;
  eq := remove(t -> op(1,t) = op(2,t), eqs);

  # figure out which equations to use
  vv := op(2,e); # the variable
  # split off renaming of the bound variable to a fresh name -- this is allowed!
  tmp, eq := selectremove(t -> (op(1,t) = vv) and op(2,t)::'And(name, Not(constant))'
                          and not depends(e, op(2,t)), eq);
  # split off [renaming the bound variable] or [variable-capture potential]
  lft, eq := selectremove(t -> op(1,t) = vv or (type(op(1, t), 'name') and
                          depends(op(2,t), vv)), eq);
  if nops(lft) = 0 then
    eq := eq union tmp; # put renaming of bound var back in
  end if;

  op_e := [op(e)];
  a := eval(op_e, eq);
  if a <> op_e then changed := true end if;
  # if things were split off
  if nops(lft) = 0 then
    'NewSLO:-Bind'(op(a))
  else
    if changed then
      eval(NewSLO:-Bind(op(a)), lft)
    else
      'eval'(e, lft)
    end if
  end if
end proc:

#############################################################################

NewSLO := module ()
  option package;
  local t_pw, gensym, density, unweight, factorize,
        recognize, get_de, recognize_de, Diffop, Recognized,
        verify_measure;
  export Integrand, applyintegrand,
         Lebesgue, Uniform, Gaussian, Cauchy, BetaD, GammaD,
         Ret, Bind, Msum, Weight, LO,
         HakaruToLO, integrate, LOToHakaru, unintegrate,
         TestHakaru, measure;


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
    elif m :: 'Gaussian(anything, anything)' then
      x := gensym('xg');
      Int(density[op(0,m)](op(m))(x) * applyintegrand(h, x),
          x=-infinity..infinity)
    elif m :: 'Cauchy(anything, anything)' then
      x := gensym('xc');
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

# Step 2 of 3: algebra (currently nothing)

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
      next_context := [op(context), x::RealRange(Open(lo), Open(hi))];
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
      if subintegral :: `*` then
        error "Nonlinear integral %1", integral
      end if;
      Weight(w, unintegrate(h, subintegral, context))
    elif integral :: t_pw
         and `and`(seq(not (depends(op(i,integral), h)),
                       i=1..nops(integral)-1, 2)) then
      n := nops(integral);
      next_context := context;
      update_context := proc(c)
        local then_context;
        then_context := [op(next_context), c];
        next_context := [op(next_context), not c]; # Mutation!
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
    local de, Dx, f, w, res;
    res := FAIL;
    de := get_de(weight, x, Dx, f);
    if de :: 'Diffop(anything, anything)' then
      res := recognize_de(op(de), Dx, f, x, lo, hi)
    end if;
    if res = FAIL then
      w := simplify(weight * (hi - lo));
      if not (w :: {'SymbolicInfinity', 'undefined'}) then
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
          init := map((val -> f(val) = eval(dens, var=val)), {0, 1/2, 1})
        end if;
        return Diffop(DEtools[de2diffop](de[1], f(var), [Dx, var]), init)
      end if
    catch: # do nothing
    end try;
    FAIL
  end proc;

  recognize_de := proc(diffop, init, Dx, f, var, lo, hi)
    local dist, ii, constraints, w, a0, a1, a, b0, b1, c0, c1, c2, loc;
    dist := FAIL;
    if lo = -infinity and hi = infinity
       and ispoly(diffop, 'linear', Dx, 'a0', 'a1') then
      a := normal(a0/a1);
      if ispoly(a, 'linear', var, 'b0', 'b1') then
        dist := Gaussian(-b0/b1, sqrt(1/b1))
      elif ispoly(numer(a), 'linear', var, 'b0', 'b1') and
           ispoly(denom(a), 'quadratic', var, 'c0', 'c1', 'c2') then
        loc := -b0/b1;
        if Testzero(c1/c2 + 2*loc) then
          dist := Cauchy(loc, sqrt(c0/c2-loc^2))
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
      ii := map(convert, init, 'diff');
      constraints := eval(ii, f = (x -> w*density[op(0,dist)](op(dist))(x)));
      w := eval(w, solve(constraints, w));
      if not (has(w, 'w')) then
        return Recognized(dist, w)
      end if
    end if;
    FAIL
  end proc;

  density[Gaussian] := proc(mu, sigma) proc(x)
    1/sigma/sqrt(2)/sqrt(Pi)*exp(-(x-mu)^2/2/sigma^2)
  end proc end proc;
  density[Cauchy] := proc(loc,scale) proc(x)
    1/Pi/scale/(1+((x-loc)/scale)^2)
  end proc end proc;
  density[BetaD] := proc(a, b) proc(x)
    x^(a-1)*(1-x)^(b-1)/Beta(a,b)
  end proc end proc;
  # Hakaru uses the alternate definition of gamma, so the args are backwards
  density[GammaD] := proc(shape,scale) proc(x)
    x^(shape-1)/scale^shape*exp(-x/scale)/GAMMA(shape);
  end proc end proc;

# Testing

  TestHakaru := proc(m,n:=m,f:=(lo->lo))
    CodeTools[Test](LOToHakaru(f(HakaruToLO(m))), n, measure({boolean,equal}))
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
      for i to k do
        if not (thisproc(op(i,m), op(i,n), `if`(i::even or i=k, mv, v))) then
          return false
        end if
      end do;
      true
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
        BetaD(v, v),
        GammaD(v, v),
        Ret(mv),
        Weight(v, mv)
      })
    end if
  end proc;

  VerifyTools[AddVerification](measure = verify_measure);

  gensym := module()
    export ModuleApply;
    local gs_counter;
    gs_counter := 0;
    ModuleApply := proc(x::name)
      gs_counter := gs_counter + 1;
      x || gs_counter;
    end proc;
  end module; # gensym

end module; # NewSLO
