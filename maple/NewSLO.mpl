# We create 4 new binding forms.  Teach Maple (through depends and eval)
# about them.
# Integrand, LO, and lam bind from 1st arg to 2nd arg, whereas Bind
# binds from 2nd arg to 3rd arg.

`depends/Integrand` := proc(h, e, x) depends(e, x minus {h}) end proc:
`depends/LO`        := proc(h, e, x) depends(e, x minus {h}) end proc:
`depends/lam`       := proc(h, e, x) depends(e, x minus {h}) end proc:

# note that v _can_ occur in m1.
`depends/Bind` := proc(m1, v::name, m2, x)
  depends(m1, x) or depends(m2, x minus {v})
end proc:

# note that i _can_ occur in n.
`depends/ary` := proc(n, i::name, e, x)
  depends(n, x) or depends(e, x minus {i})
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

`eval/ary` := proc(e, eqs)
  local n, i, ee;
  n, i, ee := op(e);
  eval(op(0,e), eqs)(eval(n, eqs), generic_evalat(i, ee, eqs))
end proc:

#############################################################################

# make gensym global, so that it can be shared with other 'global' routines
gensym := module()
  export ModuleApply;
  local gs_counter, utf8, blocks, radix, unicode;
  gs_counter := -1;
  utf8 := proc(n :: integer)
    local m;
    if n<128 then n
    elif n<2048 then 192+iquo(n,64,'m'), 128+m
    elif n<65536 then 224+iquo(n,4096,'m'), 128+iquo(m,64,'m'), 128+m
    elif n<2097152 then 240+iquo(n,262144,'m'), 128+iquo(m,4096,'m'), 128+iquo(m,64,'m'), 128+m
    elif n<67108864 then 248+iquo(n,16777216,'m'), 128+iquo(m,262144,'m'), 128+iquo(m,4096,'m'), 128+iquo(m,64,'m'), 128+m
    elif n<2147483648 then 248+iquo(n,1073741824,'m'), 128+iquo(m,16777216,'m'), 128+iquo(m,262144,'m'), 128+iquo(m,4096,'m'), 128+iquo(m,64,'m'), 128+m
    end if
  end proc;
  blocks := map((b -> block(convert(op(0,b), decimal, hex), op(1,b))),
                ["4e00"(20950)]);
  radix := `+`(op(map2(op, 2, blocks))) / 2;
  unicode := proc(nn)
    local n, b;
    n := nn;
    for b in blocks do
      if n < op(2,b) then return n + op(1,b) else n := n - op(2,b) end if
    end do
  end proc;
  ModuleApply := proc(x::name)
    gs_counter := gs_counter + 1;
    cat(x, op(map(StringTools:-Char, map(utf8 @ unicode, applyop(`+`, 1, map(`*`, convert(gs_counter, 'base', radix), 2), 1)))))
  end proc;
end module: # gensym

#############################################################################

NewSLO := module ()
  option package;
  local t_pw, unweight, factorize,
        recognize, get_de, recognize_de, mysolve, Diffop, Recognized,
        reduce, simplify_assuming, reduce_pw, reduce_Int, get_indicators,
        indicator, extract_dom, banish, known_measures,
        myexpand_product,
        piecewise_if, nub_piecewise, foldr_piecewise,
        ModuleLoad, ModuleUnload, verify_measure,
        find_vars, find_constraints, interpret, reconstruct, invert, get_var_pos, 
        promote, change_var, disint2;
  export
     # note that these first few are smart constructors (for themselves):
         app, idx, integrate, applyintegrand,
     # while these are "proper functions"
         map_piecewise,
         bind, weight,
         plate, # TODO remove this one
         toLO, fromLO, unintegrate,
         RoundTripLO,
         TestHakaru, measure, density, bounds,
         improve, ReparamDetermined, determined, Reparam, Banish,
         disint;
  # these names are not assigned (and should not be).  But they are
  # used as global names, so document that here.
  global Bind, Weight, Ret, Msum, Integrand, Plate, LO, Indicator, ary,
         Lebesgue, Uniform, Gaussian, Cauchy, BetaD, GammaD, StudentT,
         lam;


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

  toLO := proc(m)
    local h;
    h := gensym('h');
#    LO(h, integrate(m, h))
     LO(h, integrate(eval(m, Plate=plate), h)) # for now
  end proc;

  known_measures := '{Lebesgue(), Uniform(anything, anything),
    Gaussian(anything, anything), Cauchy  (anything, anything),
    StudentT(anything, anything, anything),
    BetaD(anything, anything), GammaD(anything, anything)}':

  integrate := proc(m, h)
    local x, n, i;
    if m :: known_measures then
      x := 'xx';
      if h :: 'Integrand(name, anything)' then
        x := op(1,h);
      end if;
      x := gensym(x);
      Int(density[op(0,m)](op(m))(x) * applyintegrand(h, x),
        x = bounds[op(0,m)](op(m)));
    elif m :: 'Ret(anything)' then
      applyintegrand(h, op(1,m))
    elif m :: 'Bind(anything, name, anything)' then
      integrate(op(1,m), Integrand(op(2,m), integrate(op(3,m), h)))
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

  improve := proc(lo :: LO(name, anything))
    LO(op(1,lo), reduce(op(2,lo), op(1,lo), []))
  end proc;

  ReparamDetermined := proc(lo :: LO(name, anything))
    local h;
    h := op(1,lo);
    LO(h,
       evalindets(op(2,lo),
                  'And'('specfunc({Int,int})',
                        'anyfunc'(anything, 'name=anything')),
                  g -> `if`(determined(op(1,g),h), Reparam(g,h), g)))
  end proc;

  determined := proc(e, h :: name)
    local ints, i;
    ints := indets(e, 'specfunc({Int,int})');
    for i in ints do
      if hastype(IntegrationTools:-GetIntegrand(i),
           'applyintegrand'('identical'(h),
             'dependent'(IntegrationTools:-GetVariable(i)))) then
        return false
      end if
    end do;
    return true
  end proc;

  Reparam := proc(e :: Int(anything, name=anything), h :: name)
    'procname(_passed)' # TODO to be implemented
  end proc;

  Banish := proc(e :: Int(anything, name=anything), h :: name,
                 levels := infinity :: extended_numeric)
    local hh;
    hh := gensym('h');
    subs(int=Int,
      banish(LO(hh, int(applyintegrand(hh,op([2,1],e)), op(2,e))),
        op([2,1],e), h, op(1,e), levels));
  end proc;

  # Walk through integrals and simplify, recursing through grammar
  # h - name of the linear operator above us
  # constraints - domain information
  # TODO unify constraints with unintegrate's context
  reduce := proc(ee, h :: name, constraints :: list(name=anything))
    # option remember, system;
    local e, elim, hh, subintegral, w, n, i, x, myint;
    e := ee;

    while e :: Int(anything, name=anything) and not hastype(op(1,e),
       'applyintegrand'('identical'(h), 'dependent'(op([2,1],e)))) do
      # try to eliminate unused var
      hh := gensym('h');
      elim := eval(banish(LO(hh, myint(applyintegrand(hh,op([2,1],e)),op(2,e))),
                          op([2,1],e), h, op(1,e), infinity),
                   myint = proc(e,r)
                     subs(int=Int, simplify_assuming(int(e,r), constraints))
                   end proc);
      if has(elim, {MeijerG, undefined})
         or numboccur(elim,Int) >= numboccur(e,Int) then
        # Maple was too good at integration
        break;
      end if;
      e := elim;
    end do;

    if e :: Int(anything, name=anything) then
      reduce_Int(reduce(op(1,e), h, [op(2,e), op(constraints)]),
               op([2,1],e), op([2,2],e), h, constraints)
    elif e :: `+` then
      map(reduce, e, h, constraints)
    elif e :: `*` then
      (subintegral, w) := selectremove(depends, e, h);
      if subintegral :: `*` then error "Nonlinear integral %1", e end if;
      reduce_pw(simplify_assuming(w, constraints))
        * reduce(subintegral, h, constraints)
    elif e :: t_pw then
      n := nops(e);
      e := piecewise(seq(`if`(i::even or i=n,
                              reduce(op(i,e), h, constraints),
                                # TODO: update_context like unintegrate does
                              simplify_assuming(op(i,e), constraints)),
                         i=1..n));
      # big hammer: simplify knows about bound variables, amongst many
      # other things
      Testzero := x -> evalb(simplify(x) = 0);
      reduce_pw(e)
    elif e :: 'integrate(anything, Integrand(name, anything))' then
      x := gensym(op([2,1],e));
      # TODO is there any way to enrich constraints in this case?
      subsop(2=Integrand(x, reduce(subs(op([2,1],e)=x, op([2,2],e)),
                                   h, constraints)), e)
    else
      simplify_assuming(e, constraints)
    end if;
  end proc;

  simplify_assuming := proc(ee, constraints :: list(name=anything..anything))
    local f, e, ep;
    f := proc(c)
      local var, lo, hi;
      var := op(1,c);
      lo, hi := op(op(2,c));
      (var > lo, var < hi)
    end proc;
    e := evalindets(ee, 'specfunc(product)', myexpand_product);
    e := evalindets(e, 'specfunc(sum)', expand);
    e := simplify(e) assuming op(map(f, constraints));
    e := eval(e, exp = expand @ exp); # not sure if this is needed?
  end proc;

  reduce_pw := proc(ee) # ee may or may not be piecewise
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

  reduce_Int := proc(ee, var :: name, rng, h :: name, constraints :: list)
    local e, dom_spec, new_rng, rest, w;

    # if there are domain restrictions, try to apply them
    (dom_spec, e) := get_indicators(ee);
    if type(e, `*`) then
      (e, w) := selectremove(depends, e, var); # pull out weight
      w := simplify_assuming(w, constraints);
    else
      w := 1;
    end if;
    (new_rng, dom_spec) := extract_dom(dom_spec, var);
    new_rng := map((b -> min(max(b, op(1,new_rng)), op(2,new_rng))), rng);
    if Testzero(op(2,new_rng)-op(1,new_rng)) then
      # trivial integration bounds
      e := 0;
    else
      (dom_spec, rest) := selectremove(depends, dom_spec, var);
      # don't pull the w too far out (yet)
      if dom_spec <> {} then 
        e := Int(w*piecewise(And(op(dom_spec)), e, 0), var = new_rng);
      else
        e := Int(w*e, var=new_rng);
      end if;
      if rest <> {} then 
        # don't turn this into a piecewise yet!
        e := Indicator(rest)*e;
      end if;
    end if;
    e
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

  # TODO: generalize the patterns of lo/hi to also catch
  # numeric < numeric + positive*v
  # numeric + negative * v < numeric
  # as both being about 'lo', for example.
  extract_dom := proc(spec :: set, v :: name)
    local lo, hi, i, rest;
    lo, rest := selectremove(type, spec, '{numeric <  identical(v),
                                           numeric <= identical(v)}');
    hi, rest := selectremove(type, rest, '{identical(v) <  numeric,
                                           identical(v) <= numeric}');
    max(map2(op,1,lo)) .. min(map2(op,2,hi)), rest;
  end proc;

  indicator := module()
    export ModuleApply;
    local to_set, co_set;

    to_set := proc(a) # Make a set whose conjunction is equivalent to a
      local x;
      if a :: '{specfunc(And), specop(anything, `and`)}' then
        map(op @ to_set, {op(a)})
      elif a :: 'And(specfunc(Not), anyfunc(anything))' then
        co_set(op(1,a))
      elif a = true then
        {}
      elif a :: (('negint' &* 'name') < 'numeric') then
        {op([1,2],a) > op(2,a)/op([1,1],a)};
      elif a :: ((negint &* name) <= numeric) then
        {op([1,2],a) >= op(2,a)/op([1,1],a)};
      elif a :: (numeric < numeric &+ (negint &* name)) then
        {(op(1,a) - op([2,1],a))/op([2,2,1],a) > op([2,2,2],a)}
      elif a :: (numeric <= numeric &+ (negint &* name)) then
        {(op(1,a) - op([2,1],a))/op([2,2,1],a) >= op([2,2,2],a)}
      elif a :: (anything < identical(infinity)) then
        {}
      elif a :: (identical(-infinity) < anything) then
        {}
      elif a :: (numeric < name ^ identical(-1)) then
        x := op([2,1],a);
        {x < 1/op(1,a), x > 0}
      elif a :: (numeric <= name ^ identical(-1)) then
        x := op([2,1],a);
        {x <= 1/op(1,a), x > 0}
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
        to_set(op(1,a) >= op(2,a))
      elif a :: 'anything <= anything' then
        to_set(op(1,a) > op(2,a))
      elif a = false then
        {}
      elif a = true then
        {false}
      else
        {Not(a)}
      end if;
    end proc;

    ModuleApply := proc(b)
      Indicator(to_set(b))
    end proc;
  end module;

  banish := proc(m, x :: name, h :: name, g, levels :: extended_numeric)
    # LO(h, banish(m, x, h, g)) should be equivalent to Bind(m, x, LO(h, g))
    # but performs integration over x innermost rather than outermost.
    local guard, subintegral, w, y, yRename, lo, hi, mm;
    guard := proc(m, c) bind(m, x, piecewise(c, Ret(x), Msum())) end proc;
    if g = 0 then
      0
    elif levels <= 0 then
      integrate(m, Integrand(x, g))
    elif not depends(g, x) then
      integrate(m, x->1) * g
    elif g :: `+` then
      map[4](banish, m, x, h, g, levels)
    elif g :: `*` then
      (subintegral, w) := selectremove(depends, g, h);
      if subintegral :: `*` then error "Nonlinear integral %1", g end if;
      banish(bind(m, x, weight(w, Ret(x))), x, h, subintegral, levels)
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
      op(0,g)(banish(mm, x, h, subintegral, levels-1), y=lo..hi)
    elif g :: t_pw then
      foldr_piecewise(
        proc(cond, th, el) proc(m)
          if depends(cond, x) then
            banish(guard(m, cond), x, h, th, levels-1) + el(guard(m, Not(cond)))
          else
            piecewise_if(cond, banish(m, x, h, th, levels-1), el(m))
          end if
        end proc end proc,
        proc(m) 0 end proc,
        g)(m)
    elif g :: 'integrate(freeof(x), Integrand(name, anything))' then
      y := gensym(op([2,1],g));
      subsop(2=Integrand(y, banish(m, x, h,
        subs(op([2,1],g)=y, op([2,2],g)), levels-1)), g)
    else
      integrate(m, Integrand(x, g))
    end if
  end proc;

  # this code should not currently be used, it is just a snapshot in time
  Reparam := proc(e::Int(anything,name=range), h::name)
    local body, var, inds, xx, inv, new_e;

    # TODO improve the checks.
    if not has(body, {Int,int}) and hastype(e,'specfunc(applyintegrand)') then
      inds := indets(body, 'applyintegrand'('identical'(h), 'dependent'(var)));
      if nops(inds)=1 and op(2,inds[1]) :: algebraic and
         not hastype(body, t_pw) then
        xx := gensym('xx');
        inv := solve({op(2,inds[1])=xx}, {var});
        try
          new_e := IntegrationTools[Change](e, inv, xx);
          if not has(new_e,{'limit'}) then e := new_e end if;
        catch:
          # this will simply not change e
        end try;
      end if;
    end if;

    e;
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

  nub_piecewise := proc(pw) # pw may or may not be piecewise
    foldr_piecewise(piecewise_if, 0, pw)
  end proc;

  foldr_piecewise := proc(cons, nil, pw) # pw may or may not be piecewise
    # View pw as a piecewise and foldr over its arms
    if pw :: t_pw then
      foldr(proc(i,x) cons(op(i,pw), op(i+1,pw), x) end proc,
            `if`(nops(pw)::odd, cons(true, op(-1,pw), nil), nil),
            seq(1..nops(pw)-1, 2))
    else
      cons(true, pw, nil)
    end if
  end proc;

  map_piecewise := proc(f,p)
    local i;
    if p :: t_pw then
      piecewise(seq(`if`(i::even or i=nops(p),f(op(i,p),_rest),op(i,p)),i=1..nops(p)))
    else
      f(p,_rest)
    end if
  end proc;

# Step 3 of 3: from Maple LO (linear operator) back to Hakaru

  fromLO := proc(lo :: LO(name, anything))
    local h;
    h := gensym(op(1,lo));
    unintegrate(h, eval(op(2,lo), op(1,lo) = h), [])
  end proc;

  unintegrate := proc(h :: name, integral, context :: list)
    local x, lo, hi, m, mm, w, w0, recognition, subintegral,
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
        weight(w0, bind(op(1,recognition), x, weight(w, m)))
      else
        # Recognition failed
        (w, w0) := factorize(w, x);
        m := weight(w, m);
        if hi <> infinity then
          m := piecewise(x < hi, m, Msum())
        end if;
        if lo <> -infinity then
          m := piecewise(lo < x, m, Msum())
        end if;
        weight(w0, bind(Lebesgue(), x, m))
      end if
#    elif integral :: 'ProductIntegral(anything, anything, name = range, name, name)' then
#      x := gensym(op([3,1,0], integral));
#      (lo, hi) := op(op([3,2], integral));
#      next_context := [op(context), lo<x, x<hi];
#      w := eval(op(1,integral), op([3,1],integral) = x);
#      m := unintegrate(h, op(2,integral), context);
#      recognition := recognize(w, x, lo, hi) assuming op(next_context);
#      if recognition :: 'Recognized(anything, anything)' then
#        # Recognition succeeded
#        mm := weight(op(2,recognition), op(1,recognition));
#        bind(Plate(ary(op(4,integral), op(5, integral), mm)), op([3,1],integral), m);
#      else
#        error "case not done yet in unintegrate of ProductIntegral"
#      end if;
    elif integral :: 'applyintegrand'('identical'(h), 'freeof'(h)) then
      Ret(op(2,integral))
    elif integral = 0 then
      Msum()
    elif integral :: `+` then
      Msum(op(map2(unintegrate, h, convert(integral, 'list'), context)))
    elif integral :: `*` then
      (subintegral, w) := selectremove(depends, integral, h);

      if subintegral :: `*` then error "Nonlinear integral %1", integral end if;
      weight(w, unintegrate(h, subintegral, context))
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
      x := 'x';
      if op(2,integral) :: 'Integrand(name, anything)' then
        x := op([2,1],integral);
      end if;
      x := gensym(x);
      # TODO is there any way to enrich context in this case?
      (w, m) := unweight(unintegrate(h, applyintegrand(op(2,integral), x),
                                     context));
      (w, w0) := factorize(w, x);
      weight(w0, bind(op(1,integral), x, weight(w, m)))
    else
      # Failure: return residual LO
      LO(h, integral)
    end if
  end proc;

  ###
  # prototype disintegrator - main entry point
  disint := proc(lo :: LO(name,anything), t::name)
    local h, integ, occurs, oper_call, ret, var, plan;
    h := gensym(op(1,lo));
    integ := eval(op(2,lo), op(1,lo) = h);
    map2(LO, h, disint2(integ, h, t, []));
  end proc;

  find_vars := proc(l)
    map(proc(x) 
          if type(x, specfunc(%int)) then op([1,1],x)
          elif type(x, specfunc(%weight)) then NULL
          else error "don't know about command (%1)", x
          end if end proc,
         l);
  end proc;

  find_constraints := proc(l)
    map(proc(x) 
          if type(x, specfunc(%int)) then op(1,x)
          elif type(x, specfunc(%weight)) then NULL
          else error "don't know about command (%1)", x
          end if end proc,
         l);
  end proc;

  # only care about bound variables, not globals
  get_var_pos := proc(v, l)
    local p;
    if member(v, l, 'p') then VarPos(v,p) else NULL end if;
  end proc;

  invert := proc(to_invert, main_var, integral, h, path, t)
    local sol, dxdt, vars, in_sol, r_in_sol, p_mv, to_promote, flip;
    if type(to_invert, 'linear'(main_var)) then
      sol := solve([t = to_invert], {main_var})[1];

    else
      # TODO: split domain.
      # right now, assume that if solve returns a single answer, it's ok!
      sol := solve([t = to_invert], {main_var});
      if not (nops(sol) = 1) then
        error "non-linear inversion needed: %1 over %2", to_invert, main_var;
      else
        sol := sol[1];
      end if;
    end if;

    dxdt := diff(op(2, sol), t);
    flip := simplify_assuming(signum(dxdt), 
      [t = -infinity .. infinity, op(find_constraints(path))]);
    if not member(flip, {1,-1}) then
      error "derivative has symbolic sign (%1), what do we do?", flip
    end if;

    # we need to figure out what variables the solution depends on,
    # and what plan that entails
    vars := find_vars(path);
    in_sol := indets(sol, 'name') minus {t, main_var};
    
    member(main_var, vars, 'p_mv');
    r_in_sol := map(get_var_pos, in_sol, vars);
    to_promote := map(x -> `if`(op(2,x)>p_mv, x, NULL), r_in_sol);
    # may have to do a bunch of promotions, or none
    interpret(
      [ %Promote(seq(VPP(op(i),p_mv), i in to_promote))
      , %Change(main_var, t = to_invert, sol, flip)
      , %ToTop(t)
      , %Drop(t)],
      path, abs(dxdt) * 'applyintegrand'(h, eval(op([2,2],integral), sol)));
  end proc;

  # basic algorithm:
  # - follow the syntax
  # - collect the 'path' traversed (aka the "heap"); allows reconstruction
  # - when we hit a Ret, figure out the change of variables
  # - note that the callee is responsible for "finishing up"
  disint2 := proc(integral, h::name, t::name, path)
    local x, lo, hi, subintegral, w, n, m, w0, perform, script, vars,
      to_invert, sol, occurs, dxdt, next_context, update_context;
    if integral :: 'And'('specfunc({Int,int})',
                         'anyfunc'('anything','name'='range'('freeof'(h)))) then
      x := op([2,1],integral);
      (lo, hi) := op(op([2,2],integral));
      perform := %int(op(2,integral));
      # TODO: enrich context with x (measure class lebesgue)
      disint2(op(1,integral), h, t, [perform, op(path)]);
    elif integral :: 'applyintegrand'('identical'(h), 'freeof'(h)) then
      if not type(op(2,integral), specfunc(Pair)) then
        # this should probably be type-checked at the top!
        error "must return a Pair to enable disintegration";
      end if;
      to_invert := op([2,1], integral);
      vars := convert(find_vars(path),'set');
      occurs := remove(type, indets(to_invert, 'name'), 'constant') intersect vars;
      if nops(occurs) = 0 then
        error "cannot invert constant (%1)", to_invert
      else
        map[2](invert, to_invert, occurs, integral, h, path, t);
      end if;
    elif integral = 0 then
      error "cannot disintegrate 0 measure"
    elif integral :: `+` then
      error "need to split on a `+`"
      # Msum(op(map2(unintegrate, h, convert(integral, 'list'), context)))
    elif integral :: `*` then
      (subintegral, w) := selectremove(depends, integral, h);
      if subintegral :: `*` then error "Nonlinear integral %1", integral end if;
      disint2(subintegral, h, t, [%weight(w), op(path)]);
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
      error "need to map into piecewise";
      piecewise(seq(piecewise(i::even,
                              unintegrate(h, op(i,integral),
                                          update_context(op(i-1,integral))),
                              i=n,
                              unintegrate(h, op(i,integral), next_context),
                              op(i,integral)),
                    i=1..n))
    elif integral :: 'integrate'('freeof'(h), 'anything') then
      x := 'x';
      if op(2,integral) :: 'Integrand(name, anything)' then
        x := op([2,1],integral);
      end if;
      x := gensym(x);
      # we would be here mostly if the measure being passed in is
      # not known.  So error is fine, and should likely be caught
      # elsewhere
      error "what to do with (%1)", integral;
      # TODO is there any way to enrich context in this case?
      (w, m) := unweight(unintegrate(h, applyintegrand(op(2,integral), x),
                                     context));
      (w, w0) := factorize(w, x);
      weight(w0, bind(op(1,integral), x, weight(w, m)))
    else
      # Failure
      # LO(h, integral)
      error "why are we here?";
    end if
  end proc;

  # single step of reconstruction
  reconstruct := proc(step, part)
    if type(step, specfunc(%int)) then
      Int(part, op(1, step));
    elif type(step, specfunc(%weight)) then
      op(1, step) * part
    else
      error "how to reconstruct (%1)", step
    end if;
  end proc;

  change_var := proc(act, chg, path, part)
    local bds, new_upper, new_lower, new_path, flip;

    # check if the *outermost* integral is the 'good' one
    if type(path[-1], specfunc(%int)) then
      if op(1, act) = op([-1,1,1], path) then
        new_path := eval(path[1..-2], op(3,act));
	bds := op([-1,1,2], path);
	new_upper := limit(op([2,2], act), op(1, act) = op(2,bds), left);
	new_lower := limit(op([2,2], act), op(1, act) = op(1,bds), right);
	flip := op(4,act);
	if flip=-1 then
	  (new_lower, new_upper) := (new_upper, new_lower);
	end if;
	if new_upper = infinity and new_lower = -infinity then
	  # we're done with this integral, put it back on path
	  interpret(chg, [op(new_path), %int(t = -infinity..infinity)], part)
	else
          # right now, putting in new constraints "innermost", while
          # they really ought to be floated up as far as possible.
          # Probably leave that to improve?
	  interpret(chg, [op(new_path),%int(t=new_lower..new_upper)],
	    piecewise(And(new_lower < t, t < new_upper), part, 0));
	end if;
      else
        error "Outer integral is not the one we want!";
	# interpret(chg, new_path, Int(part, op([-1,1], path)));
      end if;
    else
      error "%Change"
    end if;
  end proc;

  promote := proc(promotions, chg, path, part)
    local x, p, ref, i1, i2, vars, danger, new_path;
    if nops(promotions)=0 then # nothing to do, next
      interpret(chg, path, part)
    elif nops(promotions)>1 then
      error "multiple promotions (%1) not yet implemented", promotions;
    else
      # move variable x, at position p, above that at position ref.
      (x, p, ref) := op(op(1,promotions));
      i1 := path[p];
      i2 := path[ref];
      # need to make sure these don't escape their scope:
      vars := find_vars(path[ref .. p-1]);
      danger := indets(op([1,2], i1), 'name') intersect {op(vars)};
      if danger = {} then
	# just go ahead
	new_path := [op(1..ref-1, path), i1, op(ref..p-1,path),
	  op(p+1..-1, path)];
	interpret(chg, new_path, part);
      else
	# need to internalize bounds as Indicator
	error "Promote %1 over %2 must take care of %3", chg[1], vars, danger;
      end if;
    end if;
  end proc;

  # interpret a plan
  # chg : plan of what needs to be done
  # path : context, allows one to reconstruct the incoming expression
  # part: partial answer
  interpret := proc(chg, path, part)
    local i, ans;
    if path=[] then part
    elif chg=[] then # finished changes, just reconstruct
      ans := part;
      for i from 1 to nops(path) do
        ans := reconstruct(path[i], ans);
      end do;
      return ans;
    elif type(chg[1], specfunc(%Change)) then
      change_var(chg[1], chg[2..-1], path, part);
    elif type(chg[1], specfunc(%Promote)) then
      promote(chg[1], chg[2..-1], path, part);
    elif type(chg[1], specfunc(%ToTop)) then
      if type(path[-1], specfunc(%int)) and op([-1,1,1], path) = op([1,1], chg) then
        interpret(chg[2..-1], path, part)
      else
        error "must float t-integral to top"
      end if;
    elif type(chg[1], specfunc(%Drop)) then
      if type(path[-1], specfunc(%int)) and op([-1,1,1], path) = op([1,1], chg) then
        interpret(chg[2..-1], path[1..-2], part)
      else
        error "asked to drop t-integral, but it is not at top"
      end if;
    else
      error "unknown plan step: %1", chg[1]
    end if;
  end proc;
  ###
  # smart constructors for our language

  bind := proc(m, x, n)
    if n = 'Ret'(x) then
      m # monad law: right identity
    elif m :: 'Ret(anything)' then
      eval(n, x = op(1,m)) # monad law: left identity
    else
      'Bind(_passed)'
    end if;
  end proc;

  weight := proc(p, m)
    if p = 1 then
      m
    elif p = 0 then
      Msum()
    elif m :: 'Weight(anything, anything)' then
      weight(p * op(1,m), op(2,m))
    else
      'Weight(_passed)'
    end if;
  end proc;

  # TODO: remove this 'smart constructor'!
  plate := proc(a)
    local xs, w, m;
    if a :: 'ary(anything, name, Ret(anything))' then
      Ret(ary(op(1,a), op(2,a), op([3,1],a)))
    elif a :: 'ary(anything, name, Bind(anything, name, anything))' then
      xs := gensym(op([3,2],a));
      bind(plate(ary(op(1,a), op(2,a), op([3,1],a))), xs,
           plate(ary(op(1,a), op(2,a),
                 eval(op([3,3],a), op([3,2],a)=idx(xs,op(2,a))))))
    elif a :: 'ary(anything, name, anything)' then
      (w, m) := unweight(op(3,a));
      if w <> 1 then
        weight(product(w, op(2,a)=1..op(1,a)), plate(ary(op(1,a), op(2,a), m)))
      else
        'Plate(_passed)'
      end if
    else
      'Plate(_passed)'
    end if;
  end proc;

  app := proc (func, argu)
    if func :: lam(name, anything) then
      eval(op(2,func), op(1,func)=argu)
    elif func :: t_pw then
      map_piecewise(procname, _passed)
    else
      'procname(_passed)'
    end if
  end proc;

  idx := proc (a, i)
    if a :: ary(anything, name, anything) then
      eval(op(3,a), op(2,a)=i)
    elif a :: t_pw then
      map_piecewise(procname, _passed)
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
      (total, map((mi -> weight(1/total, mi)), m))
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

  recognize := proc(weight0, x, lo, hi)
    local Constant, weight, de, Dx, f, w, res, rng;
    res := FAIL;
    # gfun[holexprtodiffeq] contains a test for {radfun,algfun} that seems like
    # it should test for {radfun(anything,x),algfun(anything,x)} instead.
    # Consequently, it issues the error "expression is not holonomic: %1" for
    # actually holonomic expressions such as exp(x*sum(g(i,j),j=1..n)).
    # Moreover, mysolve has trouble solve-ing constraints involving sum, etc.
    # To work around these weaknesses, we wrap sum(...), etc. in Constant[...].
    # Unlike sum(...), Constant[sum(...)] passes the type test {radfun,algfun},
    # which we need to handle exp(x*sum(...)) using gfun[holexprtodiffeq].
    # Like sum(...i...), Constant[sum(...i...)] depends on i, which we need so
    # that product(sum(...i...),i=1..m) doesn't simplify to ...^m.
    weight := evalindets[flat](weight0,
                And(# Not(radfun), Not(algfun),
                    'specfunc({product, sum, idx})',
                    'freeof'(x)),
                proc(e) Constant[e] end);
    de := get_de(weight, x, Dx, f);
    if de :: 'Diffop(anything, anything)' then
      res := recognize_de(op(de), Dx, f, x, lo, hi)
    end if;
    if res = FAIL then
      rng := hi - lo;
      w := simplify(weight * (hi - lo));
      # weight could be piecewise and simplify will hide the problem
      if not (rng :: 'SymbolicInfinity'
              or w :: {'SymbolicInfinity', 'undefined'}) then
        res := Recognized(Uniform(lo, hi), w)
      end if
    end if;
    # Undo Constant[...] wrapping
    evalindets[flat](res, 'specindex'(anything, Constant), x -> op(1,x))
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
          init := map(proc (val)
                        try f(val) = eval(dens, var=val)
                        catch: NULL
                        end try
                      end proc,
                      {0, 1/2, 1})
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
        w := eval(w, mysolve(simplify(constraints), w));
        if not (has(w, 'w')) then
          return Recognized(dist, simplify(w))
        end if
      catch: # do nothing
      end try;
      WARNING("recognized %1 as %2 but could not solve %3", f, dist, init)
    end if;
    FAIL
  end proc;

  mysolve := proc(constraints)
    # This wrapper around "solve" works around the problem that Maple sometimes
    # thinks there is no solution to a set of constraints because it doesn't
    # recognize the solution to each constraint is the same.  For example--
    # This fails     : solve({c*2^(-1/2-alpha) = sqrt(2)/2, c*4^(-alpha) = 2^(-alpha)}, {c}) assuming alpha>0;
    # This also fails: solve(simplify({c*2^(-1/2-alpha) = sqrt(2)/2, c*4^(-alpha) = 2^(-alpha)}), {c}) assuming alpha>0;
    # But this works : map(solve, {c*2^(-1/2-alpha) = sqrt(2)/2, c*4^(-alpha) = 2^(-alpha)}, {c}) assuming alpha>0;
    # And the difference of the two solutions returned simplifies to zero.

    local result;
    if nops(constraints) = 0 then return NULL end if;
    result := solve(constraints, _rest);
    if result <> NULL or not (constraints :: {set,list}) then
      return result
    end if;
    result := mysolve(subsop(1=NULL,constraints), _rest);
    if result <> NULL
       and op(1,constraints) :: 'anything=anything'
       and simplify(eval(op([1,1],constraints) - op([1,2],constraints),
                         result)) <> 0 then
      return NULL
    end if;
    result
  end proc;

  myexpand_product := proc(prod)
    local x, p, body, quantifier;
    (body, quantifier) := op(prod);
    x := op(1, quantifier);
    p := proc(e)
      local ee;
      if e :: 'exp(anything)' then
        ee := expand(op(1,e));
        ee := convert(ee, 'list', `+`);
        `*`(op(map(z -> exp(sum(z, quantifier)), ee)));
      elif e :: ('freeof'(x) ^ 'anything') then
        op(1,e) ^ expand(sum(op(2,e), quantifier))
      elif e :: ('anything' ^ 'freeof'(x)) then
        p(op(1,e)) ^ op(2,e)
      else
        product(e, quantifier)
      end if
    end proc;
    `*`(op(map(p, convert(body, list, `*`))));
  end proc;

  density[Lebesgue] := proc() proc(x) 1 end proc end proc;
  density[Uniform] := proc(a,b) proc(x)
    1/(b-a)
  end proc end proc;
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

  bounds[Lebesgue] := proc() -infinity .. infinity end proc;
  bounds[Uniform] := proc(a, b) a .. b end proc;
  bounds[Gaussian] := proc(mu, sigma) -infinity .. infinity end proc;
  bounds[Cauchy] := proc(loc, scale) -infinity .. infinity end proc;
  bounds[StudentT] := proc(mu, sigma) -infinity .. infinity end proc;
  bounds[BetaD] := proc(nu, loc, scale) 0 .. 1 end proc;
  bounds[GammaD] := proc(a, b) 0 .. infinity end proc;

  RoundTripLO := proc(m)
      lprint(eval(ToInert(fromLO(improve(toLO(m)))), _Inert_ATTRIBUTE=NULL))
  end proc;

# Testing

  TestHakaru := proc(m,n::algebraic:=m,{simp:=improve,verify:=simplify})
    CodeTools[Test](fromLO(simp(toLO(m))), n,
      measure(verify), _rest)
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

  ModuleLoad := proc()
    VerifyTools[AddVerification](measure = verify_measure);
  end proc;

  ModuleUnload := proc()
    VerifyTools[RemoveVerification](measure);
  end proc;

  ModuleLoad();

end module; # NewSLO
