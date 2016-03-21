# Teach Maple (through depends and eval) about our new binding forms.
# Integrand, LO, and lam bind from 1st arg to 2nd arg.
# Branch binds from 1st arg (a pattern) to 2nd arg.
# Bind and ary bind from 2nd arg to 3rd arg.

`depends/Integrand` := proc(v, e, x) depends(e, x minus {v}) end proc:
`depends/LO`        := proc(v, e, x) depends(e, x minus {v}) end proc:
`depends/lam`       := proc(v, e, x) depends(e, x minus {v}) end proc:

`depends/Branch`    := proc(p, e, x) depends(e, x minus {pattern_binds(p)}) end proc:
pattern_binds := proc(p)
  if p = PWild or p = PDone then
    NULL
  elif p :: PVar(anything) then
    op(1,p)
  elif p :: PDatum(anything, anything) then
    pattern_binds(op(2,p))
  elif p :: {PInl(anything), PInr(anything),
             PKonst(anything), PIdent(anything)} then
    pattern_binds(op(1,p))
  elif p :: PEt(anything, anything) then
    pattern_binds(op(1,p)), pattern_binds(op(2,p))
  else
    error "pattern_binds: %1 is not a pattern", p
  end if
end proc:

# note that v _can_ occur in m1.
`depends/Bind` := proc(m1, v::name, m2, x)
  depends(m1, x) or depends(m2, x minus {v})
end proc:

# note that i _can_ occur in n.
`depends/ary` := proc(n, i::name, e, x)
  depends(n, x) or depends(e, x minus {i})
end proc:

generic_evalat := proc(vv::{name,list(name)}, mm, eqs)
  local v, m, eqsRemain, subsEq, eq, rename, funs;
  funs := map2(op, 0, indets(mm, 'function'));
  eqsRemain := remove((eq -> op(1,eq) = op(2,eq)), eqs);
  eqsRemain, subsEq := selectremove((eq -> type(op(1,eq), 'name')), eqsRemain);
  eqsRemain := select((eq -> not has(op(1,eq), vv) and
    (depends(mm, op(1,eq)) or member(op(1,eq), funs))), eqsRemain);
  m := mm;
  rename := proc(v::name)
    local vRename;
    if depends(eqsRemain, v) then
      vRename := gensym(v);
      m := subs(v=vRename, m);
      vRename
    else
      v
    end if
  end proc;
  if vv :: name then
    v := rename(vv)
  else
    v := map(rename, vv);
  end if;
  m := subs(subsEq,m);
  if nops(eqsRemain) > 0 then
    m := eval(m,eqsRemain);
  end if;
  v, m;
end proc:

`eval/Integrand` := proc(e, eqs)
  local v, ee;
  v, ee := op(e);
  eval(op(0,e), eqs)(generic_evalat(v, ee, eqs))
end proc:

`eval/LO` := proc(e, eqs)
  local v, ee;
  v, ee := op(e);
  eval(op(0,e), eqs)(generic_evalat(v, ee, eqs))
end proc:

`eval/lam` := proc(e, eqs)
  local v, ee;
  v, ee := op(e);
  eval(op(0,e), eqs)(generic_evalat(v, ee, eqs))
end proc:

`eval/Branch` := proc(e, eqs)
  local p, ee, vBefore, vAfter;
  p, ee := op(e);
  vBefore := [pattern_binds(p)];
  vAfter, ee := generic_evalat(vBefore, ee, eqs);
  eval(op(0,e), eqs)(subs(op(zip(`=`, vBefore, vAfter)), p), ee)
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
  local t_pw, t_case, p_true, p_false,
        unweight, factorize, pattern_match, make_piece,
        recognize, get_de, recognize_de, mysolve, Diffop, Recognized,
        reduce, to_assumption, simplify_assuming, convert_piecewise,
        reduce_pw, reduce_Int, get_indicators,
        integrate_ary,
        flip_cond,
        reduce_PI, elim_int,
        indicator, extract_dom, banish, known_measures,
        myexpand_product,
        piecewise_if, nub_piecewise, foldr_piecewise,
        ModuleLoad, ModuleUnload, verify_measure,
        find_vars, find_constraints, interpret, reconstruct, invert, 
        get_var_pos, get_int_pos,
        avoid_capture, change_var, disint2;
  export
     # note that these first few are smart constructors (for themselves):
         case, app, idx, integrate, applyintegrand,
     # while these are "proper functions"
         map_piecewise,
         bind, weight,
         toLO, fromLO, improve,
         RoundTripLO, RoundTripCLO,
         toCLO, fromCLO, cimprove,
         TestHakaru, measure, density, bounds,
         unintegrate,
         ReparamDetermined, determined, Reparam, Banish,
         disint;
  # these names are not assigned (and should not be).  But they are
  # used as global names, so document that here.
  global Bind, Weight, Ret, Msum, Integrand, Plate, LO, Indicator, ary,
         Lebesgue, Uniform, Gaussian, Cauchy, BetaD, GammaD, StudentT,
         Context, t_ctx,
         lam,
         Datum, Inr, Inl, Et, Done, Konst, Ident,
         Branches, Branch, PWild, PVar, PDatum, PInr, PInl, PEt, PDone, PKonst, PIdent;

  t_pw    := 'specfunc(piecewise)';
  t_case  := 'case(anything, specfunc(Branch(anything, anything), Branches))';
  p_true  := 'PDatum(true,PInl(PDone))';
  p_false := 'PDatum(false,PInr(PInl(PDone)))';

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
    LO(h, integrate(m, h))
  end proc;

  # toLO does not use the context, so just map in
  toCLO := proc(c :: Context(list(t_ctx), anything))
    Context(op(1,c), toLO(op(2,c)));
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
      integrate(op(1,m), eval(Integrand(op(2,m), 'integrate'(op(3,m), x)), x=h))
    elif m :: 'specfunc(Msum)' then
      `+`(op(map(integrate, [op(m)], h)))
    elif m :: 'Weight(anything, anything)' then
      op(1,m) * integrate(op(2,m), h)
    elif m :: t_pw then
      n := nops(m);
      piecewise(seq(`if`(i::even or i=n, integrate(op(i,m), h), op(i,m)),
                    i=1..n))
    elif m :: t_case then
      subsop(2=map(proc(b :: Branch(anything, anything))
                     eval(subsop(2='integrate'(op(2,b),x),b), x=h)
                   end proc,
                   op(2,m)),
             m);
    elif m :: 'LO(name, anything)' then
      eval(op(2,m), op(1,m) = h)
    elif m :: 'Plate'(anything) then
      x := 'pp';
      if h :: 'Integrand(name, anything)' then
        x := op(1,h);
      end if;
      x := gensym(x);
      # we don't know the dimension, so use x as a vector variable.
      ProductIntegral(integrate_ary(op(1,m)), x, applyintegrand(h, x));
    elif h :: procedure then
      x := gensym('xa');
      'integrate'(m, Integrand(x, h(x)))
    else
      'procname(_passed)'
    end if
  end proc;

  # integrates programs that denote arrays of measures
  integrate_ary := proc(m)
    local h;

    if m :: 'ary'(anything, name, anything) then
      h := gensym('hh');
      # aryM = array of Measures
      aryM(op(1,m), op(2,m), h, integrate(op(3,m), h));
    else
      # right now, throw a hard error rather than just passing things
      # through; once we understand this better, we'll revert.
      error "was expecting an array program but got %1 instead", m;
    end if;
  end proc;

# Step 2 of 3: computer algebra

  improve := proc(lo :: LO(name, anything), {_ctx :: list := []})
    LO(op(1,lo), reduce(op(2,lo), op(1,lo), _ctx))
  end proc;

  cimprove := proc(c :: Context(list(t_ctx), LO(name, anything)))
    Context(op(1,c), improve(op(2,c), _ctx = op(1,c)))
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
                 levels :: extended_numeric := infinity)
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
  reduce := proc(ee, h :: name, constraints :: list(t_ctx))
    # option remember, system;
    local e, elim, hh, subintegral, w, ww, n, i, x, c, myint, res;
    e := ee;

    if e :: Int(anything, name=anything) then
      e := elim_int(e, h, constraints);
      if e :: Int(anything, name = anything) then
        reduce_Int(reduce(op(1,e), h, [op(2,e), op(constraints)]),
                 op([2,1],e), op([2,2],e), h, constraints)
      elif e <> ee then
        reduce(e, h, constraints)
      else
        e
      end if;
    elif e :: `+` then
      map(reduce, e, h, constraints)
    elif e :: `*` then
      (subintegral, w) := selectremove(depends, e, h);
      if subintegral :: `*` then error "Nonlinear integral %1", e end if;
      subintegral := convert(reduce(subintegral, h, constraints), 'list', `*`);
      (subintegral, ww) := selectremove(depends, subintegral, h);
      reduce_pw(simplify_assuming(`*`(w, op(ww)), constraints))
        * `*`(op(subintegral));
    elif e :: t_pw then
      x := select(type, constraints, name=anything..anything);
      if nops(x) > 0 then
        e := convert_piecewise(e, op([1,1],x), constraints);
      end if;
      if e :: t_pw then
        n := nops(e);
        e := piecewise(seq(`if`(i::even or i=n,
                                reduce(op(i,e), h, constraints),
                                  # TODO: update_context like unintegrate does
                                simplify_assuming(op(i,e), constraints)),
                           i=1..n));
      end if;
      # big hammer: simplify knows about bound variables, amongst many
      # other things
      Testzero := x -> evalb(simplify(x) = 0);
      reduce_pw(e)
    elif e :: t_case then
      subsop(2=map(proc(b :: Branch(anything, anything))
                     eval(subsop(2='reduce'(op(2,b),x,c),b),
                          {x=h, c=constraints})
                   end proc,
                   op(2,e)),
             e);
    elif e :: 'integrate(anything, Integrand(name, anything))' then
      x := gensym(op([2,1],e));
      # TODO is there any way to enrich constraints in this case?
      subsop(2=Integrand(x, reduce(subs(op([2,1],e)=x, op([2,2],e)),
                                   h, constraints)), e)
    elif e :: 'ProductIntegral'(anything, name, anything) then
      reduce_PI(e, h, constraints);
    else
      simplify_assuming(e, constraints)
    end if;
  end proc;

  elim_int := proc(ee, h :: name, constraints :: list(t_ctx))
    local e, hh, elim;

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
    e;
  end proc;

  to_assumption := proc(c :: t_ctx)
    local var, lo, hi;
    if type(c, name = anything .. anything) then
      var := op(1,c);
      lo, hi := op(op(2,c));
      (var > lo, var < hi)
    elif type(c, name :: property) then
      c
    elif type(c, '{name < anything, name <= anything, name > anything,
                   name >= anything}') then
      c
    else
      error "is %1 a valid constraint?", c;
    end if;
  end proc;

  simplify_assuming := proc(ee, constraints :: list(t_ctx))
    local e, ep;
    e := evalindets(ee, 'specfunc(product)', myexpand_product);
    e := evalindets(e, 'specfunc(sum)', expand);
    e := simplify(e) assuming op(map(to_assumption, constraints));
    eval(e, exp = expand @ exp);
  end proc;

  convert_piecewise := proc (expr :: specfunc(piecewise),
                             var :: name, constraints :: list)
    local e, i, assumptions;
    e := expr;
    assumptions := map(to_assumption, constraints);
    # Reduce inequality between exp(a) and exp(b) to inequality between a and b
    # [ccshan 2016-02-29]
    e := piecewise(seq(`if`(i::odd and i<nops(e)
                              and op(i,e) :: '{exp(anything) <  exp(anything),
                                               exp(anything) <= exp(anything)}'
                              and ((is(op([i,1,1],e), real) and
                                    is(op([i,2,1],e), real))
                                   assuming op(assumptions)),
                            op([i,0],e)(op([i,1,1],e), op([i,2,1],e)),
                            op(i,e)),
                       i=1..nops(e)));
    if e :: t_pw then
      try
        e := convert(e, 'piecewise', var) assuming op(assumptions);
      catch:
      end try;
    end if;
    e;
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
    local e, dom_spec, new_rng, rest, w, bound, indep, i;

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
      if dom_spec <> {} then 
        e := Int(piecewise(And(op(dom_spec)), e, 0), var = new_rng);
      else
        e := Int(e, var=new_rng);
      end if;
      e := w*elim_int(e, h, constraints);
      # what does rest depend on?
      bound := [var, op(map2(op, 1, constraints))];
      (rest, indep) := selectremove(depends, rest, bound);
      # don't turn 'rest' into piecewise (yet), but indep is ok
      if indep = {} then
        e := mul(indicator(i), i in rest)*e;
      else
        e := mul(indicator(i), i in rest)*piecewise(And(op(indep)), e, 0);
      end if;
    end if;
    e
  end proc;

  reduce_PI := proc(ee, h, constraints)
    local e, nm, hh, nh, w, m, n, i, var, x, a, xs, aa, mm, ww, inner;
    (e, nm, hh) := op(ee);

    # by construction, the inner and outer h are different
    if type(e,'aryM'(anything, name, name, 'applyintegrand'(name,anything))) then
      if op(3,e) = op([4,1],e) then
        eval(hh, nm = 'ary'(op(1,e), op(2,e), op([4,2],e)))
      else
        error "reduce_PI: %1 is not patently linear in %2", op(4,e), op(3,e)
      end if
    elif type(e, 'aryM'(anything, name, name, anything)) then
      (n, i, var, a) := op(e);
      a := reduce(a, var, constraints);
      if type(a, `*`) then
        (m, w) := selectremove(depends, a, var);
      else
        (m, w) := (a, 1);
      end if;

      w := simplify_assuming(product(w, i=1..n), constraints);
      # special case; could do Integrand too.
      if a :: 'Int'(anything, name = range) then
        if type(op(1,a), `*`) then
          (mm, ww) := selectremove(depends, op(1,a), var);
        else
          (mm, ww) := (op(1,a), 1);
        end if;
        if not type(mm, 'applyintegrand'(name, name)) then
          x := op([2,1], a);
          xs := gensym(x);
          inner := ProductIntegral('aryM'(n, i, var,
                   eval(mm, x = idx(xs, i))), nm, hh);
          aa := ProductIntegral('aryM'(n, i, var,
                 Int(ww * applyintegrand(var, x),op(2,a))), xs,
                 reduce_PI(inner, var, constraints));
          return aa; # recurse?  only on inner?
        end if;
      end if;

      if normal(a/m) <> 1 then # something changed
        w * reduce(ProductIntegral(aryM(n, i, var, m), nm, hh), h, constraints)
      else
        w * 'ProductIntegral'(e, nm, hh)
      end if;
    else
      ee
    end if;
  end proc;
#  plate := proc(a)
#    local xs, w, m;
#    elif a :: 'ary(anything, name, Bind(anything, name, anything))' then
#      xs := gensym(op([3,2],a));
#      bind(plate(ary(op(1,a), op(2,a), op([3,1],a))), xs,
#           plate(ary(op(1,a), op(2,a),
#                 eval(op([3,3],a), op([3,2],a)=idx(xs,op(2,a))))))
#    end if;
#  end proc;

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
    lo, rest := selectremove(type, spec, '{freeof(v) <  identical(v),
                                           freeof(v) <= identical(v)}');
    hi, rest := selectremove(type, rest, '{identical(v) <  freeof(v),
                                           identical(v) <= freeof(v)}');
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
      local res;

      res := to_set(b);
      `if`(res={}, 1, 'Indicator'(res));
    end proc;
  end module;

  # flip an actual condition.  Might fail if it is trivially unsat.
  flip_cond := proc(c)
    op(op(1,indicator(c)))
  end proc;

  banish := proc(m, x :: name, h :: name, g, levels :: extended_numeric)
    # LO(h, banish(m, x, h, g)) should be equivalent to Bind(m, x, LO(h, g))
    # but performs integration over x innermost rather than outermost.
    local guard, subintegral, w, y, yRename, lo, hi, mm, xx, hh, gg, ll;
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
    elif g :: t_case then
      subsop(2=map(proc(b :: Branch(anything, anything))
                     eval(subsop(2='banish'(op(2,b),xx,hh,gg,ll),b),
                          {xx=x, hh=h, gg=g, ll=l})
                   end proc,
                   op(2,integral)),
             integral);
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

  fromLO := proc(lo :: LO(name, anything), {_ctx :: list(t_ctx) := []})
    local h;
    h := gensym(op(1,lo));
    unintegrate(h, eval(op(2,lo), op(1,lo) = h), _ctx)
  end proc;

  fromCLO := proc(c :: Context(list(t_ctx), LO(name, anything)))
    Context(op(1,c), fromLO(op(2,c), op(1,c)))
  end proc;

  unintegrate := proc(h :: name, integral, context :: list(t_ctx))
    local x, c, lo, hi, m, mm, w, w0, recognition, subintegral,
          n, i, next_context, update_context, lower, upper;
    if integral :: 'And'('specfunc({Int,int})',
                         'anyfunc'('anything','name'='range'('freeof'(h)))) then
      x := gensym(op([2,1],integral));
      (lo, hi) := op(op([2,2],integral));
      lower := `if`(not (lo = -infinity), lo < x, NULL);
      upper := `if`(not (hi = infinity), x < hi, NULL);
      if [lower, upper] = [] then lower := x :: real end if;
      next_context := [op(context), lower, upper];
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
    elif integral :: 'aryM'(anything, name, name, anything) then
      m := unintegrate(op(3,integral), op(4, integral), context);
      'ary'(op(1,integral), op(2, integral), m);
    elif integral :: 'ProductIntegral'(anything, name, anything) then
      m := unintegrate(h, op(1, integral), context);
      (w,m) := unweight(m);
      mm := unintegrate(h, op(3, integral), context);
      weight(w, bind(Plate(m), op(2,integral), mm));
    elif integral :: 'applyintegrand'('identical'(h), 'freeof'(h)) then
      Ret(op(2,integral))
    elif integral = 0 then
      Msum()
    elif integral :: `+` then
      Msum(op(map2(unintegrate, h, convert(integral, 'list'), context)))
    elif integral :: `*` then
      (subintegral, w) := selectremove(depends, integral, h);

      if subintegral :: `*` then error "Nonlinear integral %1", integral end if;
      m := weight(w, unintegrate(h, subintegral, context));
      if m :: Weight(anything, anything) then
        m := weight(simplify_assuming(op(1,m), context), op(2,m));
      end if;
      m
    elif integral :: t_pw
         and `and`(seq(not (depends(op(i,integral), h)),
                       i=1..nops(integral)-1, 2)) then
      n := nops(integral);
      next_context := context;
      update_context := proc(c)
        local then_context;
        then_context := [op(next_context), c];
        next_context := [op(next_context), flip_cond(c)]; # Mutation!
        then_context
      end proc;
      piecewise(seq(piecewise(i::even,
                              unintegrate(h, op(i,integral),
                                          update_context(op(i-1,integral))),
                              i=n,
                              unintegrate(h, op(i,integral), next_context),
                              op(i,integral)),
                    i=1..n))
    elif integral :: t_case then
      subsop(2=map(proc(b :: Branch(anything, anything))
                     eval(subsop(2='unintegrate'(x,op(2,b),c),b),
                          {x=h, c=context})
                   end proc,
                   op(2,integral)),
             integral);
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
    local NONE; # used as a placeholder
    map(proc(x) 
          if type(x, specfunc(%int)) then op([1,1],x)
          elif type(x, specfunc(%weight)) then NONE
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
    local sol, dxdt, vars, in_sol, r_in_sol, p_mv, would_capture, flip;
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
    would_capture := map2(op, 1, r_in_sol);

    # May have to pull the integral for main_var up a few levels
    interpret(
      [ %WouldCapture(main_var, p_mv, [seq(i, i in would_capture)])
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
      sol := map(disint2, convert(integral, 'list'), h, t, path);
      error "on a `+`, got", sol;
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
        next_context := [op(next_context), flip_cond(c)]; # Mutation!
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

  get_int_pos := proc(var, path)
    local finder;
    finder := proc(loc) 
      if type(op(loc,path),specfunc(%int)) and op([loc,1,1], path) = var then
        loc
      else
        NULL # cheating...
      end if
    end proc;
    seq(finder(i),i=1..nops(path)); 
  end proc;

  change_var := proc(act, chg, path, part)
    local bds, new_upper, new_lower, new_path, flip, var, finder, pos,
       DUMMY;

    # first step, find where the relevant integral is
    var := op(1,act);
    pos := get_int_pos(var, path);
    new_path := eval(subsop(pos=DUMMY, path), op(3,act));

    bds := op([pos,1,2], path);
    new_upper := limit(op([2,2], act), op(1, act) = op(2,bds), left);
    new_lower := limit(op([2,2], act), op(1, act) = op(1,bds), right);
    flip := op(4,act);
    if flip=-1 then
      (new_lower, new_upper) := (new_upper, new_lower);
    end if;
    if new_upper = infinity and new_lower = -infinity then
      # we're done with this integral, put it back on path
      new_path := subsop(pos = %int(t = -infinity .. infinity), new_path);
      interpret(chg, new_path, part)
    else
      # right now, putting in new constraints "innermost", while
      # they really ought to be floated up as far as possible.
      # Probably leave that to improve?
      new_path := subsop(pos = %int(t = new_lower.. new_upper), new_path);
      interpret(chg, new_path,
	piecewise(And(new_lower < t, t < new_upper), part, 0));
    end if;
  end proc;

  # avoid_capture is essentially "inverse banish", where we pull integrals
  # up rather than pushing them down.  The list contains which variables
  # would be captured by the 'main' one.  %Top is a special variable that
  # just means that we should just push the one integral to the top, but
  # there's no need to rearrange anything else.
  avoid_capture := proc(task :: %WouldCapture(name, posint, list), chg, path, part)
    local x, p, here, there, vars, new_path, go_past, to_top, work, n, pos, 
      y, v, scope;

    go_past := convert(map2(op, 1, op(3,task)), 'set');
    to_top := member(%Top, go_past);
    if to_top and nops(go_past)>1 then
      error "cannot ask to promote to top and past some variables";
    end if;

    if nops(go_past)=0 then # nothing to do, next
      interpret(chg, path, part)
    else
      n := nops(path);
      x := op(1,task);
      p := op(2,task);

      if p = n and to_top then
        return interpret(chg, path, part)
      end if;

      # two-pass algorithm:
      # 1. push the integral on the main variable "up", past the others
      # 2. push all the weights "down" into scope

      # for efficiency, work with a table, not a list
      pos := p+1;
      work := evalb(pos <= n);
      new_path := table(path);
      here  := path[p];

      # first pass
      while work do
        y := new_path[pos];
        if type(y, specfunc(%weight)) then
          new_path[pos-1] := y;
          new_path[pos] := here;
          pos := pos + 1;
        elif type(y, specfunc(%int)) then
          v := op([1,1], y);
          go_past := go_past minus {v};
          # TODO: surely we're missing a test here for the bounds
          new_path[pos-1] := y;
          new_path[pos] := here;
          pos := pos + 1;
          work := evalb(go_past = {} and pos <= n);
        else
          error "How do I move past a %1 ?", eval(y);
        end if;
      end do;

      # second pass
      scope := NULL;
      for pos from n to 2 by -1 do
        y := new_path[pos];
        if type(y, specfunc(%int)) then
          scope := op([1,1], y), scope;
        elif type(y, specfunc(%weight)) then
          vars := indets(y, 'name');
          vars := `if`(member(x, vars), vars union go_past, vars);
          vars := vars intersect go_past;
          if vars <> {} then # if no problem vars, keep going
            there := new_path[pos-1];
            if type(there, specfunc(%int)) then
              # TODO: surely we're missing a test here for the bounds
              scope := op([1,1], there), scope;
              new_path[pos-1] := y;
              new_path[pos] := there;
            elif type(there, specfunc(%weight)) then
              new_path[pos-1] := %weight(op(1,y) * op(1, there));
              new_path[pos] := %weight(1); # don't mess up the length
            else
              error "how do I move a weight below a %1", there;
            end if;
          end if;
        else
          error "How do I move below a %1 ?", y;
        end if;
      end do;

      interpret(chg, [seq(new_path[i], i=1..nops(path))], part);
    end if;
  end proc;

  # interpret a plan
  # chg : plan of what needs to be done
  # path : context, allows one to reconstruct the incoming expression
  # part: partial answer
  interpret := proc(chg, path, part)
    local i, ans, pos, var;
    if path=[] then part
    elif chg=[] then # finished changes, just reconstruct
      ans := part;
      for i from 1 to nops(path) do
        ans := reconstruct(path[i], ans);
      end do;
      return ans;
    elif type(chg[1], specfunc(%Change)) then
      change_var(chg[1], chg[2..-1], path, part);
    elif type(chg[1], specfunc(%WouldCapture)) then
      avoid_capture(chg[1], chg[2..-1], path, part);
    elif type(chg[1], specfunc(%ToTop)) then
      var := op([1,1], chg);
      if type(path[-1], specfunc(%int)) and op([-1,1,1], path) = var then
        interpret(chg[2..-1], path, part)
      else

        pos := get_int_pos(var, path);
        interpret([%WouldCapture(var, pos, [%Top]), op(2..-1,chg)], path, part); 
      end if;
    elif type(chg[1], specfunc(%Drop)) then
      if type(path[-1], specfunc(%int)) and op([-1,1,1], path) = op([1,1], chg) then
        interpret(chg[2..-1], path[1..-2], part)
      else
        error "asked to drop t-integral (%1, %2), but it is not at top ",
          path, part
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
    elif m :: 'Weight(anything, anything)' then
      op(1,m)*bind(op(2,m), x, n)
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

  case := proc(e, bs :: specfunc(Branch(anything, anything), Branches))
    local ret, b, substs, eSubst, pSubst, p, binds, uncertain;
    ret := Branches();
    for b in bs do
      substs := pattern_match(e, e, op(1,b));
      if substs <> NULL then
        eSubst, pSubst := substs;
        p := subs(pSubst, op(1,b));
        binds := {pattern_binds(p)};
        uncertain := remove((eq -> lhs(eq) in binds), eSubst);
        if nops(uncertain) = 0 then p := PWild end if;
        ret := Branches(op(ret),
                        Branch(p, eval(eval(op(2,b), pSubst), eSubst)));
        if nops(uncertain) = 0 then break end if;
      end if
    end do;
    if ret :: Branches(Branch(identical(PWild), anything)) then
      op([1,2], ret)
    elif ret :: Branches(Branch(identical(p_true), anything),
                         Branch({identical(p_false),
                                 identical(PWild),
                                 PVar(anything)}, anything)) then
      piecewise(make_piece(e), op([1,2], ret), op([2,2], ret))
    elif ret :: Branches(Branch(identical(p_false), anything),
                         Branch({identical(p_true),
                                 identical(PWild),
                                 PVar(anything)}, anything)) then
      piecewise(make_piece(e), op([2,2], ret), op([1,2], ret))
    else
      'case'(e, ret)
    end if
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
    if a :: 'ary'(anything, name, anything) then
      eval(op(3,a), op(2,a)=i)
    elif a :: t_pw then
      map_piecewise(procname, _passed)
    else
      'procname(_passed)'
    end if
  end proc;

  unweight := proc(m)
    local total, ww, mm;
    if m :: 'Weight(anything, anything)' then
      op(m)
    elif m :: 'specfunc(Msum)' then
      total := `+`(op(map((mi -> unweight(mi)[1]), m)));
      (total, map((mi -> weight(1/total, mi)), m))
    elif m :: 'specfunc(ary)' then
      (ww,mm) := unweight(op(3,m));
      (product(ww, op(2,m)=1..op(1,m)), 'ary'(op(1,m), op(2,m), mm))
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

  pattern_match := proc(e0, e, p)
    local x, substs, eSubst, pSubst;
    if p = PWild then return {}, {}
    elif p :: PVar(anything) then
      x := op(1,p);
      pSubst := {`if`(depends(e0,x), x=gensym(x), NULL)};
      return {subs(pSubst,x)=e}, pSubst;
    elif p = p_true then
      if e = true then return {}, {}
      elif e = false then return NULL
      end if
    elif p = p_false then
      if e = false then return {}, {}
      elif e = true then return NULL
      end if
    elif p :: PDatum(anything, anything) then
      if e :: Datum(anything, anything) then
        if op(1,e) = op(1,p) then return pattern_match(e0, op(2,e), op(2,p))
        else return NULL
        end if
      end if
    elif p :: PInl(anything) then
      if e :: Inl(anything) then return pattern_match(e0, op(1,e), op(1,p))
      elif e :: Inr(anything) then return NULL
      end if
    elif p :: PInr(anything) then
      if e :: Inr(anything) then return pattern_match(e0, op(1,e), op(1,p))
      elif e :: Inl(anything) then return NULL
      end if
    elif p :: PEt(anything, anything) then
      if e :: Et(anything, anything) then
        substs := pattern_match(e0, op(1,e), op(1,p));
        if substs = NULL then return NULL end if;
        eSubst, pSubst := substs;
        substs := pattern_match(e0, eval(op(2,e),eSubst), op(2,p));
        if substs = NULL then return NULL end if;
        return eSubst union substs[1], pSubst union substs[2];
      elif e = Done then return NULL
      end if
    elif p = PDone then
      if e = Done then return {}, {}
      elif e :: Et(anything, anything) then return NULL
      end if
    elif p :: PKonst(anything) then
      if e :: Konst(anything) then return pattern_match(e0, op(1,e), op(1,p))
      end if
    elif p :: PIdent(anything) then
      if e :: Ident(anything) then return pattern_match(e0, op(1,e), op(1,p))
      end if
    else
      error "pattern_match: %1 is not a pattern", p
    end if;
    pSubst := map((x -> `if`(depends(e0,x), x=gensym(x), NULL)),
                  {pattern_binds(p)});
    eSubst := {e=evalindets(
                   evalindets[nocache](
                     subs(pSubst,
                          p_true=true,
                          p_false=false,
                          PDatum=Datum, PInr=Inr, PInl=Inl, PEt=Et, PDone=Done,
                          PKonst=Konst, PIdent=Ident,
                          p),
                     identical(PWild),
                     p -> gensym(_)),
                   PVar(anything),
                   p -> op(1,p))};
    eSubst, pSubst
  end proc;

  make_piece := proc(rel)
    # Try to prevent PiecewiseTools:-Is from complaining
    # "Wrong kind of parameters in piecewise"
    if rel :: {'`::`', 'boolean', '`in`'} then
      rel
    elif rel :: {specfunc(anything, {And,Or,Not}), `and`, `or`, `not`} then
      map(make_piece, rel)
    else
      rel = true
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

  RoundTripLO := proc(m, {ctx :: list(t_ctx) := []})
      lprint(eval(ToInert(fromLO(improve(toLO(m), _ctx = ctx), _ctx = ctx)), 
        _Inert_ATTRIBUTE=NULL))
  end proc;

  RoundTripCLO := proc(m :: Context(list(t_ctx), anything))
      sprintf("%a",(eval(ToInert(fromCLO(cimprove(toCLO(m)))), _Inert_ATTRIBUTE=NULL)))
  end proc;

# Testing

  TestHakaru := proc(m,n::algebraic:=m,{simp:=improve,verify:=simplify,ctx:=[]})
    CodeTools[Test](fromLO(simp(toLO(m), _ctx = ctx), _ctx = ctx), n,
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
    TypeTools[AddType](t_ctx, 
      '{name :: anything, name = anything .. anything, name < anything,
        name <= anything, name > anything, name >= anything}');
    VerifyTools[AddVerification](measure = verify_measure);
  end proc;

  ModuleUnload := proc()
    TypeTools[RemoveType](t_ctx);
    VerifyTools[RemoveVerification](measure);
  end proc;

  ModuleLoad();

end module; # NewSLO
