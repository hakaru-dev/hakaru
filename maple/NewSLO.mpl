# Teach Maple (through depends and eval) about our new binding forms.
# Integrand and LO bind from 1st arg to 2nd arg.

`depends/Integrand` := proc(v, e, x) depends(e, x minus {v}) end proc:
`depends/LO`        := proc(v, e, x) depends(e, x minus {v}) end proc:

`eval/Integrand` := proc(e, eqs)
  local v, ee;
  v, ee := op(e);
  eval(op(0,e), eqs)(BindingTools:-generic_evalat(v, ee, eqs))
end proc:

`eval/LO` := proc(e, eqs)
  local v, ee;
  v, ee := op(e);
  eval(op(0,e), eqs)(BindingTools:-generic_evalat(v, ee, eqs))
end proc:

#############################################################################

NewSLO := module ()
  option package;
  local
        t_sum, t_product,
        integrate_known,
        recognize_continuous, recognize_discrete, get_de, get_se,
        recognize_de, mysolve, Shiftop, Diffop, Recognized,
        factorize, termize, bind, weight,
        reduce_IntSum, reduce_IntsSums, get_indicators,
        elim_intsum, do_elim_intsum, int_assuming, sum_assuming,
        banish, banish_guard, banish_weight,
        reduce_pw, nub_piecewise, piecewise_if,
        find_vars, kb_from_path, interpret, reconstruct, invert,
        get_var_pos, get_int_pos,
        avoid_capture, change_var, old_disint, disint2,
        mk_sym, mk_ary, mk_idx, innermostIntSum, ChangeVarInt,
        ModuleLoad;
  export
     # These first few are smart constructors (for themselves):
         integrate, applyintegrand,
     # while these are "proper functions"
         RoundTrip, Simplify, SimplifyKB, TestSimplify, TestHakaru, Efficient,
         toLO, fromLO, unintegrate, unweight, improve, reduce,
         density, bounds,
         ReparamDetermined, determined, reparam, disint;
  # these names are not assigned (and should not be).  But they are
  # used as global names, so document that here.
  global LO, Integrand, Indicator, SumIE, ProductIE;
  uses Hakaru, KB, Loop;

  RoundTrip := proc(e, t::t_type)
    local result;
    interface(screenwidth=infinity, prettyprint=0);
    kernelopts(assertlevel=0);
    writeto("/dev/fd/2");
    result := eval(ToInert(Simplify(_passed)), _Inert_ATTRIBUTE=NULL);
    writeto(terminal);
    lprint(result)
  end proc;

  Simplify := proc(e, t::t_type, {ctx :: list := []}, $)
    subsindets(SimplifyKB(e, t, foldr(assert, empty, op(ctx))),
               And({t_sum, t_product}, anyfunc(anything, anything=range)),
               e -> subsop(0 = `if`(e::t_sum, SumIE, ProductIE),
                           applyop(`+`, [2,2,2], e, 1)))
  end proc;

  SimplifyKB := proc(e, t::t_type, kb::t_kb, $)
    local patterns, x, kb1, ex;
    if t :: HMeasure(anything) then
      fromLO(improve(toLO(e), _ctx=kb), _ctx=kb)
    elif t :: HFunction(anything, anything) then
      patterns := htype_patterns(op(1,t));
      if patterns :: Branches(Branch(PVar(name),anything)) then
        # Eta-expand the function type
        x := `if`(e::lam(name,anything,anything), op(1,e),
                  op([1,1,1],patterns));
        x, kb1 := genType(x, op(1,t), kb, e);
        ex := app(e,x);
        lam(x, op(1,t), SimplifyKB(ex, op(2,t), kb1))
      else
        # Eta-expand the function type and the sum-of-product argument-type
        x := `if`(e::lam(name,anything,anything), op(1,e), d);
        if depends([e,t,kb], x) then x := gensym(x) end if;
        ex := app(e,x);
        lam(x, op(1,t), 'case'(x,
          map(proc(branch)
                local eSubst, pSubst, p1, binds, y, kb1, i, pSubst1;
                eSubst, pSubst := pattern_match([x,e], x, op(1,branch));
                p1 := subs(pSubst, op(1,branch));
                binds := [pattern_binds(p1)];
                kb1 := kb;
                pSubst1 := table();
                for i from 1 to nops(binds) do
                  y, kb1 := genType(op(i,binds), op([2,i],branch), kb1);
                  pSubst1[op(i,binds)] := y;
                end do;
                pSubst1 := op(op(pSubst1));
                Branch(subs(pSubst1, p1),
                       SimplifyKB(eval(eval(ex,eSubst),pSubst1), op(2,t), kb1))
              end proc,
              patterns)))
      end if
    else
      simplify_assuming(e, kb)
    end if
  end proc;

# Testing

  TestSimplify := proc(m, t, n::algebraic:=m, {verify:=simplify})
    local s, r;
    # How to pass keyword argument {ctx::list:=[]} on to Simplify?
    s, r := selectremove(type, [_rest], 'identical(ctx)=anything');
    CodeTools[Test](Simplify(m,t,op(s)), n, measure(verify), op(r))
  end proc;

  TestHakaru := proc(m, n::{set(algebraic),algebraic}:=m,
                     {simp:=improve, verify:=simplify, ctx::list:=[]})
    local kb;
    kb := foldr(assert, empty, op(ctx));
    CodeTools[Test](fromLO(simp(toLO(m), _ctx=kb), _ctx=kb), n,
      measure(verify), _rest)
  end proc;

  # Test roughly for "efficient" Hakaru measure terms,
  # i.e., those we want simplification to produce.
  Efficient := proc(mm, $)
    local m, n;
    m := mm;
    if has(m, 'undefined') then
      return false;
    end if;
    while m :: '{lam(name, anything, anything),
                 Context(anything, anything),
                 And(specfunc(piecewise), anyfunc(anything, anything, Msum()))}' do
      m := op(`if`(op(0,m)='lam',3,2),m);
    end do;
    if m :: 'Weight(anything, anything)' then m := op(2,m) end if;
    if has(m, '{infinity, Lebesgue, int, Int, Beta, GAMMA}') then
      return false;
    end if;
    for n in `if`(m :: 'specfunc(Msum)', m, [m]) do
      if n :: 'Weight(anything, anything)' then n := op(2,n) end if;
      if has(subsindets(n, 'specfunc(Weight(anything, anything), Msum)',
                        s -> `if`(Testzero(`+`(op(map2(op, 1, s))) - 1),
                                  map2(op, 2, s), s)),
             '{Msum, Weight}') then
        return false;
      end if;
    end do;
    return true;
  end proc;

  t_sum     := 'specfunc({sum    ,Sum    })';
  t_product := 'specfunc({product,Product})';

# An integrand h is either an Integrand (our own binding construct for a
# measurable function to be integrated) or something that can be applied
# (probably proc, which should be applied immediately, or a generated symbol).

  applyintegrand := proc(h, x, $)
    local var, body, dummy;
    if h :: 'Integrand(name, anything)' then
      var, body := op(h);
      if x :: {boolean, specfunc({And,Or,Not})} then
        body := eval(body, var=dummy);
        var  := dummy;
        body := subs((var=true)=var, body);
      end if;
      eval(body, var=x)
    elif h :: appliable then
      h(x)
    else
      'procname(_passed)'
    end if
  end proc;

# Step 1 of 3: from Hakaru to Maple LO (linear operator)

  toLO := proc(m, $)
    local h;
    h := gensym('h');
    LO(h, integrate(m, h, []))
  end proc;

  integrate := proc(m, h, loops :: list(name = range) := [], $)
    local x, n, i, res, l;

    if m :: known_continuous then
      integrate_known(Int, Ints, 'xx', m, h, loops)
    elif m :: known_discrete then
      integrate_known(Sum, Sums, 'kk', m, h, loops)
    elif m :: 'Ret(anything)' then
      applyintegrand(h, mk_ary(op(1,m), loops))
    elif m :: 'Bind(anything, name, anything)' then
      res := eval(op(3,m), op(2,m) = mk_idx(op(2,m), loops));
      res := eval(Integrand(op(2,m), 'integrate'(res, x, loops)), x=h);
      integrate(op(1,m), res, loops);
    elif m :: 'specfunc(Msum)' and (nops(loops) = 0 or nops(m) = 1) then
      `+`(op(map(integrate, [op(m)], h, loops)))
    elif m :: 'Weight(anything, anything)' then
      foldl(product, op(1,m), op(loops)) * integrate(op(2,m), h, loops)
    elif m :: t_pw
      and not depends([seq(op(i,m), i=1..nops(m)-1, 2)], map(lhs, loops)) then
      n := nops(m);
      piecewise(seq(`if`(i::even or i=n, integrate(op(i,m), h, loops), op(i,m)),
                    i=1..n))
    elif m :: t_case and not depends(op(1,m), map(lhs, loops)) then
      subsop(2=map(proc(b :: Branch(anything, anything))
                     eval(subsop(2='integrate'(op(2,b), x, loops),b), x=h)
                   end proc,
                   op(2,m)),
             m);
    elif m :: 'LO(name, anything)' then
      eval(op(2,m), op(1,m) = h)
    elif m :: 'Plate(nonnegint, name, anything)' then
      # Unroll Plate when the bound is known. We unroll Plate here (instead
      # of unrolling Ints in reduce, for example) because we have no other
      # way to integrate certain Plates, namely those whose bodies' control
      # flows depend on the index.
      x := mk_sym('pp', h);
      x := [seq(cat(x,i), i=0..op(1,m)-1)];
      if op(1,m) = 0 then
        res := undefined;
      else
        if op(1,m) = 1 then
          res := op(1,x);
        else
           res := idx(x,op(2,m));
#          res := piecewise(seq(op([op(2,m)=i-1, op(i,x)]), i=2..op(1,m)),
#                         op(1,x));
        end if;
        res := mk_idx(res, loops);
      end if;
      res := applyintegrand(h, mk_ary('ary'(op(1,m), op(2,m), res), loops));
      for i from op(1,m) to 1 by -1 do
        res := integrate(eval(op(3,m), op(2,m)=i-1),
                         Integrand(op(i,x), res), loops);
      end do;
      res
    elif m :: 'Plate(anything, name, anything)' then
      integrate(op(3,m), h, [op(2,m)=0..op(1,m)-1, op(loops)])
    elif m :: 'Context(anything, anything)' then
      applyop(integrate, 2, m, h, loops)
    elif h :: appliable then
      x := gensym('xa');
      'integrate'(m, Integrand(x, h(x)), loops)
    else
      'procname(_passed)'
    end if
  end proc;

  integrate_known := proc(make, makes, var, m, h, loops :: list(name=range), $)
    local x, dens, bds;
    x := mk_sym(var, h);
    dens := density[op(0,m)](op(m));
    bds := bounds[op(0,m)](op(m));
    if loops = [] then
      make(dens(x) * applyintegrand(h, x), x = bds);
    else
      makes(foldl(product, dens(mk_idx(x,loops)), op(loops))
              * applyintegrand(h, x),
            x, bds, loops)
    end if;
  end proc;

# Step 3 of 3: from Maple LO (linear operator) back to Hakaru

  fromLO := proc(lo :: LO(name, anything), {_ctx :: t_kb := empty}, $)
    local h;
    h := gensym(op(1,lo));
    unintegrate(h, eval(op(2,lo), op(1,lo) = h), _ctx)
  end proc;

  unintegrate := proc(h :: name, e, kb :: t_kb, $)
    local x, c, lo, hi, make, m, mm, w, w0, w1, recognition, subintegral,
          i, kb1, kb2, loops, subst, hh, pp, t, bnds;
    if e :: 'And'('specfunc({Int,int})',
                  'anyfunc'('anything','name'='range'('freeof'(h)))) then
      (lo, hi) := op(op([2,2],e));
      x, kb1 := genLebesgue(op([2,1],e), lo, hi, kb);
      subintegral := eval(op(1,e), op([2,1],e) = x);
      (w, m) := unweight(unintegrate(h, subintegral, kb1));
      recognition := recognize_continuous(w, x, lo, hi, kb1);
      if recognition :: 'Recognized(anything, anything)' then
        (w, w0) := factorize(op(2,recognition), x, kb1);
        weight(w0, bind(op(1,recognition), x, weight(w, m)))
      else error "recognize_continuous is never supposed to fail" end if
    elif e :: 'And'('specfunc({Sum,sum})',
                    'anyfunc'('anything','name'='range'('freeof'(h)))) then
      (lo, hi) := op(op([2,2],e));
      x, kb1 := genType(op([2,1],e), HInt(closed_bounds(lo..hi)), kb);
      subintegral := eval(op(1,e), op([2,1],e) = x);
      (w, m) := unweight(unintegrate(h, subintegral, kb1));
      recognition := recognize_discrete(w, x, lo, hi, kb1);
      if recognition :: 'Recognized(anything, anything)' then
        (w, w0) := factorize(op(2,recognition), x, kb1);
        weight(w0, bind(op(1,recognition), x, weight(w, m)))
      else error "recognize_discrete is never supposed to fail" end if
    elif e :: 'And'('specfunc({Ints,ints,Sums,sums})',
                    'anyfunc'('anything', 'name', 'range'('freeof'(h)),
                              'list(name=range)')) then
      loops := op(4,e);
      bnds  := op(3,e);
      if op(0,e) in {Ints,ints} then
        t := HReal(open_bounds(bnds));
        make := Int;
      else
        t := HInt(closed_bounds(bnds));
        make := Sum;
      end if;
      x, kb1 := genType(op(2,e), mk_HArray(t, loops), kb);
      if nops(op(4,e)) > 0 then
        kb1 := assert(size(x)=op([4,-1,2,2],e)-op([4,-1,2,1],e)+1, kb1);
      end if;
      subintegral := eval(op(1,e), op(2,e) = x);
      (w, m) := unweight(unintegrate(h, subintegral, kb1));
      w := peel(w); # for "Don't be confused by extra iterations" tests
      bnds, loops, kb2 := genLoop(bnds, loops, kb, 'Integrand'(x,[w,m]));
      w, pp := unproducts(w, x, loops, kb2);
      hh := gensym('ph');
      subintegral := make(pp * applyintegrand(hh,x), x=bnds);
      (w1, mm) := unweight(unintegrate(hh, subintegral, kb2));
      mm := foldl(((mmm,loop) ->
                   Plate(op([2,2],loop) - op([2,1],loop) + 1,
                         op(1,loop),
                         eval(mmm, op(1,loop) = op(1,loop) - op([2,1],loop)))),
                  mm, op(loops));
      w := w * foldl(product, w1, op(loops));
      w := simplify_factor_assuming(w, kb1);
      (w, w0) := factorize(w, x, kb1);
      weight(simplify_factor_assuming(w0, kb),
             bind(mm, x, weight(simplify_factor_assuming(w, kb1), m)))
    elif e :: 'applyintegrand'('identical'(h), 'freeof'(h)) then
      Ret(op(2,e))
    elif e = 0 then
      Msum()
    elif e :: `+` then
      map2(unintegrate, h, Msum(op(e)), kb)
    elif e :: `*` then
      (subintegral, w) := selectremove(depends, e, h);
      if subintegral :: `*` then error "Nonlinear integral %1", e end if;
      (w0, w) := get_indicators(w);
      kb1 := foldr(assert, kb, op(w0));
      m := weight(w, unintegrate(h, subintegral, kb1));
      if m :: Weight(anything, anything) then
        m := weight(simplify_factor_assuming(op(1,m), kb1), op(2,m));
      end if;
      piecewise_And(w0, m, Msum())
    elif e :: t_pw
         and `and`(seq(not (depends(op(i,e), h)),
                       i=1..nops(e)-1, 2)) then
      kb_piecewise(e, kb, ((lhs, kb) -> lhs),
                          ((rhs, kb) -> unintegrate(h, rhs, kb)))
    elif e :: t_case then
      subsop(2=map(proc(b :: Branch(anything, anything))
                     eval(subsop(2='unintegrate'(x,op(2,b),c),b),
                          {x=h, c=kb})
                   end proc,
                   op(2,e)),
             e);
    elif e :: 'Context(anything, anything)' then
      subsop(2=unintegrate(h, op(2,e), assert(op(1,e), kb)), e)
    elif e :: 'integrate'('freeof'(h), 'anything', identical([])) then
      x := mk_sym('x', op(2,e));
      # If we had HType information for op(1,e),
      # then we could use it to tell kb about x.
      (w, m) := unweight(unintegrate(h, applyintegrand(op(2,e), x), kb));
      (w, w0) := factorize(w, x, kb);
      weight(w0, bind(op(1,e), x, weight(w, m)))
    else
      # Failure: return residual LO
      LO(h, e)
    end if
  end proc;

  recognize_continuous := proc(weight0, x, lo, hi, kb, $)
    local Constant, de, Dx, f, w, res, rng;
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
    w := subsindets[flat](weight0,
           And(function, Not(specfunc({exp, And, Or, Not})),
               'freeof'(x)),
           proc(e) Constant[e] end);
    w := subsindets[flat](w, {`^`, specfunc(exp)},
           proc(e)
             applyop(proc(e)
                       subsindets[flat](e,
                         And({`^`, specfunc(exp)},
                             Not(radfun), Not(algfun), 'freeof'(x)),
                         proc(e) Constant[e] end)
                     end,
                     -1, e)
             end);
    de := get_de(w, x, Dx, f);
    if de :: 'Diffop(anything, anything)' then
      res := recognize_de(op(de), Dx, f, x, lo, hi, kb)
    end if;
    if res = FAIL then
      res := Recognized(Lebesgue(lo, hi), w);
      rng := hi - lo;
      if not (rng :: 'SymbolicInfinity') then
        w := simplify_factor_assuming(w * rng, kb);
        # w could be piecewise and simplify will hide the problem
        if not (w :: {'SymbolicInfinity', 'undefined'}) then
          res := Recognized(Uniform(lo, hi), w)
        end if
      end if
    end if;
    # Undo Constant[...] wrapping
    res := subsindets[flat](res, 'specindex'(anything, Constant), x -> op(1,x));
    res
  end proc;

  recognize_discrete := proc(w, k, lo, hi, kb, $)
    local se, Sk, f, a0, a1, lambda, r, s, res;
    res := FAIL;
    if lo = 0 and hi = infinity then
      se := get_se(w, k, Sk, f);
      if se :: 'Shiftop(anything, anything, identical(ogf))' and
         ispoly(op(1,se), 'linear', Sk, 'a0', 'a1') then
        lambda := normal(-a0/a1*(k+1));
        if not depends(lambda, k) then
          res := Recognized(PoissonD(lambda), eval(w,k=0)/exp(-lambda));
        end if;
        if ispoly(lambda, 'linear', k, 'b0', 'b1') then
          r := b0/b1;
          res := Recognized(NegativeBinomial(r, b1), eval(w,k=0)/(1-b1)^r);
        end if
      end if;
    elif lo = 0 and not(hi :: 'SymbolicInfinity') then
      s, r := factorize(simplify_factor_assuming(w, kb), k, kb);
      if s <> 1 then
        s := simplify_factor_assuming(s, kb);
        res := ary(hi+1, k, s);
        if res :: 'list' and nops(convert(res,'set')) = 1 then
          res := Recognized(Counting(lo, hi+1), res[1]);
        else
          res := Recognized(Categorical(res), r);
        end if;
      end if;
    end if;
    if res = FAIL then
      res := Recognized(Counting(lo, hi+1), w);
    end if;
    applyop(simplify_assuming, 1,
            applyop(simplify_factor_assuming, 2, res, kb), kb)
  end proc;

  get_de := proc(dens, var, Dx, f, $)
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

  get_se := proc(dens, var, Sk, u, $)
    :: Or(Shiftop(anything, set(function=anything), name), identical(FAIL));
    local x, de, re, gftype, init, f;
    try
      # ser := series(sum(dens * x^var, var=0..infinity), x);
      # re := gfun[seriestorec](ser, f(var));
      # re, gftype := op(re);
      _EnvFormal := true;
      de := gfun[holexprtodiffeq](sum(dens*x^var, var=0..infinity), f(x));
      re := gfun[diffeqtorec](de, f(x), u(var));
      re := gfun[rectohomrec](re, u(var));
      if not (re :: set) then
        re := {re}
      end if;
      init, re := selectremove(type, re, `=`);
      if nops(re) = 1 then
        if nops(init) = 0 then
          init := {u(0) = eval(rens, var=0)};
        end if;
        re := map(proc(t)
                    local s, r;
                    s, r := selectremove(type, convert(t, 'list', `*`),
                                         u(polynom(nonnegint, var)));
                    if nops(s) <> 1 then
                      error "rectohomrec result nonhomogeneous";
                    end if;
                    s := op([1,1],s) - var;
                    if s :: nonnegint and r :: list(polynom(anything, var)) then
                      `*`(op(r), Sk^s);
                    else
                      error "unexpected result from rectohomrec"
                    end if
                  end proc,
                  convert(re[1], 'list', `+`));
        return Shiftop(`+`(op(re)), init, 'ogf')
      end if
    catch: # do nothing
    end try;
    FAIL
  end proc;

  recognize_de := proc(diffop, init, Dx, f, var, lo, hi, kb, $)
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
    # elif not evalb((hi - lo) :: 'SymbolicInfinity')
    #      and ispoly(diffop, 'linear', Dx, 'a0', 'a1')
    #      and ispoly(a0 - 2*var, 'linear', var, 'b0', 'b1') then
    #   c0 := (lo*b1 + hi + lo + b0) / (hi - lo);
    #   c1 := -(hi*b1 + hi + lo + b0) / (hi - lo);
    #   if c0 = 1 and c1 = 1 then
    #       dist := Uniform(lo, hi)
    #   else
    #       dist := bind(BetaD(c0, c1),x,lo+(hi-lo)*x)
    #   end if
    elif lo = 0 and hi = infinity
         and ispoly(diffop, 'linear', Dx, 'a0', 'a1')
         and ispoly(normal(a0*var/a1), 'linear', var, 'b0', 'b1') then
    #  if Testzero(b1-1/2) then
    #    dist := ChiSquared(2*(1-b0))
    #  else
        dist := GammaD(1-b0, 1/b1)
    #  end if;
    end if;
    if dist <> FAIL then
      try
        ii := map(convert, init, 'diff');
        constraints := eval(ii, f = (x -> w*density[op(0,dist)](op(dist))(x)));
        w := eval(w, mysolve(constraints, w));
        if not (has(w, 'w')) then
          return Recognized(simplify_assuming(dist, kb),
                            simplify_factor_assuming(w, kb));
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

  unweight := proc(m, $)
    local total, ww, mm;
    if m :: 'Weight(anything, anything)' then
      op(m)
    elif m :: 'specfunc(Msum)' then
      total := `+`(op(map((mi -> unweight(mi)[1]), m)));
      (total, map((mi -> weight(1/total, mi)), m))
    else
      (1, m)
    end if;
  end proc;

  # (s,r):=factorize(e,var,kb) expresses e in the context kb as s*r,
  # where r doesn't depend on var and s is as simple as possible
  # (and non-negative if possible).
  factorize := proc(e, var, kb, $)
    local res, x, y, kb1, s, r;
    if not depends(e, var) then
      return 1, e;
    end if;
    if e :: `*` then
      res := map(`[]`@factorize, list_of_mul(e), var, kb);
      return `*`(op(map2(op,1,res))),
             `*`(op(map2(op,2,res)));
    end if;
    if e :: 'anything^freeof(var)' then
      s, r := factorize(op(1,e), var, kb);
      return s^op(2,e),
             r^op(2,e);
    end if;
    if e :: 'And(specfunc({product,Product}),
                 anyfunc(anything, name=range(freeof(var))))' then
      x, kb1 := genType(op([2,1],e), HInt(closed_bounds(op([2,2],e))), kb, var);
      s, r := factorize(eval(op(1,e), op([2,1],e)=x), var, kb1);
      return op(0,e)(s, x=op([2,2],e)),
             op(0,e)(r, x=op([2,2],e));
    end if;
    if e :: 'And(specfunc({product,Product}),
                 anyfunc(anything, name=range))'
       and not depends(subsop([2,2,2]=undefined,e), var) then
      s, r := termize(op([2,2,2],e), var, kb);
      x := op([2,1],e);
      y := `if`(depends(r,x), gensym(x), x);
      return op(0,e)(eval(op(1,e),x=r+1+y), y=0..s-1),
             op(0,e)(op(1,e), x=op([2,2,1],e)..r);
    end if;
    e, 1;
  end proc;

  # (s,r):=termize(e,var,kb) expresses e in the context kb as s+r,
  # where r doesn't depend on var and s is as simple as possible.
  termize := proc(e, var, kb, $)
    local res, x, y, kb1, s, r, i, conds, pw;
    if not depends(e, var) then
      return 0, e;
    end if;
    if e :: `+` then
      res := map(`[]`@termize, [op(e)], var, kb);
      return `+`(op(map2(op,1,res))),
             `+`(op(map2(op,2,res)));
    end if;
    if e :: `*` then
      s, r := selectremove(depends, e, var);
      if r <> 1 then return op(map(`*`, [termize(s, var, kb)], r)) end if;
    end if;
    if e :: 'And(specfunc({sum,Sum}),
                 anyfunc(anything, name=range(freeof(var))))' then
      x, kb1 := genType(op([2,1],e), HInt(closed_bounds(op([2,2],e))), kb, var);
      s, r := termize(eval(op(1,e), op([2,1],e)=x), var, kb1);
      return op(0,e)(s, x=op([2,2],e)),
             op(0,e)(r, x=op([2,2],e));
    end if;
    if e :: 'And(specfunc({sum,Sum}),
                 anyfunc(anything, name=range))'
       and not depends(subsop([2,2,2]=undefined,e), var) then
      s, r := termize(op([2,2,2],e), var, kb);
      x := op([2,1],e);
      y := `if`(depends(r,x), gensym(x), x);
      return op(0,e)(eval(op(1,e),x=r+1+y), y=0..s-1),
             op(0,e)(op(1,e), x=op([2,2,1],e)..r);
    end if;
    if e :: 'specfunc(piecewise)' then
      conds := [seq(op(i,e), i=1..nops(e)-1, 2)];
      if depends(conds, var) then
        # Too bad the conditions depend on var.
        # But maybe the conditions depend on var only in certain cases
        # (whose conditions in turn do not depend on var)?
        pw := select(proc(pw, $)
                        local i;
                        if not depends(pw, var) then return false end if;
                        for i from 1 by 2 to nops(pw)-1 do
                          if depends(op(i,pw), var) then return false end if;
                        end do;
                        for i from 2 by 2 to nops(pw)-1 do
                          if not depends(op(i,pw), var) then return true end if;
                        end do;
                        return not depends(op(-1,pw), var);
                      end proc,
                      indets(conds, 'specfunc(piecewise)'));
        if nops(pw) > 0 then
          pw := op(1, pw); # Pick any eligible piecewise to lift
          pw := piecewise(seq(`if`(i::odd and i<nops(pw),
                                   op(i,pw),
                                   subs(pw=op(i,pw), e)),
                              i=1..nops(pw)));
          return termize(pw, var, kb);
        end if;
      else
        # Yay, the conditions don't depend on var.
        # So just map into the piecewise.
        res := kb_piecewise(e, kb, ((cond, kb) -> cond),
                                   ((ee, kb) -> [termize(ee, var, kb)]));
        if res :: 'specfunc(piecewise)'
           and [seq(op(i,res), i=2..nops(res)-1, 2), op(-1,res)]
               :: 'list([anything, anything])' then
          return piecewise(seq(op(`if`(i::odd and i<nops(res), i, [i,1]), res),
                               i=1..nops(res))),
                 piecewise(seq(op(`if`(i::odd and i<nops(res), i, [i,2]), res),
                               i=1..nops(res)));
        elif res :: '[anything, anything]' then
          return op(res)
        end if;
      end if;
    end if;
    e, 0;
  end proc;

  ###
  # smart constructors for our language

  bind := proc(m, x, n, $)
    if n = 'Ret'(x) then
      m # monad law: right identity
    elif m :: 'Ret(anything)' then
      eval(n, x = op(1,m)) # monad law: left identity
    else
      'Bind(_passed)'
    end if;
  end proc;

  weight := proc(p, m, $)
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

# Step 2 of 3: computer algebra

  improve := proc(lo :: LO(name, anything), {_ctx :: t_kb := empty}, $)
  local r, `&context`;
       userinfo(3, improve, "input: ", print(lo &context _ctx));
       userinfo(3, improve, NoName, fflush(terminal));     
       r:= LO(op(1,lo), reduce(op(2,lo), op(1,lo), _ctx));
       userinfo(3, improve, "output: ", print(r));
       r
  end proc;

  # Walk through integrals and simplify, recursing through grammar
  # h - name of the linear operator above us
  # kb - domain information
  reduce := proc(ee, h :: name, kb :: t_kb, $)
    local e, subintegral, w, ww, x, c, kb1;
    e := ee;
    if e :: 'And(specfunc({Int,Sum}), anyfunc(anything,name=range))' then
      x, kb1 := `if`(op(0,e)=Int,
        genLebesgue(op([2,1],e), op([2,2,1],e), op([2,2,2],e), kb),
        genType(op([2,1],e), HInt(closed_bounds(op([2,2],e))), kb));
      reduce_IntSum(op(0,e),
        reduce(subs(op([2,1],e)=x, op(1,e)), h, kb1), h, kb1, kb)
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
      reduce_pw(e)
    elif e :: t_case then
      subsop(2=map(proc(b :: Branch(anything, anything))
                     eval(subsop(2='reduce'(op(2,b),x,c),b),
                          {x=h, c=kb})
                   end proc,
                   op(2,e)),
             e);
    elif e :: 'Context(anything, anything)' then
      applyop(reduce, 2, e, h, assert(op(1,e), kb))
    elif e :: 'integrate(anything, Integrand(name, anything), list)' then
      x := gensym(op([2,1],e));
      # If we had HType information for op(1,e),
      # then we could use it to tell kb about x.
      subsop(2=Integrand(x, reduce(subs(op([2,1],e)=x, op([2,2],e)), h, kb)), e)
    else
      simplify_assuming(e, kb)
    end if;
  end proc;

  reduce_IntSum := proc(mk :: identical(Int, Sum),
                        ee, h :: name, kb1 :: t_kb, kb0 :: t_kb, $)
    local e, dom_spec, w, var, new_rng, make, elim;

    # if there are domain restrictions, try to apply them
    (dom_spec, e) := get_indicators(ee);
    dom_spec := kb_subtract(foldr(assert, kb1, op(dom_spec)), kb0);
    new_rng, dom_spec := selectremove(type, dom_spec,
      {`if`(mk=Int, [identical(genLebesgue), name, anything, anything], NULL),
       `if`(mk=Sum, [identical(genType), name, specfunc(HInt)], NULL),
       [identical(genLet), name, anything]});
    if not (new_rng :: [list]) then
      error "kb_subtract should return exactly one gen*"
    end if;
    make    := mk;
    new_rng := op(new_rng);
    var     := op(2,new_rng);
    if op(1,new_rng) = genLebesgue then
      new_rng := op(3,new_rng)..op(4,new_rng);
    elif op(1,new_rng) = genType then
      new_rng := range_of_HInt(op(3,new_rng));
    else # op(1,new_rng) = genLet
      if mk=Int then return 0 else make := eval; new_rng := op(3,new_rng) end if
    end if;
    e := `*`(e, op(map(proc(a::[identical(assert),anything], $)
                         Indicator(op(2,a))
                       end proc,
                       dom_spec)));
    elim := elim_intsum(make(e, var=new_rng), h, kb0);
    if elim = FAIL then
      e, w := selectremove(depends, list_of_mul(e), var);
      reduce_pw(simplify_factor_assuming(`*`(op(w)), kb0))
        * make(`*`(op(e)), var=new_rng);
    else
      reduce(elim, h, kb0);
    end if
  end proc;

  reduce_IntsSums := proc(makes, ee, var::name, rng, bds, h::name, kb::t_kb, $)
    local e, elim;
    # TODO we should apply domain restrictions like reduce_IntSum does.
    e := makes(ee, var, rng, bds);
    elim := elim_intsum(e, h, kb);
    if elim = FAIL then e else reduce(elim, h, kb) end if
  end proc;

  get_indicators := proc(e, $)
    local sub, inds, rest;
    if e::`*` then
      sub := map((s -> [get_indicators(s)]), [op(e)]);
      `union`(op(map2(op,1,sub))), `*`(op(map2(op,2,sub)))
    elif e::`^` then
      inds, rest := get_indicators(op(1,e));
      inds, subsop(1=rest, e)
    elif e::'Indicator(anything)' then
      {op(1,e)}, 1
    else
      {}, e
    end if
  end proc;

  elim_intsum := proc(e, h :: name, kb :: t_kb, $)
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

  do_elim_intsum := proc(kb, f, ee, v::{name,name=anything})
    local w, e, x, g, t, r;
    w, e := get_indicators(ee);
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

  int_assuming := proc(e, v::name=anything, kb::t_kb, $)
    simplify_factor_assuming('int'(e, v), kb);
  end proc;

  sum_assuming := proc(e, v::name=anything, kb::t_kb)
    simplify_factor_assuming('sum'(e, v), kb);
  end proc;

  banish := proc(g, h :: name, kb :: t_kb, levels :: extended_numeric,
                 x :: name, make, $)
    # banish(g, h, kb, levels, x, make), where the integrand h and the
    # integration variable x take scope over the integral g patently linear
    # in h, should be equivalent to make(kb, g), where the integration operator
    # make binds x in g, except
    #   - integration over x is performed innermost rather than outermost;
    #   - if levels < infinity then levels controls how deeply to banish g;
    #   - make is invoked with the KB in the first argument extended.
    local subintegral, w, y, kb1, lo, hi, m, loops, xx, less;
    if g = 0 then
      0
    elif levels <= 0 then
      make(kb, g)
    elif not depends(g, x) then
      make(kb, 1) * g
    elif g :: `+` then
      map(banish, _passed)
    elif g :: `*` then
      (subintegral, w) := selectremove(depends, g, h);
      if subintegral :: `*` then error "Nonlinear integral %1", g end if;
      banish(subintegral, h, kb, levels, x, banish_weight(make, w));
    elif g :: 'And'('specfunc({Int,int,Sum,sum})',
                    'anyfunc'('anything','name'='range'('freeof'(h)))) then
      lo, hi      := op(op([2,2],g));
      m           := make;
      if depends(lo, x) then
        m  := banish_guard(eval(m), lo<y);
        lo := -infinity;
      end if;
      if depends(hi, x) then
        m  := banish_guard(eval(m), y<hi);
        hi := infinity;
      end if;
      y, kb1 := `if`(op(0,g) in '{Int,int}',
        genLebesgue(op([2,1],g), lo, hi, kb, make),
        genType(op([2,1],g), HInt(closed_bounds(lo..hi)), kb, make));
      subintegral := subs(op([2,1],g)=y, op(1,g));
      op(0,g)(banish(subintegral, h, kb1, levels-1, x, m), y=lo..hi)
    elif g :: 'And'('specfunc({Ints,ints,Sums,sums})',
                    'anyfunc'('anything', 'name', 'range'('freeof'(h)),
                              'list(name=range)')) then
      lo, hi      := op(op(3,g));
      loops       := op(4,g);
      xx          := map(lhs, loops);
      m           := make;
      less        := `if`(op(0,g) in '{Ints,ints}', `<`, `<=`);
      if depends(lo, x) then
        m  := banish_guard(m, forall(xx, less(lo, mk_idx(y,loops))));
        lo := -infinity;
      end if;
      if depends(hi, x) then
        m  := banish_guard(m, forall(xx, less(mk_idx(y,loops), hi)));
        hi := infinity;
      end if;
      y, kb1 := genType(op(2,g),
                        mk_HArray(`if`(op(0,g) in '{Ints,ints}',
                                       HReal(open_bounds(lo..hi)),
                                       HInt(closed_bounds(lo..hi))),
                                  op(4,g)),
                        kb);
      if nops(op(4,g)) > 0 then
        kb1 := assert(size(y)=op([4,-1,2,2],g)-op([4,-1,2,1],g)+1, kb1);
      end if;
      subintegral := subs(op(2,g)=y, op(1,g));
      op(0,g)(banish(subintegral, h, kb1, levels-1, x, m), y, lo..hi, op(4,g));
    elif g :: t_pw then
      foldr_piecewise(
        proc(cond, th, el, $) proc(make, kb, $)
          if depends(cond, x) then
            banish(th, h, kb, levels-1, x, banish_guard(make, cond))
              + el(banish_guard(make, Not(cond)), kb)
          else
            piecewise_if(cond,
              banish(th, h, assert(cond, kb), levels-1, x, make),
              el(make, assert(Not(cond), kb)))
          end if
        end proc end proc,
        proc(make, kb, $) 0 end proc,
        g)(make, kb)
    elif g :: t_case then
      map_piecewiselike(banish, _passed)
    elif g :: 'integrate(freeof(x), Integrand(name, anything), list)' then
      y           := gensym(op([2,1],g));
      subintegral := subs(op([2,1],g)=y, op([2,2],g));
      subsop(2=Integrand(y, banish(subintegral, h, kb, levels-1, x, make)), g)
    else
      make(kb, g)
    end if
  end proc;

  banish_guard := proc(make, cond, $)
    if cond :: 'And(specfunc(Not), anyfunc(anything))' then
      # Work around simplify/piecewise bug:
      #   > simplify(piecewise(Not(i=0), 1, 0))
      #   a
      # (due to PiecewiseTools:-ImportImplementation:-UseSolve calling
      # solve(Not(i=0), {i}, 'AllSolutions', 'SolveOverReals'))
      proc(kb,g,$) make(kb, piecewise(op(1,cond),0,g)) end proc
    else
      proc(kb,g,$) make(kb, piecewise(cond,g,0)) end proc
    end if
  end proc;

  banish_weight := proc(make, w, $)
    proc(kb,g,$) make(kb, w*g) end proc
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

(*------------------- cut code -------------------------------
  #This code should not currently be used, it is just a snapshot in time.
  #New version defined below.
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
-------------- end cut code ---------------------------------- *)

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
    local i;
    for i in indets(e, 'specfunc({Int,int})') do
      if hastype(IntegrationTools:-GetIntegrand(i),
           'applyintegrand'('identical'(h),
             'dependent'(IntegrationTools:-GetVariable(i)))) then
        return false
      end if
    end do;
    return true
  end proc;

  #Beginning of Carl's code devoted to disintegration and the reparametrization (aka change
  #of variables) of integrals and sums.

  #Finds the innermost Ints or Sums in an expression, that is, those which
  #don't contain further Ints or Sums
  innermostIntSum:= proc(e::anything, $)::set(specfunc({Int,Sum}));
       select(IS-> nops(indets(IS, specfunc({Int,Sum}))) = 1, indets(e, specfunc({Int,Sum})))
  end proc;

  #my substitute for IntegrationTools:-Change
  ChangeVarInt:= proc(J::specfunc(Int), target::algebraic, $)
  local
       newJ, #What J will become.
       x::name:= op([2,1], J),
       u::name:= gensym('u'),  #new variable of integration
       s,                      #What x will become
       F                       #Boolean: flip integral?
  ;  
       s:= {solve({u = target}, {x})};
       if nops(s) = 0 then
            userinfo(1, reparam, "Can't solve substitution target.");
            return e
       end if;
       if nops(s) > 1 then
            userinfo(1, reparam, "Case of multi-branched substitution not handled.");
            return e
       end if;
       s:= s[];
                   
       newJ:= Int(
            eval(implicitdiff(u = target, x, u)*op(1,J), s),
            u= 
                 limit(target, x= op([2,2,1], J), right).. #lower limit
                 limit(target, x= op([2,2,2], J), left),   #upper limit
            op(3.., J) #optional Int args (unlikely to be used)
       );
       
       #If lower limit > upper limit, then flip limits of integration.
       F:= is(op([2,2,1], newJ) > op([2,2,2], newJ));
       if F::truefalse then
            if F then
                 userinfo(2, reparam, "Switching limits:", op([2,2], newJ));
                 newJ:= IntegrationTools:-Flip(newJ)
            end if
       else #If inequality can't be decided, then don't reverse.
            userinfo(1, reparam, "Can't order new limits:", op([2,2], newJ))
       end if;

       newJ
  end proc;
 
  #main procedure for int/sum reparamterizations 
  reparam:= proc(e::LO(symbol, algebraic), {ctx::list:= []}, $)
  local
       J:= innermostIntSum(e),   #the integral or sum
       newJ, #What J will become
       #possible subs target(s)
       oldarg::{algebraic, set(algebraic)}:= map2(op, 2, indets(e, specfunc(applyintegrand)))
  ;
       if nops(J) = 0 then
            userinfo(2, procname, "No sum or integral found.");
            return e
       end if;
       if nops(J) > 1 then
            userinfo(1, reparam, "Case of multiple innermost Int or Sums not yet handled.");
            return 'procname'(e)
       end if;
       J:= J[];
       if J::specfunc(Sum) then
            userinfo(1, reparam, "Sums not yet handled.");
            return 'procname'(e)
       end if;
       
       if nops(oldarg) <> 1 then
            userinfo(1, thisproc, "More than 1 reparam possible:", oldarg);
            return 'procname'(e)
       end if;
       oldarg:= oldarg[];   #Extract the reparam target.

       #If the target is simply a name, return input unchanged.
       if oldarg::symbol then
            userinfo(2, procname, "No need for a reparameterization.");
            return e 
       end if;

       (*#************ This isn't currently used. **********************************
       #Check the invertibility of the change of vars.

       #The ability of `solve` to select a branch is very limited. For example,
               solve({y=x^2, x > 0}, {x})
       #returns
               sqrt(y), -sqrt(y).
       #This needs to be dealt with. First idea: Use `is` to filter
       #solutions. This is implemented below.                     

       #The next command is redundantly performed in the local inits. I put it here also
       #because I anticipate some future situations where that's no longer valid.

       #Save current vars for comparison with vars after `solve`.
       Ns:= indets(oldarg, symbol);
       #The usage of `explicit` in the next line is undocumented. 
       S:= {solve({'y'=oldarg, a <= x, x <= b}, {x}, allsolutions, explicit)};
       S:= map(s->`if`(s::specfunc(piecewise), s[], s), S);
       #Use `is` to filter solutions under the assumptions.
       assume(a <= x, x <= b);
       S:= select(s-> ver(rhs,lhs)(eval(s, y= oldarg)[]), S);
       if  nops(S) <> 1  or  indets(S, symbol) <> Ns union {y}  or  hastype(S, RootOf)  then
            WARNING("Reparam target is not invertible (upto `solve` and `is`).");
            userinfo(1, procname, "Target:", subs(x= ':-x', oldarg), "S:", subs(x= ':-x', S), "domain:", ':-x'= a..b);
            return 'procname'(e)
       end if;
       *******************************************************************************)

       #Make the change of vars.
       newJ:= simplify_assuming('ChangeVarInt(J, oldarg)', foldr(assert, empty, ctx[]));
 
       if newJ = 0 then
            WARNING("Integral is 0, likely due to improper handling of an infinity issue.");
            userinfo(
                 1, procname, "u subs:",
                 print(
                      #Reformat the ChangeVarInt command for readability.
                      subs(
                           x= ':-x',
                           'ChangeVarInt'(
                                subsindets(
                                     J,
                                     specfunc(applyintegrand),
                                     f-> ':-h'(op(2,f))
                                )
                           ),
                           oldarg
                      )
                 )
            )
       end if;

       subs(J= newJ, e)
  end proc;

  #Disintegration *
  #---------------*
  #Abbreviations:
  #     wrt = "with respect to".
  #     wrt var = "a variable wrt which disintegration is performed". There may be
  #          more than one of these, in which case they are passed (in the 2nd arg)
  #          as Pairs, possibly nested.
  #     wrt-var type: Each wrt var may be continuous (Lebesgue), discrete (Counting),
  #          point evaluation (Dirac), and there may be other types added later.   
  disint:= module()
  local
       #Dispatch table for wrt-var types. For each, there is a "cond constructor",
       #a "disintegrator", and a "disintegrator_arg_extractor". The cond constructor
       #builds the associated relation in the master piecewise; the disintegrator
       #does the differentiation or whatever operator is analogous to differentiation
       #for that type after the measure has been `improve`d; and the
       #disintegrator_arg_extractor builds the 2nd arg to the disintegrator from
       #the t_disint_var passed in the 2nd arg of disint.
       #
       #APIs:
       #     Indices: 
       #          Must be the op(0, ...) of the expression passed with the 
       #          wrt var.
       #     cond_constructor: (algebraic,name)-> boolean (most likely, a relation)
       #     disintegrator: (algebraic, {name, name=anything})-> algebraic
       #     disintegrator_arg_extractor: 
       #          (`&M`(name, t_wrt_var_type))-> {name, name= anything}
       Wrt_var_types::static:= table([
            Lebesgue= Record(
                 cond_constructor= `<=`, 
                 disintegrator= diff,
                 disintegrator_arg_extractor= (A-> op(1,A))
            ),
            Counting= Record(
                 cond_constructor= `<=`, 
                 disintegrator= LREtools:-delta,
                 disintegrator_arg_extractor= (A-> op(1,A))
            ),
            #Ret is aka Dirac.
            Ret= Record(
                 cond_constructor= `=`,
                 #If it wasn't necessary to clean out the superfluous `Indicator`s,
                 #then this disintegrator could simply be `eval`, which would 
                 #have a great symmetry, the 3 disintegrators being diff, delta,
                 #and eval. 
                 disintegrator= ((e::algebraic, pt::{name=anything})-> 
                      eval(
                           eval(e, pt),
                           #Remove any Indicator made superfluous by the above eval:
                           Indicator= (r-> `if`(r::`=` and r, 1, 'Indicator'(r)))
                      )
                 ),
                 disintegrator_arg_extractor= (A-> op(1,A)= op([2,1], A))
            )
       ]), 
   
       #types for disint wrt vars (2nd arg to disint)
       t_wrt_var_type,
       t_disint_var, #Curiosity: giving this a type `type` causes a kernel crash
                     #during update-archive.
       t_disint_var_pair,  
       ModuleLoad::static:= proc($) #Needed to declare types.
            TypeTools:-AddType(
                 t_wrt_var_type,
                 satisfies(t-> assigned(Wrt_var_types[op(0,t)]))                    
            );
            TypeTools:-AddType(t_disint_var, {name, name &M t_wrt_var_type});
            TypeTools:-AddType(     #Caution: recursive type: Make sure base cases
                 t_disint_var_pair, #are on left (a la McCarthy rule).
                 'Pair'({t_disint_var, t_disint_var_pair} $ 2) 
            )
       end proc, 
       #end of types for disint
  
       DV::table,  #wrt vars, with their types and conditions
       p::symbol,  #"pair"--abstract representation
       #`path` is layers of fst(...) and snd(...) built by traversing tree
       #(Weird Maple syntax note: Module prefixes seem to be required for
       #assertion type checking. Failure to include them causes kernel crash
       #during execution.)
       path::{specfunc({Hakaru:-fst, Hakaru:-snd}), symbol},

       #Parses the 2nd arg---the wrt vars.
       # works by side-effect: accumulates "paths" to variables in T
       # via the module variable DV.
       traverse_var_tree::static:= proc(
            T::{t_disint_var, t_disint_var_pair}, $
       )::identical(NULL);
       local 
            v::name, #the wrt var 
            M::NewSLO:-disint:-t_wrt_var_type, 
            pp #iterator over [fst, snd]---the deconstructors of Pair
       ;
            if T::t_disint_var then
                 #Add a default wrt-var type if none appears.
                 (v,M):= op(`if`(T::name, T &M 'Lebesgue'((-1,1)*~infinity), T));
                 DV[v]:= Record(
                      'wrt_var_type'= M, 
                      'path'= path,
                      'disintegrator_arg'= 
                           Wrt_var_types[op(0,M)]:-disintegrator_arg_extractor(
                                v &M M
                           )
                 );
                 path:= op(path) #Peel off outer layer: fst or snd.
            else #T::Pair(..., ...)---deconstruct recursively.
                 for pp in [fst, snd] do path:= pp(path); thisproc(pp(T)) end do
            end if;
            NULL                        
       end proc, #disint:-traverse_var_tree
      
       ModuleApply::static:= proc(
            m::t_Hakaru, 
            #var &M wrt-var type, or Pairs thereof
            A::{t_disint_var, t_disint_var_pair},
            {ctx::list:= []}, #context: parameter assumptions, "knowledge"
            $
       )::t_Hakaru;
       local
            mc,  #final integral to be passed to improve @ toLO; then result
                 #of each disintegration step
            kb:= foldr(assert, empty, ctx[]),
            V, #wrt vars
            v::name #iterator over V
       ;
            #Init module variables.
            DV:= table();
            p:= gensym('p');
            path:= fst(p);

            traverse_var_tree(A); # collect information about A in DV
            userinfo(3, Disint, "DV:", eval(DV));
            V:= indices(DV, 'nolist');
            mc:= Bind(
                 m, p,
                 #The piecewise condition is a conjunction of conditions, each
                 #condition formed from a (var,path) pair from DV. 
                 piecewise(
                      And(seq(
                           Wrt_var_types[op(0, DV[v]:-wrt_var_type)]:-
                                cond_constructor(DV[v]:-path, v),
                           v= V
                      )),
                      Ret(snd(p)),
                      Msum()
                 )
            ); 
            mc:= improve(toLO(mc), _ctx= kb);
            #Does the order of application of the disintegrators matter? 
            #Theoretically, I think not, it's just like differentiation. As far
            #as Maple's ability to do the computation, maybe it matters.
            for v in V do
                 mc:= applyop(
                      Wrt_var_types[op(0, DV[v]:-wrt_var_type)]:-disintegrator, 
                      2, mc, DV[v]:-disintegrator_arg
                )
            end do;      
            fromLO(mc, _ctx= kb)
       end proc #disint:-ModuleApply
  ; 
       ModuleLoad()
  end module; #disint
  ###################### end of Carl's code ######################
  
  ###
  # prototype disintegrator - main entry point
  old_disint := proc(lo :: LO(name,anything), t::name)
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

  # this generates a KB loaded up with the knowledge gathered along
  # the current path, as well as the (potentially renamed) current path
  # there should actually not be any renaming, but let's see if that
  # invariant actually holds.
  kb_from_path := proc(path)
    local res;
    # foldr(((b,kb) -> assert_deny(b, pol, kb)), kb, op(bb))
    res := foldr(proc(b,info)
          local x, lo, hi, p, kb;
          (kb, p) := op(info);
          if type(b, specfunc(%int)) then
            (lo, hi) := op(op([1,2],b));
 
            x, kb := genLebesgue(op([1,1], b), lo, hi, kb);
            [kb, [ %int(x = lo..hi), p]];
          elif type(b, specfunc(%weight)) then
            [kb, [ b, p ]];
          else error "don't know about command (%1)", x
          end if end proc,
         [empty, []], op(path));
    (res[1], ListTools:-Flatten(res[2]));
  end proc;

  # only care about bound variables, not globals
  get_var_pos := proc(v, l)
    local p;
    if member(v, l, 'p') then VarPos(v,p) else NULL end if;
  end proc;

  invert := proc(to_invert, main_var, integral, h, path, t)
    local sol, dxdt, vars, in_sol, r_in_sol, p_mv, would_capture, flip,
      kb, npath;
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
    (kb, npath) := kb_from_path(path);
    kb := assert(t::real, kb);
    flip := simplify_assuming(signum(dxdt), kb);
      # [t = -infinity .. infinity, op(kb_from_path(path))]);
    if not member(flip, {1,-1}) then
      error "derivative has symbolic sign (%1), what do we do?", flip
    end if;

    # we need to figure out what variables the solution depends on,
    # and what plan that entails
    vars := find_vars(npath);
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
      npath, abs(dxdt) * 'applyintegrand'(h, eval(op([2,2],integral), sol)));
  end proc;

  # basic algorithm:
  # - follow the syntax
  # - collect the 'path' traversed (aka the "heap"); allows reconstruction
  # - when we hit a Ret, figure out the change of variables
  # - note that the callee is responsible for "finishing up"
  disint2 := proc(integral, h::name, t::name, path)
    local x, lo, hi, subintegral, w, m, w0, perform, script, vars,
      to_invert, sol, occurs, dxdt, update;
    if integral :: 'And'('specfunc({Int,int})',
                         'anyfunc'('anything','name'='range'('freeof'(h)))) then
      x := op([2,1],integral);
      (lo, hi) := op(op([2,2],integral));
      perform := %int(op(2,integral));
      # TODO: enrich kb with x (measure class lebesgue)
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
      error "need to map into piecewise";
      kb_piecewise(integral, kb,
                   ((lhs, kb) -> lhs),
                   ((rhs, kb) -> unintegrate(h, rhs, kb)))
    elif integral :: 'integrate'('freeof'(h), 'anything', identical([])) then
      x := mk_sym('x', op(2,integral));
      # we would be here mostly if the measure being passed in is
      # not known.  So error is fine, and should likely be caught
      # elsewhere
      error "what to do with (%1)", integral;
      # If we had HType information for op(1,e),
      # then we could use it to tell kb about x.
      (w, m) := unweight(unintegrate(h, applyintegrand(op(2,integral), x), kb));
      (w, w0) := factorize(w, x, kb);
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
    local bds, new_upper, new_lower, np, new_path, flip, var, finder, pos,
       DUMMY, kb, as;

    # first step: get ourselves a kb from this path
    (kb, np) := kb_from_path(path);
    as := kb_to_assumptions(kb);

    # second step, find where the relevant integral is
    var := op(1,act);
    pos := get_int_pos(var, np);
    new_path := eval(subsop(pos=DUMMY, np), op(3,act));

    bds := op([pos,1,2], path);
    new_upper := limit(op([2,2], act), op(1, act) = op(2,bds), left)
      assuming op(as);
    new_lower := limit(op([2,2], act), op(1, act) = op(1,bds), right)
      assuming op(as);
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

  density[Lebesgue] := proc(lo,hi,$) proc(x,$) 1 end proc end proc;
  density[Uniform] := proc(a,b,$) proc(x,$)
    1/(b-a)
  end proc end proc;
  density[Gaussian] := proc(mu, sigma, $) proc(x,$)
    1/sigma/sqrt(2)/sqrt(Pi)*exp(-(x-mu)^2/2/sigma^2)
  end proc end proc;
  density[Cauchy] := proc(loc, scale, $) proc(x,$)
    1/Pi/scale/(1+((x-loc)/scale)^2)
  end proc end proc;
  density[StudentT] := proc(nu, loc, scale, $) proc(x,$)
    GAMMA((nu+1)/2) / GAMMA(nu/2) / sqrt(Pi*nu) / scale
    * (1 + ((x-loc)/scale)^2/nu)^(-(nu+1)/2)
  end proc end proc;
  density[BetaD] := proc(a, b, $) proc(x,$)
    x^(a-1)*(1-x)^(b-1)/Beta(a,b)
  end proc end proc;
  # Hakaru uses the alternate definition of gamma, so the args are backwards
  density[GammaD] := proc(shape, scale, $) proc(x,$)
    x^(shape-1)/scale^shape*exp(-x/scale)/GAMMA(shape);
  end proc end proc;
  density[InverseGammaD]:= proc(shape, scale, $)
       proc(x,$) scale^shape/GAMMA(shape)/x^(shape+1)/exp(scale/x) end proc
  end proc;
  density[Counting] := proc(lo, hi, $) proc(k,$)
    1
  end proc end proc;
  density[Categorical] := proc(a, $) proc(k,$)
    idx(a,k)
  end proc end proc;
  density[Binomial]:= proc(n,p,$)
       proc(k,$) p^k*(1-p)^(n-k)*GAMMA(n+1)/GAMMA(k+1)/GAMMA(n-k+1) end proc
  end proc;
  density[NegativeBinomial] := proc(r, p, $) proc(k,$)
    p^k * (1-p)^r * GAMMA(r+k) / GAMMA(k+1) / GAMMA(r)
  end proc end proc;
  density[PoissonD] := proc(lambda, $) proc(k,$)
    lambda^k/exp(lambda)/k!
  end proc end proc;
  density[ChiSquared] := proc(k, $) proc(x,$)
    x^((1/2)*k-1)*exp(-(1/2)*x)/(2^((1/2)*k)*GAMMA((1/2)*k))
  end proc end proc:

  bounds[Lebesgue] := `..`;
  bounds[Uniform] := proc(a, b, $) a .. b end proc;
  bounds[Gaussian] := proc(mu, sigma, $) -infinity .. infinity end proc;
  bounds[Cauchy] := proc(loc, scale, $) -infinity .. infinity end proc;
  bounds[StudentT] := proc(nu, loc, scale, $) -infinity .. infinity end proc;
  bounds[BetaD] := proc(a, b, $) 0 .. 1 end proc;
  bounds[GammaD] := proc(shape, scale, $) 0 .. infinity end proc;
  bounds[InverseGammaD]:= proc(shape, scale, $) 0..infinity end proc;
  bounds[Counting] := proc(lo, hi, $) lo..hi-1 end proc;
  bounds[Categorical] := proc(a, $) 0 .. size(a)-1 end proc;
  bounds[Binomial]:= proc(n,p,$) 0..n end proc;
  bounds[NegativeBinomial] := proc(r, p, $) 0 .. infinity end proc;
  bounds[PoissonD] := proc(lambda, $) 0 .. infinity end proc;
  bounds[ChiSquared] := proc(k, $) 0 .. infinity end proc;

  mk_sym := proc(var :: name, h, $)
    local x;
    x := var;
    if h :: 'Integrand(name, anything)' then
      x := op(1,h);
    elif h :: 'procedure' then
      x := op(1, [op(1,h), x]);
    end if;
    gensym(x)
  end proc;

  mk_ary := proc(e, loops :: list(name = range), $)
    foldl((res, i) -> ary(op([2,2],i) - op([2,1],i) + 1,
                          op(1,i),
                          eval(res, op(1,i) = op(1,i) + op([2,1],i))),
          e, op(loops));
  end proc;

  mk_idx := proc(e, loops :: list(name = range), $)
    foldr((i, res) -> idx(res, op(1,i) - op([2,1],i)),
          e, op(loops));
  end proc;

  ModuleLoad := proc($)
    local prev;
    Hakaru; # Make sure the Hakaru module is loaded for the types t_type and t_Hakaru.
    KB;     # Make sure the KB module is loaded, for the type t_kb
    prev := kernelopts(opaquemodules=false);
    try
      PiecewiseTools:-InertFunctions := PiecewiseTools:-InertFunctions
        union '{# Do not lift piecewise over a binder
                Integrand,LO,lam,Branch,Bind,ary,Plate,
                forall,Ints,Sums,ints,sums,`..`}';
    catch:
         userinfo(
              1, NewSLO,
              "Redefinition of PiecewiseTools:-InertFunctions failed.",
              StringTools:-FormatMessage(lastexception[2..-1])
         )
    finally
      kernelopts(opaquemodules=prev);
    end try
  end proc; #ModuleLoad

  ModuleLoad();

end module; # NewSLO
