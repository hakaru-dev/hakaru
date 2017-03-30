

# Step 3 of 3: from Maple LO (linear operator) back to Hakaru

fromLO := module()

  export ModuleApply :=
  proc(lo :: LO(name, anything), {_ctx :: t_kb := empty}, $)
    local h;
    h := gensym(op(1,lo));
    unintegrate(h, eval(op(2,lo), op(1,lo) = h), _ctx)
  end proc;

  export
  unintegrate := proc(h :: name, e, kb :: t_kb, $)
    local x, c, lo, hi, make, m, mm, w, w0, w1, recognition, subintegral,
          i, kb1, kb2, loops, subst, hh, pp, t, bnds, br;
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
        ASSERT(type(kb1,t_kb), "unintegrate{Ints,Sums}: integral bounds invalid");
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
      (w0, w) := op(Domain:-Extract:-Shape(w));
      w0 := Domain:-Shape:-asConstraints(w0);
      kb1 := foldr(assert, kb, op(w0));
      if kb1 :: t_kb then
        m := weight(w, unintegrate(h, subintegral, kb1));
        if m :: Weight(anything, anything) then
          m := weight(simplify_factor_assuming(op(1,m), kb1), op(2,m));
        end if;
        piecewise_And(w0, m, Msum())
      else # if the domain is empty
        Msum()
      end if;
    elif e :: t_pw and not Partition:-ConditionsDepend(Partition:-PWToPartition(e), h) then
        kb_piecewise(e, kb, ((lhs, kb)-> lhs), ((rhs, kb)-> unintegrate(h, rhs, kb)));
    elif e :: Partition and not Partition:-ConditionsDepend(e, h) then
        kb_Partition(e, kb, ((lhs, kb)-> lhs), ((rhs, kb)-> unintegrate(h, rhs, kb)));
    elif e :: t_case then
      subsop(2=map(proc(b :: Branch(anything, anything))
                     eval(subsop(2='toLO:-unintegrate'(x,op(2,b),c),b),
                          {x=h, c=kb})
                   end proc,
                   op(2,e)),
             e);
    elif e :: 'Context(anything, anything)' then
      kb1 := assert(op(1,e),kb);
      if kb1 :: t_kb then
          subsop(2=unintegrate(h, op(2,e), kb1), e);
      else# A contradictory `Context' implies anything, so produce 'anything'
          # In particular, 42 :: t_Hakaru = false, so a term under a false
          # assumption should never be inspected in any way.
          42
      end if;

    elif e :: 'toLO:-integrate'('freeof'(h), 'anything', identical([])) then
      x := mk_sym('x', op(2,e));
      # If we had HType information for op(1,e),
      # then we could use it to tell kb about x.
      (w, m) := unweight(unintegrate(h, applyintegrand(op(2,e), x), kb));
      (w, w0) := factorize(w, x, kb);
      weight(w0, bind(op(1,e), x, weight(w, m)))
    # elif e :: identical('undefined') then
      # an undefined term can become anything
      # Msum()

    else
      # Failure: return residual LO
      LO(h, e)
    end if
  end proc;

  export
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

  export
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

  local
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

  local
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

  local
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


  # (s,r):=factorize(e,var,kb) expresses e in the context kb as s*r,
  # where r doesn't depend on var and s is as simple as possible
  # (and non-negative if possible).
  local
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
  local
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


  local
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

end module; # fromLO
