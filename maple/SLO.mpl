# SLO = Simplify Linear Operator.
#
#  This assumes that the input is the output of Language.Hakaru.Syntax.tester
# No checking is done that this is actually the case.
#
# SLO : simplifier
# AST : takes simplified form and transform to AST
#

SLO := module ()
  export ModuleApply, AST, simp, flip_cond,
    c; # very important: c is "global".
  local ToAST, t_binds, t_pw, t_rel,
    into_pw, myprod, do_pw,
    mkProb, getCtx, instantiate, lambda_wrap, find_paths,
    fill_table, toProp, toType,
    twiddle, myint, myint_pw,
    adjust_types, compute_domain, analyze_cond, isPos,
    adjust_superpose,
    get_breakcond, merge_pw,
    MyHandler, getBinderForm, infer_type, join_type, join2type,
    simp_sup, simp_if, into_sup, simp_rel, 
    simp_pw, simp_pw_equal, simp_pw3,
    comp2, comp_algeb, compare, comp_list,
    get_de, mkRealDensity, recognize_density, recognize_density_01, density;

  t_binds := 'specfunc(anything, {int, Int, sum, Sum})';
  t_pw := 'specfunc(anything, piecewise)';
  t_rel := {`<`,`<=`,`=`,`<>`};

  ModuleApply := proc(spec::Typed(anything,anything))
    local expr, typ, glob, gsiz, ctx, r, inp, meastyp, res, gnumbering;
    expr := op(1, spec);
    typ := op(2, spec);
    glob, gnumbering, gsiz, meastyp := getCtx(typ, {}, table(), 0);
    r := Record('htyp' = typ, 'mtyp' = meastyp,
                'gctx' = glob, 'gnum' = gnumbering, 'gsize' = gsiz);
    inp := instantiate(expr, r, 0, typ);
    try
      # be context sensitive for this pass too:
      _EnvBinders := {};
      NumericEventHandler(division_by_zero = MyHandler);
      res := HAST(simp(eval(simp(eval(inp(c), 'if_'=piecewise)), Int=myint)), r);
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

    ctx := op(2,inp);

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
      v, subst, ivars, ff, newvar, rest, a, b, e;
    e := inp; # make e mutable
    if type(e, specfunc(name, c)) then
      return Return(op(e))
    # we might have recursively encountered a hidden 0
    elif (e = 0) then
      return Superpose()
    # we might have done something odd, and there is no x anymore (and not 0)
    elif type(e, 'numeric') then
      error "the constant %1 is not a measure", e
    # invariant: we depend on c
    else
      binders := indets(e, t_binds);
      vars := indets(e, specfunc(anything, c));
      subst := map(x-> x = op(0,x)[op(x)], vars);
      ivars := map2(op, 2, subst);
      if binders = {} then
        # this is a 'raw' measure, with no integrals
        ee := subs(subst, e);
        if type(ee, 'polynom'(anything,ivars)) then
          ee := collect(ee, ivars, simplify);
          d := degree(ee, ivars);
          ld := ldegree(ee, ivars);
          cof := [coeffs(ee, ivars, 'v')]; # cof is a list, v expseq
          if (d = 1) and (ld = 1) then
            ff := (x,y) -> WeightedM(simplify(x), Return(op(y)));
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
          error "sums not handled yet"
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
      ee, vars, all_vars, num, den, push_in, i,
      cs, simp_poly, simp_prod, simp_npw;

    simp_npw := zz -> `if`(op(1,zz)::t_pw, into_pw(SLO:-c,op(1,zz)), zz);
    if e=undefined or e::numeric then return e end if;
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
      local actual, cof;
      cof := c;
      if v=1 then return cof end if;
      actual := thaw(v);
      if type(actual, t_binds) then
        _EnvBinders := _EnvBinders union {op([2,1], actual)};
        op(0,actual)(simp(cof*op(1,actual)), op(2,actual))
      elif type(actual, t_pw) then
        actual := simplify(actual); # might get rid of pw!
        `if`(actual::t_pw, into_pw((x -> cof * x), actual), cof*actual);
      elif degree(v, vars)>1 then 
        if type(actual, '`*`'(t_pw)) then
          into_pw((x -> cof * x), merge_pw([op(actual)], mul));
        else
          error "product? (%1)", actual
        end if;
      else
        error "how can (%1) not be a binder, pw or c?", v
      end if;
    end proc;

    simp_poly := proc(p)
      local coef_q, vars_q, q, c0, res, heads;
      q := collect(p, all_vars , 'distributed', simplify);
      if ldegree(q, vars)<1 then
        # need to 'push in' additive constant sometimes
        c0 := tcoeff(q, vars);
        q := q - c0; # this should work because of the collect
      else
        c0 := 0;
      end if;
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
      if op(1,ee)::t_pw then
        ee := into_pw((x -> Pair(x, op(2,ee))), op(1,ee))
      elif op(2,ee)::t_pw then
        ee := into_pw((x -> Pair(op(1,ee), x)), op(2,ee))
      end if;
    else
      error "ee (%1) should be ratpoly in (%2)", ee, vars;
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

  merge_pw := proc(l::list, f)
    local breakpoints, sbp, i, n, res;

    breakpoints := convert(map(get_breakcond, l), 'set');
    sbp := map(twiddle, breakpoints);
    n := nops(l[1]);
    if nops(sbp)=1 then
      res := simp_pw(piecewise(seq(`if`(i::odd and i<n, 
                                   op(i,l[1]), 
                                   f(op(i,j),j=l)), i=1..n)));
      simp(res);
    else
      error "multiple piecewises with different breakpoints %1", l
    end if;
  end proc;

  get_breakcond := proc(pw::specfunc(anything, piecewise))
    local i, n;
    n := nops(pw);
    [seq(`if`(i::odd and i<n, op(i,pw), NULL), i=1..n)]
  end proc;

  simp_rel := proc(r)
    if r::name then
      r
    elif r::t_rel then
      # special case
      if r = ('Right' = 'Left') then
        false
      else
        map(simp_rel, r)
      end if;
    elif r::specfunc(anything, {And, Or, Not}) then
      map(simp_rel, r)
    else
      simp(r)
    end;
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
  simp_pw := proc(pw)
    local res, cond, l, r, b1, b2, b3, rel, new_cond;
    res := simp_pw_equal(pw);
    if nops(res)=3 then
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
          res := piecewise(And(op(1,res),op([2,1],res)), op([2,2],res), op(3,res));
      end if;
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

  mkProb := proc(w, ctx)
    local typ, pb, rl, pos, rest;
    if type(w, `*`) then
      pb, rl := selectremove(x->evalb(infer_type(x,ctx)=Prob), w);
      # all parts are Prob
      if rl = 1 then
        pb
      else
        # if there are multiple Real parts
        if type(rl, `*`) then
          pos, rest := selectremove(isPos, rl);
          # deal with pos part right away:
          pos := pb * maptype(`*`, mkProb, pos, ctx);
          if rest = 1 then
            pos
          else
            # make sure the rest really is positive
            # if not isPos(rest) then WARNING("cannot insure it will not crash") end if;
            if pos = 1 then
              unsafeProb(rest); # res it the whole thing, don't recurse!
            else
              pos * mkProb(rest, ctx)
            end if;
          end if;
        else # otherwise rl is a single thing
          # if not isPos(rl) then WARNING("cannot insure it will not crash") end if;
          if pb = 1 then
            unsafeProb(rl); # rl is the whole thing, don't recurse!
          else
            pb * mkProb(rl, ctx); # go ahead
          end if;
        end if;
      end if;
    elif type(w, 'exp'(anything)) then
      exp_(op(1,w));
    elif type(w, 'erf'(anything)) then
      erf_(mkProb(op(1,w)));
    elif type(w, 'ln'(anything)) then
      error "mkProb ln: %1", w;
    elif type(w, anything^{identical(1/2), identical(-1/2)}) then
      typ := infer_type(op(1,w), ctx);
      if member(typ,{'Prob','Number'}) then 
        w 
      else 
        mkProb(op(1,w), ctx) ^ op(2,w) 
      end if;
    elif type(w, anything^fraction) then # won't be sqrt
      unsafeProb(w);
    elif type(w, 'unsafeProb'(anything)) then
      error "there should be no unsafeProb in %1", w
    else
      typ := infer_type(w, ctx);
      if member(typ, {'Prob', 'Number'}) then
        w
      elif typ = 'Real' then
        # we are going to need to cast.  Is it safe?
        # if not isPos(w) then WARNING("cannot insure it will not crash") end if;
        unsafeProb(w);
      else
        error "how do I make a Prob from %1 in %2", w, eval(_EnvTypes)
      end if;
    end if;
  end proc;

  # use assumptions to figure out if we are actually positive, even
  # when the types say otherwise
  isPos := proc(w)
    local res;

    res := signum(0, w, 1) assuming op(_EnvPathCond);
    evalb(res = 1);
  end proc;

  toProp := proc(x::`=`)
    local nm, typ, prop, rest, left, right, r1, r2;
    (nm, typ) := op(x);

    if type(typ, 'symbol') then
      if typ = 'Real' then (prop, rest) := 'real', {};
      elif typ = 'Prob' then (prop, rest) := RealRange(0,infinity), {};
      elif typ = 'Bool' then (prop, rest) := boolean, {};
      elif typ = 'Unit' then (prop, rest) := identical(Unit), {};
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
      else
        error "Real/Prob/Bool/Unit are the only base types: %1", typ;
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

  infer_type := proc(e, ctx)
    local typ, l, res;
    if type(e, boolean) then
      'Bool'
    elif e = 'Pi' then Prob
    elif e = 'Unit' then Unit
    elif e = 'Lebesgue' then Measure(Real)
    elif e = 'undefined' then Real
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
    elif type(e, anything^fraction) then
      infer_type(op(1,e), ctx); # need to make sure it is inferable
      # if it is <0, weird things will happen
      # someone else will make sure to cast this correctly
    elif type(e, 'erf'(anything)) then
      infer_type(op(1,e), ctx); # erf is Real, erf_ is Prob
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
    elif type(e, {'integer', 'fraction'}) then
      Number # constants are polymorphic!
    elif type(e, specfunc(anything, 'piecewise')) then
      typ := NULL;
      for l from 1 to nops(e) do
        if l::odd and l<nops(e) then
          next;
        else # last or e:: evan
          typ := typ, infer_type(op(l, e), ctx)
        end if;
      end do;
      join_type(typ);
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
    elif type(e, specfunc(anything, 'BetaD')) then
      Measure(Prob)
    elif type(e, 'Bind'(anything, name, anything)) then
      Measure(Real)
    elif type(e, 'Bind'(anything, name = range, anything)) then
      Measure(Real)
    else
      error "how do I infer a type from %1", e;
    end if;
  end proc;

  join2type := proc(a,b)
    if a = b then a
    elif a = 'Number' then b
    elif b = 'Number' then a
    elif a = 'Real' or b = 'Real' then 'Real' # we'll need to patch
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
    local ee, dom, opc, res, var, left, right, inf_typ, typ2, cond, fcond;
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
      elif typ2 = Real and member(inf_typ, {'Real', 'Number'}) then
        'Return'(op(1,e))
      elif typ2 :: Pair(anything, anything) and
           op(1,e) :: Pair(anything, anything) then
        left  := adjust_types('Return'(op([1,1],e)), Measure(op(1,typ2)), ctx);
        right := adjust_types('Return'(op([1,2],e)), Measure(op(2,typ2)), ctx);
        'Return'(Pair(op(1,left), op(1,right)));
      elif typ2 = Bool and member(op(1,e), {true,false}) then
        e
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
      dom := compute_domain(op(1,e));
      var := op([2,1],e);
      inf_typ := infer_type(op(1,e), ctx); # should assert Measure(..)
      _EnvTypes := _EnvTypes union {var :: op(1,inf_typ)};
      _EnvPathCond := _EnvPathCond union {var :: dom};
      # need to adjust types on first op, to its own type, as that may require
      # tweaking which functions are used
      Bind(adjust_types(op(1,e), inf_typ, ctx), op(2,e), adjust_types(op(3,e), typ, ctx));
    elif type(e, 'Bind'(anything, name, anything)) then
      dom := compute_domain(op(1,e));
      var := op(2,e);
      inf_typ := infer_type(op(1,e), ctx); # should assert Measure(..)
      _EnvTypes := _EnvTypes union {var :: op(1,inf_typ)};
      _EnvPathCond := _EnvPathCond union {var :: dom};
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
      opc := _EnvPathCond;
      _EnvPathCond := opc union {cond};
      left := adjust_types(op(2,e), typ, ctx);
      fcond := flip_cond(cond);
      _EnvPathCond := opc union {fcond};
      right := adjust_types(op(3,e), typ, ctx);
      If(cond, left, right);
    elif type(e, 'Uniform'(anything, anything)) and typ = 'Measure(Real)' then
      e
    elif type(e, 'Uniform'(anything, anything)) and typ = 'Measure(Prob)' then
      var := gensym('pp');
      Bind(e, var, Return(unsafeProb(var)))
    elif type(e, 'BetaD'(anything, anything)) and typ = 'Measure(Prob)' then
      BetaD(mkProb(op(1,e), ctx), mkProb(op(2,e), ctx))
    elif type(e, 'NormalD'(anything, anything)) and typ = 'Measure(Real)' then
      NormalD(op(1,e), mkProb(op(2, e), ctx))
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

  compute_domain := proc(e)
    local res;
    if type(e, 'Uniform'(anything, anything)) then
      'RealRange'(op(e));
    elif type(e, 'BetaD'(anything, anything)) then
      'RealRange'(0,1);
    elif type(e, {identical('Lebesgue'), specfunc(anything, 'NormalD')}) then
      'real'
    elif type(e, specfunc(anything, 'Superpose')) then
      res := map((x -> compute_domain(op(2,x))), {op(e)});
      if nops(res)=1 then
        res[1]
      else
        error "expression %1 has multiple domain: %2", e, res
      end if;
    elif type(e, 'Bind'(anything, name, anything)) then
      'real'
    elif type(e, 'Bind'(anything, name = range, anything)) then
      RealRange(op([2,2,1], e), op([2,2,2], e))
    elif type(e, 'WeightedM'(anything, anything)) then
      compute_domain(op(2,e))
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
        constraints := eval(ii, f = (x -> c0*density[BetaD](a,b)(x)));
        sol := solve(constraints, c0);
        return WeightedM(eval(c0, sol), BetaD(a,b));
      # degenerate case with b=1
      elif degree(a0,var)=0 and degree(a1,var)=1 and normal(var + a1)=0 then
        a := coeff(a0, var, 0) + 1;
        constraints := eval(ii, f = (x -> c0*density[BetaD](a,1)(x)));
        sol := solve(constraints, c0);
        return WeightedM(eval(c0, sol), BetaD(a,1));
      # degenerate case with a=1
      elif degree(a0,var)=0 and degree(a1,var)=1 and normal(a1 - (var-1))=0 then
        b := -(coeff(a0, var, 0) - 1);
        constraints := eval(ii, f = (x -> c0*density[BetaD](1,b)(x)));
        sol := solve(constraints, c0);
        return WeightedM(eval(c0, sol), BetaD(1,b));
      # degenerate case with a=1, presented differently
      elif degree(a0,var)=0 and degree(a1,var)=1 and normal(a1 + (var-1))=0 then
        b := (coeff(a0, var, 0) + 1);
        constraints := eval(ii, f = (x -> c0*density[BetaD](1,b)(x)));
        sol := solve(constraints, c0);
        return WeightedM(eval(c0, sol), BetaD(1,b));
      end if;
    end if;
    NULL;
  end proc;


  mkRealDensity := proc(dens, var, rng)
    local de, res, new_dens, Dx, diffop, init;
    if dens :: specfunc(anything, 'WeightedM') then
      res := NULL;
      # no matter what, get the de.  
      # TODO: might want to switch from var=0 sometimes
      de := get_de(op(1,dens),var,Dx);
      if de::specfunc(anything, 'Diffop') then
        (diffop, init) := op(de);
        # dispatch on rng
        if rng = -infinity..infinity then
          res := recognize_density(diffop, init, Dx, var);
        elif rng = 0..1 then
          res := recognize_density_01(diffop, init, Dx, var);
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
    elif dens :: specfunc(anything, 'Return') then
      Bind(Uniform(op(1,rng), op(2,rng)), var, dens)
    else
      Bind(Lebesgue, var = rng, dens)
    end if
  end proc;

  density[NormalD] := proc(mu, sigma) proc(x)
    1/sigma/sqrt(2)/sqrt(Pi)*exp(-(x-mu)^2/2/sigma^2)
  end proc end proc;
  density[BetaD] := proc(a, b) proc(x)
    x^(a-1)*(1-x)^(b-1)/Beta(a,b)
  end proc end proc;

#############
# more hacks to get around Maple weaknesses
  myint := proc(expr, b)
    local var, inds;
    _EnvBinders := _EnvBinders union {op(1,b)};
    var := op(1,b);
    inds := indets(expr, specfunc(anything,c));
    inds := select(depends, inds, var);
    if inds={} then 
      if type(expr, t_binds) then
        subsop(1=myint(op(1,expr),b), expr)
      else
        int(expr, b) 
      end if;
    elif type(expr, t_pw) then
      # what is really needed here is to 'copy'
      # PiecewiseTools:-IntImplementation:-Definite
      myint_pw(expr, b)
    elif type(expr, t_binds) then
      # go in?
      Int(expr, b) 
    else 
      Int(expr, b) 
    end if;
  end proc;

  # need to deal better with other boundaries
  myint_pw := proc(expr, b :: name = identical(-infinity..infinity))
    local rels, n, rest, i, res, var, lower, cond;
    n := floor(nops(expr)/2);
    rels := [seq(op(2*i-1, expr), i=1..n)];
    rest := evalb(2*n < nops(expr));
    if type(rels, list({`<`, `<=`})) and indets(rels) = {op(1,b)} then
      res := 0; lower := -infinity; var := op(1,b);
      for i from 1 to n do
        cond := op(2*i-1, expr);
        if cond::{identical(var) < anything, identical(var) <= anything} then
          res := res + myint(op(2*i, expr), var = lower .. op(2,cond));
          lower := op(2,cond);
        elif cond::{anything < identical(var), anything <= identical(var)} then
          res := res + myint(op(2*i, expr), var = op(1,cond) .. infinity);
          lower := infinity;
        else
          error "cannot handle condition (%1) while integrating pw", cond;
        end if;
      end do;
      if rest then
        if lower = infinity then error "What the hey?" end if;
        res := res + myint(op(-1, expr), lower..infinity);
      end if;
      res
    else
      Int(expr, b)
    end if;
  end proc;
end;

# works, but could be made more robust
`evalapply/if_` := proc(f, t) if_(op(1,f), op(2,f)(t[1]), op(3,f)(t[1])) end;

# piecewise is horrible, so this hack takes care of some of it
if_ := proc(cond, tb, eb)
  if cond::name then
    if_(cond = true, tb, eb)
  else
    'if_'(cond, tb, eb)
  end if;
end proc;

WeightedM := proc(w, m)
  if w=1 then
    m
  elif type(m, specfunc(anything, 'Superpose')) then
    Superpose(op(map(into_sup, m, w)));
  elif type(m, specfunc(anything, 'WeightedM')) then
    WeightedM(w*op(1,m), op(2,m))
  else
    'WeightedM'(w,m)
  end if;
end;

Superpose := proc()
  local wm, bind, bindrr, i, j, bb, res, l;

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
        error "how do I superpose %1", i;
      end if;
    end do;
    res := [
      seq(WeightedM(wm[j], j), j = [indices(wm, 'nolist')]),
      seq(bb(bind,j,true), j = [indices(bind)]),
      seq(bb(bindrr,j,false), j = [indices(bindrr)])];
    if nops(res)=1 then res[1] else 'Superpose'(op(res)) end if;
  end if;
end proc;

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
  elif w='Lebesgue' and var::`=` and not(op([2,1],var) :: SymbolicInfinity)
        and not(op([2,2],var) :: SymbolicInfinity) then
    Bind(Uniform(op([2,1],var), op([2,2],var)), op(1,var), meas)
  elif w :: 'WeightedM'(anything, anything) then
    WeightedM(op(1,w), Bind(op(2,w), var, meas));
  else
    'Bind'(w, var, meas)
  end if;
end proc;

If := proc(cond, tb, eb)
  local patch_eb;
  patch_eb := proc(eb)
    local fcond, new_cond, rest_cond, t1, t2;

    fcond := SLO:-flip_cond(cond);
    new_cond := AndProp(op(1,eb), fcond);
    rest_cond := AndProp(SLO:-flip_cond(op(1,eb)), fcond);
    # note: if t1 is unsat, this might FAIL
    t1 := coulditbe(new_cond) assuming op(_EnvPathCond);
    try 
      # assume(rest_cond); # weird way to catch unsat!
      coulditbe(rest_cond) assuming rest_cond;
      t2 := true;
    catch "when calling '%1'. Received: 'contradictory assumptions'":
    # catch "the assumed property", "contradictory assumptions":
      t2 := false;
    end try;
    if t1=false then
      error "Why is %1 unsatisfiable?", new_cond;
    elif t2 then
      eb
    else
      op(2,eb)
    end if;
  end proc;

  if cond = true then
    tb
  elif cond = false then
    eb
  elif tb = 'Return'(undefined) then
    # must 'patch things up' if we had a nested If
    `if`(op(0,eb) = 'If', patch_eb(eb), eb);
  elif eb = Return(undefined) then
    tb
  elif tb = eb then
    eb
  elif type(cond, anything = identical(true)) then
    If(op(1,cond), tb, eb)
  elif op(0,eb) = 'If' and op(3,eb)=Superpose() then
    'If'(cond, tb, patch_eb(eb))
  else
    'If'(cond, tb, eb)
  end if;
end;

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
