# SLO = Simplify Linear Operator.
#
#  This assumes that the input is the output of Language.Hakaru.Syntax.tester
# No checking is done that this is actually the case.
#
# SLO : simplifier
# AST : takes simplified form and transform to AST
#

SLO := module ()
  export ModuleApply, AST, simp,
    c; # very important: c is "global".
  local ToAST, t_binds, t_pw, into_pw_prod, into_pw_plus, myprod, do_pw,
    mkProb, getCtx, instantiate, lambda_wrap, fill_table, toProp,
    adjust_types, compute_domain, analyze_cond, flip_cond, isPos,
    adjust_superpose,
    add_pw, get_bp, merge_pw,
    MyHandler, getBinderForm, infer_type, join_type, join2type,
    simp_sup, simp_if, into_sup, simp_rel,
    comp2, comp_algeb, compare, comp_list,
    mkRealDensity, recognize_density, density;

  t_binds := 'specfunc(anything, {int, Int, sum, Sum})';
  t_pw := 'specfunc(anything, piecewise)';

  ModuleApply := proc(spec::Typed(anything,anything))
    local expr, typ, glob, gsiz, ctx, r, inp, meastyp, res, gnumbering;
    expr := op(1, spec);
    typ := op(2, spec);
    glob, gnumbering, gsiz, meastyp := getCtx(typ, {}, table(), 0);
    r := Record('htyp' = typ, 'mtyp' = meastyp,
                'gctx' = glob, 'gnum' = gnumbering, 'gsize' = gsiz);
    inp := instantiate(expr, r, 0, typ);
    try
      NumericEventHandler(division_by_zero = MyHandler);
      res := HAST(simp(value(eval(inp(c), 'if_'=piecewise))), r);
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

    # right at the start, put the global context in the 'path'.
    _EnvPathCond := map(toProp, ctx:-gctx);
    res := ToAST(op(inp));
    res := adjust_types(res, ctx:-mtyp, ctx);
    res := adjust_superpose(res);
    lambda_wrap(res, 0, ctx);
  end proc;

  # recursive function which does the main translation
  ToAST := proc(inp, ctx)
    local a0, a1, var, vars, rng, ee, cof, d, ld, weight, binders,
      v, subst, ivars, ff, newvar, rest, a, b, e, span;
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
          span := RealRange(op(1,rng), op(2,rng));
          if type(weight, 'SymbolicInfinity') then
            rest := ToAST(ee, ctx);
            if rng = -infinity..infinity then
              mkRealDensity(rest, var)
            else
              # recognize densities on partial range here
              Bind(Lebesgue, var = rng, rest)
            end if;
          else
            v := simplify(weight*ee) assuming var :: span;
            rest := ToAST(v, ctx);
            Bind(Uniform(op(rng)), var, rest);
          end if;
        elif type(e, 'specfunc'(anything, {'sum','Sum'})) then
          error "sums not handled yet"
        elif type(e, t_pw) then
          return do_pw(map(simplify, [op(e)]), ctx);
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

  # simp mostly recurses and simplifies as it goes
  simp := proc(e)
    local a, b, d, res;
    if type(e, `+`) then
      # first push constants in
      res := map(simp, e);
      # only worry about + of pw
      if not type(res, `+`) then return simp(res) end if; # it happens!
      a, b := selectremove(type, res, t_pw);
      if a = 0 then # none to worry about
        res
      else
        if type(a,`+`) then
          add_pw([op(a)]);
        else
          into_pw_plus(b, a)
        end if;
      end if;
    elif type(e, `*`) then
      a, b := selectremove(type, e, t_binds);
      # now casesplit on what a is
      if a=1 then  # no binders
        a, b := selectremove(type, e, t_pw);
        if a=1 then # and no piecewise at this level, deeper?
          map(simp, b); # b is a `*`
        elif type(a, `*`) then
          error "do not know how to multiply 2 pw: %1", a
        elif type(a, t_pw) then
          res := simplify(a);
          if type(res, t_pw) then
            into_pw_prod(b, res)
          else
            simp(b)*simp(res)
          end if;
        else
          error "something weird happened: (a) was supposed to be pw", a
        end if
      elif type(a, `*`) then
        error "product of 2 binders?!?: %1", a
      else
        # simp(b)*simp(a)
        subsop(1=myprod(simp(b),simp(op(1,a))), a)
      end if
    elif type(e, t_binds) then
      subsop(1=simp(op(1,e)), e)
    # need to go into pw even if there is no factor to push in
    elif type(e, t_pw) then
      into_pw_prod(1, e); # because this simplifies too
    elif type(e, anything ^ anything) then
      simp(op(1,e)) ^ simp(op(2,e))
    else
      simplify(e)
    end if;
  end;

  into_pw_plus := proc(ss, pw)
    local n, f;

    n := nops(pw);
    f := proc(j)
      if j=n then # last one is special, always a value
        simp(ss + simp(op(j, pw)))
      elif type(j,'odd') then # a condition
        simp_rel( op(j, pw) )
      else # j even
        simp(ss + simp(op(j, pw)))
      end if;
    end proc;
    piecewise(seq(f(i),i=1..n))
  end proc;

  into_pw_prod := proc(fact, pw)
    local n, f;

    n := nops(pw);
    f := proc(j)
      if j=n then # last one is special, always a value
        simp(myprod(fact, simp(op(j, pw))))
      elif type(j,'odd') then # a condition
        simp_rel( op(j, pw) )
      else # j even
        simp(myprod(fact , simp(op(j, pw))))
      end if;
    end proc;
    piecewise(seq(f(i),i=1..n))
  end proc;

  add_pw := proc(l)
    local breakpoints, sbp;

    breakpoints := map(get_bp, l);
    sbp := convert(breakpoints, 'set');
    if nops(sbp)=1 then
      merge_pw(l,'add');
    else
      error "multiple piecewises to be added with different breakpoints %1", l
    end if;
  end proc;

  merge_pw := proc(l, f)
    local i, n;
    n := nops(l[1]);
    piecewise(seq(`if`(i::odd and i<n, 
                      op(i,l[1]), 
                      f(op(i,j),j=l)), i=1..n))
  end proc;

  get_bp := proc(pw::specfunc(anything, piecewise))
    local i, n;
    n := nops(pw);
    [seq(`if`(i::odd and i<n, op(i,pw), NULL), i=1..n)]
  end proc;

  simp_rel := proc(r)
    if r::name then
      r
    elif r::{`<`,`<=`,`=`,`<>`} then
      map(simp_rel, r)
    elif r::specfunc(anything, {And, Or, Not}) then
      map(simp_rel, r)
    else
      simplify(r)
    end;
  end proc;

  # myprod takes care of pushing a product inside a `+`
  myprod := proc(a, b)
    if type(b,`+`) then
      map2(myprod, a, b)
    else
      a*b
    end if;
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
            if not isPos(rest) then WARNING("cannot insure it will not crash") end if;
            if pos = 1 then
              unsafeProb(rest); # res it the whole thing, don't recurse!
            else
              pos * mkProb(rest, ctx)
            end if;
          end if;
        else # otherwise rl is a single thing
          if not isPos(rl) then WARNING("cannot insure it will not crash") end if;
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
    elif type(w, anything^fraction) then
      typ := infer_type(op(1,w), ctx);
      if member(typ,{'Prob','Number'}) then 
        w 
      else 
        mkProb(op(1,w), ctx) ^ op(2,w) 
      end if;
    elif type(w, 'unsafeProb'(anything)) then
      error "there should be no unsafeProb in %1", w
    else
      typ := infer_type(w, ctx);
      if member(typ, {'Prob', 'Number'}) then
        w
      elif typ = 'Real' then
        # we are going to need to cast.  Is it safe?
        if not isPos(w) then WARNING("cannot insure it will not crash") end if;
        unsafeProb(w);
      else
        error "how do I make a Prob from %1 in %2", w, eval(_EnvPathCond)
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

  toProp := proc(x)
    if type(x,`=`) then op(1,x) :: toProp(op(2,x))
    elif type(x, 'symbol') then
      if x = 'Real' then 'real'
      elif x = 'Prob' then RealRange(0,infinity)
      elif x = 'Bool' then boolean
      elif x = 'Unit' then identical(Unit)
      else
        error "Unknown base type %1", x
      end if;
    else
      error "How can I make a property from %1", x;
    end if;
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

  lambda_wrap := proc(expr, cnt, ctx)
    local var, sub;
    if cnt = ctx:-gsize then
      expr
    else
      var := ctx:-gnum[cnt];
      if type(var, 'name') then
        Lambda(var, lambda_wrap(expr, cnt+1, ctx));
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
    elif type(e, boolean) then
      'Bool'
    elif type(e, anything^integer) then
      infer_type(op(1,e), ctx);
    elif type(e, {'exp'(anything), 'cos'(anything), 'sin'(anything)}) then
      typ := infer_type(op(1,e), ctx); # need to make sure it is inferable
      'Real' # someone else will make sure to cast this correctly
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
        res := select(type, _EnvPathCond, identical(e) :: anything);
        if nops(res)=1 then 
          typ := op([1,2], res);
          if type(typ, {'RealRange'(anything, anything), identical(real)}) then
            'Real'
          else
            typ
          end if;
        else
          error "Impossible: an untyped free variable %1 in local context %2",
            e, eval(_EnvPathCond)
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
      _EnvPathCond := _EnvPathCond union {var :: real};
      Bind(Lebesgue, var, adjust_types(op(3,e), typ, ctx));
    elif type(e, 'Bind'(anything, name, anything)) then
      dom := compute_domain(op(1,e));
      var := op(2,e);
      inf_typ := infer_type(op(1,e), ctx);
      _EnvPathCond := _EnvPathCond union {var :: dom};
      # need to adjust types on first op, to its own type, as that may require
      # tweaking which functions are used
      Bind(adjust_types(op(1,e), inf_typ, ctx), var, adjust_types(op(3,e), typ, ctx));
    elif type(e, 'Bind'(identical(Lebesgue), name = range, anything)) then
      dom := RealRange(op([2,2,1],e), op([2,2,2], e));
      var := op([2,1],e);
      _EnvPathCond := _EnvPathCond union {var :: dom};
      Bind(op(1,e), var, adjust_types(op(3,e), typ, ctx));
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
    elif type(e, 'NormalD'(anything, anything)) and typ = 'Measure(Real)' then
      NormalD(op(1,e), mkProb(op(2, e), ctx))
    else
     error "adjust_types of %1 at type %2", e, typ;
    end if;
  end proc;

  compute_domain := proc(e)
    local res;
    if type(e, 'Uniform'(anything, anything)) then
      'RealRange'(op(e));
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

  flip_cond := proc(cond)
    if type(cond, `<`) then op(2,cond) <= op(1,cond)
    elif type(cond, `<=`) then op(2,cond) < op(1,cond)
    elif type(cond, `=`) then op(1,cond) <> op(2,cond)
    else
      error "Don't know how to deal with condition %1", cond
    end if;
  end proc;

  # while inside the evaluator, we want infinities
  MyHandler := proc(operator, operands, default_value)
    NumericStatus( division_by_zero = false);
    if operator='ln' then -infinity else default_value end if;
  end proc;

  # dirac < uniform < NormalD < bind < WeightedM < SUPERPOSE
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
    elif x::specfunc(anything, 'SUPERPOSE') then
      if y::specfunc(anything, 'SUPERPOSE') then
        error "cannot compare 2 SUPERPOSE %1, %2", x, y
      else
	evalb(not member(op(0,y), '{Return, Uniform, NormalD, WeightedM, SUPERPOSE}'));
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

  # density recognizer
  recognize_density := proc(dens, var)
    local de, init, diffop, Dx, a0, a1, scale, at0, mu, sigma;
    de := gfun[holexprtodiffeq](dens, f(var));
    init, de := selectremove(type, de, `=`);
    if nops(init)=1 and nops(de)=1 then
      init := rhs(init[1]);
      de := de[1];
      diffop := DEtools[de2diffop](de, f(var), [Dx, var]);
      if degree(diffop, Dx) = 1 then
	a0 := coeff(diffop, Dx, 0);
	a1 := coeff(diffop, Dx, 1);
	if degree(a0, var) = 1 and degree(a1, var) = 0 then
          scale := coeff(a0, var, 1);
          mu := -coeff(a0, var, 0)/scale;
          sigma := sqrt(coeff(a1, var, 0)/scale);
          at0 := simplify(eval(init/density[NormalD](mu, sigma, 0)));
          return WeightedM(at0, NormalD(mu,sigma));
	end if;
      end if;
    end if;
    NULL;
  end proc;

  mkRealDensity := proc(dens, var)
    local res, new_dens;
    if dens :: specfunc(anything, 'WeightedM') then
      res := recognize_density(op(1,dens), var);
      if res<>NULL then
        Bind(res, var, op(2,dens))
      else
        Bind(Lebesgue, var, dens)
      end if;
    elif dens :: specfunc(anything, 'Bind') then
      new_dens := mkRealDensity(op(1, dens), var);
      # uses associatibity of >>=
      Bind(op(1, new_dens), op(2, new_dens), 
        Bind(op(3, new_dens), op(2, dens), op(3, dens)));
    else
      Bind(Lebesgue, var, dens)
    end if
  end proc;

  density[NormalD] := proc(mu, sigma, x)
    1/sigma/sqrt(2)/sqrt(Pi)*exp(-(x-mu)^2/2/sigma^2)
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
  elif meas :: 'WeightedM'(anything, 'Return'(identical(var))) and
    not depends(op(1, meas), var) then
    WeightedM(op(1,meas), w)
  else
    'Bind'(w, var, meas)
  end if;
end proc;

If := proc(cond, tb, eb)
  if cond = true then
    tb
  elif cond = false then
    eb
  elif tb = Return(undefined) then
    eb
  elif eb = Return(undefined) then
    tb
  elif tb = eb then
    eb
  elif type(cond, anything = identical(true)) then
    If(op(1,cond), tb, eb)
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
