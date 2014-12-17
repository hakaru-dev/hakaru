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
    c, arrrg; # very important: c and arrrg are "global".
  local ToAST, t_binds, t_pw, into_pw, myprod, gensym, gs_counter, do_pw,
    superpose, mkWM, mkProb, getCtx, addCtx, instantiate, lambda_wrap,
    adjust_types, compute_domain;

  t_binds := 'specfunc(anything, {int, Int, sum, Sum})';
  t_pw := 'specfunc(anything, piecewise)';

  ModuleApply := proc(spec::Typed(anything,anything))
    local expr, typ, glob, gsiz, ctx, r, inp, meastyp;
    expr := op(1, spec);
    typ := op(2, spec);
    glob, gsiz, meastyp := getCtx(typ, table(), 0);
    r := Record('htyp' = typ, 'mtyp' = meastyp,
                'gctx' = glob, 'gsize' = gsiz, 'lctx' = table());
    inp := instantiate(expr, r, 0);
    try
      HAST(simp(value(eval(inp(c), 'if_'=piecewise))), r);
    catch "Wrong kind of parameters in piecewise":
      error "Bug in Hakaru -> Maple translation, piecewise used incorrectly.";
    end try;
  end proc;

  # AST transforms the Maple to a representation of the mochastic AST
  AST := proc(inp::HAST(anything, Context))
    local res, ctx;
    res := ToAST(op(inp));
    ctx := op(2,inp);
    res := adjust_types(res, ctx, table());
    lambda_wrap(res, 0, ctx);
  end proc;

  getCtx := proc(typ, glob, ctr)
    if type(typ, 'Measure'(anything)) then
      glob, ctr, op(1,typ)
    elif type(typ, 'Arrow'(anything, anything)) then
      glob[ctr] := op(1,typ);
      getCtx(op(2,typ), glob, ctr+1)
    else 
      error "must have either Measure or Arrow, got", typ;
    end if;
  end proc;

  lambda_wrap := proc(expr, cnt, ctx)
    local var, sub;
    if cnt = ctx:-gsize then
      expr
    else
      var := cat('yy', cnt);
      sub := arrrg[cnt] = var;
      Lambda(var, lambda_wrap(subs(sub, expr), cnt+1, ctx));
    end if;
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
      error "the constant", e, "is not a measure"
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
            # WM = Weight-Measure pair
            ff := (x,y) -> mkWM(simplify(x), Return(op(y)), ctx);
            Superpose(op(zip(ff, cof, [v])));
            # `if`(cof=1, rest, Bind_(Factor(simplify(cof)), rest))
          else
            if (ld = 0) then
              error "non-zero constant encountered as a measure", ee
            else
              error "polynomial in c:", ee
            end if;
          end if;
        elif type(ee, t_pw) then
          return do_pw(map(simplify, [op(e)]), ctx, typ);
        else
          error "no binders, but still not a polynomial?", ee
        end if;
      else
        if type(e, 'specfunc'(anything, {'int','Int'})) then
          var, rng := op(op(2,e));
          if assigned(ctx:-lctx[var]) then
            # must alpha-rename
            newvar := gensym(_YY);
            e := subs(var = newvar, e);
            var := newvar;
          end if;
          ee := op(1,e);
          weight := simplify(op(2,rng)-op(1,rng));
          if type(weight, 'SymbolicInfinity') then
            rest := ToAST(ee, addCtx(op(2,e), ctx));
            # should recognize densities here
            Bind(Lebesgue, var = rng, rest)
          else
            v := simplify(weight*ee) 
                 assuming var :: RealRange(op(1,rng), op(2,rng));
            rest := ToAST(v, addCtx(op(2,e), ctx));
            # process the rest, and then recognize
            # recognize 'raw' uniform
            if type(rest, specfunc(identical(var), 'Return')) then
              if ctx:-mtyp = 'Real' then
                Uniform(op(rng));
              elif ctx:-mtyp = 'Prob' then
                if signum(0,op(1,rng),1) = 1 and
                   signum(0,op(2,rng),1) = 1 then
                  # someone will add the unsafeProb later
                  Bind(Uniform(op(rng)), var, Return(var));
                else
                  error "uniform with a negative range cannot be a Prob";
                end if;
              else
                error "uniform can only result in Real or Prob";
              end if;
            elif type(rest, 'Superpose'('WM'(anything, anything))) then
              # finite range.
              weight := simplify(op([1,1], rest));
              ee := op([1,2], rest);
              if type(ee, Return(anything)) then
                Bind(Uniform(op(1, rng), op(2, rng)), var,
                    Superpose(mkWM(weight, simplify(ee), ctx)))
              else
                error "almost uniform but not quite?", ee
              end if;
            else
              Bind(Lebesgue, var = rng, rest)
            end if;
          end if;
        elif type(e, 'specfunc'(anything, {'sum','Sum'})) then
          error "sums not handled yet"
        elif type(e, t_pw) then
          return do_pw(map(simplify, [op(e)]), ctx, typ);
        elif type(e, `+`) then
          superpose(map(ToAST, [op(e)], ctx), ctx);
        elif type(e, `*`) then
          # we have a binder in here somewhere
          a, b := selectremove(type, e, t_binds);
          # now casesplit on what a is
## from here
          if a=1 then  # no surface binders
            a, b := selectremove(type, e, t_pw);
            if a=1 then # and no piecewise either
              error "buried binder: ", b
            elif type(a, `*`) then
              error "do not know how to multiply 2 pw:", a
            elif type(a, t_pw) then
              Superpose(mkWM(b, ToAST(a, ctx), ctx))
            else
              error "something weird happened:", a, " was supposed to be pw"
            end if
          elif type(a, `*`) then
            error "product of 2 binders?!?", a
          else
            Superpose(mkWM(b, ToAST(a, ctx), ctx))
          end if
## to here
        else
            error "Not sure what to do with a ", e
        end if;
      end if;
    end if;
  end proc;

  # simp mostly recurses and simplifies as it goes
  simp := proc(e) 
    local a, b, d;
    if type(e, `+`) then
      map(simp, e)
    elif type(e, `*`) then
      a, b := selectremove(type, e, t_binds);
      # now casesplit on what a is
      if a=1 then  # no binders
        a, b := selectremove(type, e, t_pw);
        if a=1 then # and no piecewise either
          d := expand(b); # probably need to write something less brutal
          if b=d then # nothing happened
            simplify(b)
          else # this might be better
            simp(d)
          end if
        elif type(a, `*`) then
          error "do not know how to multiply 2 pw:", a
        elif type(a, t_pw) then
          into_pw(b, a)
        else
          error "something weird happened:", a, " was supposed to be pw"
        end if
      elif type(a, `*`) then
        error "product of 2 binders?!?", a
      else
        simp(b)*simp(a)
        # subsop(1=myprod(simp(b),simp(op(1,a))), a)
      end if
    elif type(e, t_binds) then
      subsop(1=simp(op(1,e)), e)
    # need to go into pw even if there is no factor to push in
    elif type(e, t_pw) then
      into_pw(1, e)
    else
      simplify(e)
    end if;
  end;

  into_pw := proc(fact, pw)
    local n, f;

    n := nops(pw);
    f := proc(j)
      if j=n then # last one is special, always a value
        simp(myprod(fact, simp(op(j, pw))))
      elif type(j,'odd') then # a condition
        op(j, pw)
      else # j even
        simp(myprod(fact , simp(op(j, pw))))
      end if;
    end proc;
    piecewise(seq(f(i),i=1..n))
  end proc;

  # myprod takes care of pushing a product inside a `+`
  myprod := proc(a, b)
    if type(b,`+`) then
      map2(myprod, a, b)
    else
      a*b
    end if;
  end proc;

  gs_counter := 0;
  gensym := proc(x::name) gs_counter := gs_counter + 1; x || gs_counter; end proc;

  # this assumes we are doing pw of measures.
  do_pw := proc(l, ctx)
    local len;
    len := nops(l);
    if len = 0 then Superpose()
    elif len = 1 then ToAST(l[1], ctx)
    else # l>=2. Note how conditions go through straight
      If(l[1], ToAST(l[2], ctx), thisproc(l[3..-1], ctx))
    end if;
  end;

  superpose := proc(l, ctx)
    local t, i, j, idx;
    t := table('sparse');
    for i in l do
      if type(i, specfunc(anything, Superpose)) then
        for j in [op(i)] do
          idx := op(2,j);
          # yeah for indexing functions!
          t[idx] := t[idx] + op(1,j);
        end do;
      else 
        error "still don't know how to superpose ", i;
      end if;
    end do;
    Superpose(seq(mkWM(t[op(i)], op(i), ctx), i = [indices(t)]));
  end proc;

  mkWM := proc(w, m, ctx)
    'WM'(mkProb(w, ctx), m);
  end proc;

  # note that this could be called more than once.
  mkProb := proc(w, ctx)
    local typ, i, ww, var, rng, sub;
    if type(w, 'realcons') and signum(0,w,1)=1 then 
      w
    elif type(w, `*`) then
      map(mkProb, w, ctx)
    elif type(w, 'specindex'(arrrg)) then
      typ := ctx:-gctx[op(1,w)];
      if typ = 'Prob' then w
      else error "how can I make a Prob from ", w, "of type ", typ;
      end if;
    elif type(w, 'exp'(anything)) then
      exp_(op(1,w));
    elif type(w, 'exp_'(anything)) then
      w
    elif type(w, 'unsafeProb'(anything)) then
      w
    else
      # use assumptions to figure out if we can 'do it'.
      ww := w;
      for i in [indices(ctx:-lctx, 'pairs')] do
          var := gensym(_ZZ);
          rng := rhs(i);
          if rng = -infinity..infinity then
            assume(var, real);
          elif type(rng, anything .. identical(infinity)) then
            assume(var >= op(1,rng));
          elif type(rng, identical(-infinity) .. anything) then
            assume(var <= op(2,rng));
          else
            assume(var, RealRange(op(1,rng), op(2,rng)));
          end if;
          sub := lhs(i) = var;
          ww := subs(sub, ww);
      end do;
      if signum(0, ww, 1) = 1 then
        unsafeProb(w)
      else
        error "how do I make a Prob from ", w, "in local ctx", eval(ctx:-lctx);
      end if;
    end if;
  end proc;

  # for adding to the local context.  Make it imperative!
  addCtx := proc(a, r) 
    local var, typ;
    var, typ := op(a);
    if assigned(r:-lctx[var]) then
      error "variable ", var, "seems to be used more than once in a binder"
    end if;
    r:-lctx[var] := typ;
    r;
  end proc;

  instantiate := proc(e, r, ctr)
    if ctr = r:-gsize then
      e
    else
      # only assume on Prob/Real, for now.
      if r:-gctx[ctr] = 'Prob' then
        assume(arrrg[ctr] >= 0);
      elif r:-gctx[ctr] = 'Real' then
        assume(arrrg[ctr], real);
      end if;
      instantiate(e(arrrg[ctr]), r, ctr+1)
    end if;
  end proc;

  ####
  # Fix-up the types using contextual information.
# TODO: need to add unsafeProb around the Prob-typed input variables,
# and then fix-up things like log.
  adjust_types := proc(e, ctx, pathcond)
    local ee, dom, opc, res;
    if type(e, specfunc(anything, 'Superpose')) then
      map(thisproc, e, ctx, pathcond)
    elif type(e, 'WM'(anything, anything)) then
      'WM'(mkProb(op(1,e), ctx), thisproc(op(2,e), ctx, pathcond));
    elif type(e, 'Return'(anything)) then
      if ctx:-mtyp = Unit and op(1,e) = Unit then
        e
      elif ctx:-mtyp = Prob then
        ee := op(1,e);
        res := mkProb(ee, ctx, pathcond);
        'Return'(res);
      elif ctx:-mtyp = Real then
        ee := op(1,e);
        if type(ee, 'realcons') then
          e;
        else
          error "Real: ", e
        end if;
      else
          error "type: ", ctx:-mtyp
      end if;
    elif type(e, 'Bind'(anything, name, anything)) then
      dom := compute_domain(op(1,e));
      if assigned(pathcond[op(2,e)]) then
        opc := pathcond[op(2,e)];
        pathcond[op(2,e)] := AndProp(opc, dom);
      else
        opc := NULL;
        pathcond[op(2,e)] := dom;
      end if;
      res := 'Bind'(op(1,e), op(2,e), adjust_types(op(3,e), ctx, pathcond));
      if opc=NULL then 
        unassign(pathcond[op(2,e)]) 
      else 
        pathcond[op(2,e)] := opc;
      end if;
      res;
    elif type(e, 'Bind'(identical(Lebesgue), name = range, anything)) then
      dom := RealRange(op([2,2,1],e), op([2,2,2], e));
      if assigned(pathcond[op(2,e)]) then
        opc := pathcond[op(2,e)];
        pathcond[op(2,e)] := AndProp(opc, dom);
      else
        opc := NULL;
        pathcond[op(2,e)] := dom;
      end if;
      res := 'Bind'(op(1,e), op(2,e), adjust_types(op(3,e), ctx, pathcond));
      if opc=NULL then 
        unassign(pathcond[op(2,e)]) 
      else 
        pathcond[op(2,e)] := opc;
      end if;
      res;
    elif type(e, 'If'(anything, anything, anything)) then
      error "If:", e;
    elif type(e, 'Uniform'(anything, anything)) then
      e
    else
     error "adjust_types ", e;
    end if;
  end proc;

  compute_domain := proc(e)
    if type(e, 'Uniform'(anything, anything)) then
      'RealRange'(op(e));
    else
      error "compute domain:", e;
    end if;
  end proc;
end;

# works, but could be made more robust
`evalapply/if_` := proc(f, t) if_(op(1,f), op(2,f)(t[1]), op(3,f)(t[1])) end;

# A Context contains 
# - a (Maple-encoded) Hakaru type 'htyp' (H-types)
# - a Measure type
# - a global context of var = H-types
# - the size of the global context
# - a local context of binders, var = range
`type/Context` := 'record'('htyp', 'mtyp', 'gctx', 'gsize', 'lctx');

if_ := proc(cond, tc, ec)
  if ec = false then And(cond, tc)
  elif tc = true then Or(cond, ec)
  else
      'if_'(cond, tc, ec)
  end if;
end proc;
