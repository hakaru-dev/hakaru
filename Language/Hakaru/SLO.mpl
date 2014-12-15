# SLO = Simplify Linear Operator.
#
#  This assumes that the input is the output of Language.Hakaru.Syntax.tester
# No checking is done that this is actually the case.
#
# SLO : simplifier
# AST : takes simplified form and transform to AST
#

SLO := module ()
  export ModuleApply, AST, simp, c; # very important: this c is "global".
  local ToAST, t_binds, t_pw, into_pw, myprod, gensym, gs_counter, do_pw,
    superpose;

  t_binds := 'specfunc(anything, {int, Int, sum, Sum})';
  t_pw := 'specfunc(anything, piecewise)';

  ModuleApply := proc(inp::anything) 
    local e;
    try
      simp(value(eval(inp(c), 'if_'=piecewise)));
    catch "Wrong kind of parameters in piecewise":
      error "Bug in Hakaru -> Maple translation, piecewise used incorrectly.";
    end try;
  end proc;

  # AST transforms the Maple to a representation of the mochastic AST
  AST := proc(inp::anything)
    local cs;
    cs := indets(inp, 'specfunc'(anything,c));
    # deal with trivial input first
    if inp=0 then
        Superpose()
    # then deal with 'bad' input
    elif nops(cs) = 0 then
      error "the constant", inp, " is not a measure."
    else 
      ToAST(inp, []);
    end if;
  end proc;

  # recursive function which does the main translation
  ToAST := proc(e, ctx)
    local a0, a1, var, vars, rng, ee, cof, d, ld, weight, binders,
      v, subst, ivars, ff, newvar, rest, a, b;
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
            ff := (x,y) -> WM(simplify(x), Return(op(y)));
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
          return do_pw(map(simplify, [op(e)]), ctx);
        else
          error "no binders, but still not a polynomial?", ee
        end if;
      else
        if type(e, 'specfunc'(anything, {'int','Int'})) then
          var, rng := op(op(2,e));
          ee := op(1,e);
          weight := simplify(op(2,rng)-op(1,rng));
          if type(weight, 'SymbolicInfinity') then
            rest := ToAST(ee, [op(2,e), op(ctx)]);
            # should recognize densities here
            Bind(Lebesgue, var = rng, rest)
          else
            rest := ToAST(weight*ee, [op(2,e), op(ctx)]);
            # process the rest, and then recognize
            # recognize 'raw' uniform
            if type(rest, specfunc(identical(var), 'Return')) then
              Uniform(op(rng));
            elif type(rest, 'Superpose'('WM'(anything, anything))) then
              # finite range.
              weight := simplify(op([1,1], rest));
              ee := op([1,2], rest);
              if type(ee, Return(anything)) then
                Bind(Uniform(op(1, rng), op(2, rng)), var,
                    Superpose(WM(weight, simplify(ee))))
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
          return do_pw(map(simplify, [op(e)]), ctx);
        elif type(e, `+`) then
          superpose(map(ToAST, [op(e)], ctx));
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
              Superpose(WM(b, ToAST(a, ctx)))
            else
              error "something weird happened:", a, " was supposed to be pw"
            end if
          elif type(a, `*`) then
            error "product of 2 binders?!?", a
          else
            Superpose(WM(b, ToAST(a, ctx)))
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

  superpose := proc(l)
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
    Superpose(seq(WM(t[op(i)], op(i)), i = [indices(t)]));
  end proc;
end;

# this has to be global!
unsafeProb := proc(v) 
  if type(v,'realcons') and signum(0, v, 1) = 1 then v else 'unsafeProb'(v) end if;
end proc;

# will get called on expressions containing 'unsafeProb'
`simplify/unsafeProb` := proc(x) local sub, f;
  sub := indets(x, 'specfunc'(anything, unsafeProb));
  f := proc(a) local b;
    b := op(1,a);
    if type(b, 'exp'(anything)) then exp_(op(1, b)) else a end if;
  end proc;
  subs(map(y -> y = f(y), sub), x)
end proc;

# works, but could be made more robust
`evalapply/if_` := proc(f, t) if_(op(1,f), op(2,f)(t[1]), op(3,f)(t[1])) end;
