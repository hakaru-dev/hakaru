# SLO = Simplify Linear Operator.
#
#  This assumes that the input is the output of Language.Hakaru.Syntax.tester
# No checking is done that this is actually the case.
#
# SLO : simplifier
# AST : takes simplified form and transform to AST
# Print: (ToDo) print an AST back to Haskell
#

SLO := module ()
  export ModuleApply, AST, simp, c; # very important: this c is "global".
  local ToAST, t_binds, t_pw;

  t_binds := 'specfunc(anything, {int, Int, sum, Sum})';
  t_pw := 'specfunc(anything, piecewise)';

  ModuleApply := proc(inp::anything) 
    local e;
    try
      simp(inp(c));
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
        0
    # then deal with 'bad' input
    elif nops(cs) = 0 then
      error "the constant", inp, " is not a measure."
    elif type(inp, `+`) then
      map(AST, SUM(op(inp)))
    elif nops(cs) > 1 then 
      error "c occurs more than once - case not currently handled"
    else # invariant: c occurs exactly once
      cs := cs[1]; # the occurence of c
      ToAST(inp, cs);
    end if;
  end proc;

  # recursive function which does the main translation
  ToAST := proc(e, cs::'specfunc'(anything,c))
    local a0, a1, var, rng, ee, cof, d, rest, weight;
    if (e = cs) then
      return Return(op(cs))
    # we might have recursively encountered a hidden 0
    elif (e = 0) then
       return 0
    # we might have done something odd, and there is no x anymore (and not 0)
    elif type(e, 'numeric') then
      error "the constant", e, "is not a measure"
    # invariant: we depend on c
    else
      binders := indets(e, t_binds);
      if binders = {} then
        ee := subs(cs=x, e);
        if type(ee, 'polynom'(anything,x)) then
          d := degree(ee, x);
          cof := coeff(ee, x, d); # pull off the leading constant
          if (d = 1) and Testzero(cof*x^d - ee) then
              rest := ToAST(cs, cs);
              `if`(cof=1, rest, Bind_(Factor(simplify(cof)), rest))
          else
            error "polynomial in c:", ee
          end if;
        elif type(ee, t_pw) then
          error "encountered piecewise, case not done yet"
        else
          error "no binders, but still not a polynomial?", ee
        end if;
      else
        if type(e, 'specfunc'(anything, {'int','Int'})) then
          var, rng := op(op(2,e));
          ee := op(1,e);
          # recognize uniform
          if ee = c(var) then
              weight := (op(2,rng)-op(1,rng));
              `if`(weight=1, Uniform(rng), Bind_(Factor(weight), Uniform(rng)))
          elif rng = -infinity..infinity then
              Bind(Lebesgue(var), ToAST(ee, cs))
          else
              Bind(Lebesgue(var=rng), ToAST(ee, cs))
          end if;
        elif type(e, 'specfunc'(anything, {'sum','Sum'})) then
            error "sums not handled yet"
        else
            error "constants should have been pushed inside already", e
        end if;
      end if;
    end if;
  end proc;

  # simp mostly pushes things in.
  simp := proc(e) 
    local a, b;
    if type(e, `+`) then
      map(simp, e)
    elif type(e, `*`) then
      a, b := selectremove(type, e, t_binds);
      # now casesplit on what a is
      if a=1 then  # no binders
        a, b := selectremove(type, e, t_pw);
        if a=1 then # and no piecewise either, just plain simplify
          simplify(b)
        elif type(a, `*`) then
          error "do not know how to multiply 2 pw:", a
        elif type(a, t_pw) then
          # error "need to push ", b, "into a piecewise"
          e
        else
          error "something weird happened:", a, " was supposed to be pw"
        end if
      elif type(a, `*`) then
        error "product of 2 binders?!?", a
      else
        subsop(1=simp(b)*simp(op(1,a)), a)
      end if
    elif type(e, t_binds) then
      subsop(1=simp(op(1,e)), e)
    else
      simplify(e)
    end if;
  end;
end;
