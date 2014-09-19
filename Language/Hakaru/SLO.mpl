# SLO = Simplify Linear Operator.
#
#  This assumes that the input is the output of Language.Hakaru.Syntax3.tester
# No checking is done that this is actually the case.
#

SLO := module ()
  export ModuleApply, AST, c; # very important: this c is "global".
  local ToAST;

  # right now, simplification means just evaluate!
  ModuleApply := proc(inp::anything) 
    try
      inp(c);
    catch "Wrong kind of parameters in piecewise":
      error "Bug in Hakaru -> Maple translation, piecewise used incorrectly.";
    end try;
  end proc;

  # AST transforms the Maple to a representation of the mochastic AST
  AST := proc(inp::anything)
    local cs;
    cs := indets(inp, 'specfunc'(anything,c));
    # deal with 'bad' input first.
    if nops(cs) = 0 then
      error "the constant", inp, " is not a measure."
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
    # we might have done something odd, and there is no x anymore
    elif type(e, 'numeric') then
      error "the constant", e, "is not a measure"
    # invariant: we depend on c
    else
      binders := indets(e, specfunc(anything, {'int', 'Int', 'sum', 'Sum'}));
      if binders = {} then
        ee := subs(cs=x, e);
        if type(ee, 'monomial'(anything,x)) then
          d := degree(ee, x);
          cof := coeff(ee, x, d); # pull off the constant
          rest := ToAST(cs, cs, x);
          `if`(cof=1, rest, Bind_(Factor(cof), rest))
        else
          error "no binders, but still not a monomial?"
        end if;
      else
        if type(e, 'specfunc'(anything, {'int','Int'})) then
          var, rng := op(op(2,e));
          ee := op(1,e);
          # recognize uniform
          if ee = c(var) then
              weight := (op(2,rng)-op(1,rng));
              `if`(weight=1, Uniform(rng), Bind_(Factor(weight), Uniform(rng)))
          else
            error var, rng, ee, cs;
          end if;
        else
          error "only integrals currently work"
        end if;
      end if;
    end if;
  end proc;
end;
