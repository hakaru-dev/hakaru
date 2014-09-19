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
    local cs, x, e;
    cs := indets(inp, 'specfunc'(anything,c));
    # deal with 'bad' input first.
    if nops(cs) = 0 then
      error "the constant", inp, " is not a measure."
    elif nops(cs) > 1 then 
      error "c occurs more than once - case not currently handled"
    else # invariant: c occurs exactly once
      cs := cs[1]; # the occurence of c
      e := subs(cs=x, inp); # use x rather than the non-name cs
      ToAST(e, cs, x);
    end if;
  end proc;

  # recursive function which does the main translation
  ToAST := proc(e, cs::'specfunc'(anything,c), x::name)
    local a0, a1, var, rng, ee, c, d, rest;
    if (e = x) then
      return Return(op(cs))
    # we might have done something odd, and there is no x anymore
    elif type(e, 'constant') then
      error "the constant", e, "is not a measure"
    # invariant: we depend on x
    elif type(e, 'monomial'(anything,x)) then
      d := degree(e, x);
      c := coeff(e, x, d); # pull off the constant
      rest := ToAST(x, cs, x);
      `if`(c=1, rest, Bind_(Factor(c), rest))
    elif type(e, 'specfunc'(anything, 'int')) then
      var, rng := op(op(2,e));
      ee := op(1,inp);
      # recognize uniform
      if ee = c(var) then
          # the pre-factor should cancel out
          (op(2,rng)-op(1,rng))*Uniform(rng)
      else
        error var, rng, ee;
      end if;
    else
      error "Only measures linear in c(Unit) currently work."
    end if;
  end proc;
end;
