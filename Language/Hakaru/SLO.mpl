# SLO = Simplify Linear Operator.
#
#  This assumes that the input is the output of Language.Hakaru.Syntax3.tester
# No checking is done that this is actually the case.
#

SLO := module ()
  export ModuleApply, AST, c; # very important: this c is "global".

  # right now, simplification means just evaluate!
  ModuleApply := proc(inp) inp(c) end proc;

  # AST transforms the Maple to a representation of the mochastic AST
  AST := proc(inp)
    local a0, a1, cs, x, e;
    cs := indets(inp, 'specfunc'(anything,c));
    if nops(cs) = 0 then
      error "constants are not measures!"
    elif nops(cs) > 1 then 
      error "c occurs more than once - case not currently handled"
    else # c occurs exactly once
      cs := cs[1]; # the occurence of c
      e := subs(cs=x, inp); # use x rather than the non-name cs
      if op(cs)=Unit and ispoly(e, 'linear', x, 'a0', 'a1') then
        if not testeq(a0) then
          error "constants are not measures!"
        else
          Factor(a1)
        end if;
      elif type(inp, 'specfunc'(anything, 'int')) then
        var, rng := op(op(2,inp));
        e := op(1,inp);
        # recognize uniform
        if e = c(var) then
            # the pre-factor should cancel out
            (op(2,rng)-op(1,rng))*Uniform(rng)
        else
          error var, rng, e;
        end if;
      else
        error "Only measures linear in c(Unit) currently work."
      end if;
    end if;
  end proc;
end;
