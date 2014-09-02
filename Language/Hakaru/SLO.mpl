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
    error "AST is not implemented yet"
  end proc;
end;
