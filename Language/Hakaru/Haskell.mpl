# Haskell -- this is a "to Haskell" 'printing' module.
#
# It will eventually have two exports:
# 1. SLO - to print our AST representation of linear operators
# 2. Expr - to print Maple expressions in Haskell, at least for those
#           which are translateable in a straightforward manner.

Haskell := module ()
  export SLO, Expr;
  local b, p, d,
      parens;
  uses StringTools;

  SLO := proc(ast) error "Haskell:-SLO not implemented yet" end;

  # this is to make things more efficient.  Note that it makes
  # things non-reentrant between Expr and p.
  b := StringBuffer();

  # for the long-term, go right to the 'right' way to do this,
  # which is to use the Inert form.  The flip-side of doing things
  # the right way would involve a proper pretty-printer, but that
  # can be added later easily enough.
  Expr := proc(expr) 
      b:-clear();
      p(ToInert(expr));
      b:-value();
  end;

  p := proc(e)
    if assigned(d[op(0,e)]) then
      d[op(0,e)](op(e))
    else
      error "Haskell:-d %1 not implemented yet", op(0,e)
    end if;
  end;

# things get silly with too much indentation, so for this table, we cheat
d[_Inert_INTPOS] := proc(x) b:-appendf("%d",x) end;
d[_Inert_RATIONAL] := proc(n,d) 
  parens(proc() p(n); b:-append(" % "); p(d); end) 
end;

  parens := proc(c) b:-append("("); c(); b:-append(")") end;
end module:
