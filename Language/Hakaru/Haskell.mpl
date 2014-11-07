# Haskell -- this is a "to Haskell" 'printing' module.
#
# A single export
# This prints our AST representation of linear operators

Haskell := module ()
  export ModuleApply;
  local b, p, d,
      parens, resolve;
  uses StringTools;

  # this is to make things more efficient.  Note that it makes
  # things non-reentrant between Expr and p.
  b := StringBuffer();

  # for the long-term, go right to the 'right' way to do this,
  # which is to use the Inert form.  The flip-side of doing things
  # the right way would involve a proper pretty-printer, but that
  # can be added later easily enough.
  ModuleApply := proc(expr) 
      b:-clear();
      p(ToInert(expr));
      b:-value();
  end;

  p := proc(e)
    if assigned(d[op(0,e)]) then
      d[op(0,e)](op(e))
    else
      error "Haskell: %1 not implemented yet (%2)", op(0,e), e
    end if;
  end;

# things get silly with too much indentation, so for this table, we cheat
d[_Inert_INTPOS] := proc(x) b:-appendf("%d",x) end;
d[_Inert_RATIONAL] := proc(n,d) 
  parens(proc() p(n); b:-append(" % "); p(d); end) 
end;
d[_Inert_FUNCTION] := proc(f, s)
  local nm;
  nm := resolve(f);
  if assigned(bi[nm]) then
    bi[nm](op(s))
  else
    error "Haskell: cannot resolve function %1", f
  end if;
end proc;

# this is the table of known internal functions
bi["Bind_"] := proc(a1, a2) p(a1); b:-append(" `bind_` "); p(a2) end;

# utility routines:
# =================

# printing
  parens := proc(c) b:-append("("); c(); b:-append(")") end;

# resolve name
  resolve := proc(inrt)
    local s;
    if typematch(inrt, specfunc(s::string, '_Inert_NAME')) then
      s
    else
      error "cannot resolve an %1", op(0,inrt);
    end if;
  end proc;
end module:
