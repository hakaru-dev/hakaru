# Haskell -- this is a "to Haskell" 'printing' module.
#
# A single export
# This prints our AST representation of linear operators

Haskell := module ()
  export ModuleApply;
  local b, p, d, bi,
      parens, resolve, sp, ufunc, bfunc, lbrack, rbrack, seqp,
      lparen, rparen;
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
d[_Inert_INTNEG] := proc(x) b:-appendf("(%d)",-x) end;
d[_Inert_RATIONAL] := proc(n,d) 
  parens(proc() p(n); b:-append(" / "); p(d); end) 
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
# ignore a2 and subsequent things below
d[_Inert_ASSIGNEDNAME] := proc(a1, a2)
  if assigned(bi[a1]) then
    bi[a1]()
  else
    b:-append(a1);
  end if;
end proc;
d[_Inert_NAME] := proc(a1) 
  if assigned(bi[a1]) then
    bi[a1]()
  else
    b:-append(a1);
  end if;
end proc;
# PROD is n-ary
d[_Inert_PROD] := proc()
  lparen(); seqp(" * ", [_passed]); rparen();
end;
d[_Inert_POWER] := proc(a1,a2)
  # should be Int "^" Int
  #        or Real "^^" Int
  #        or Prob "^^" Int
  #        or Real "**" Real
  #        or Prob "`pow_`" Real
  parens(proc() p(a1); b:-append(" ^ "); p(a2) end);
end;

# this is the table of known internal functions
bi["Bind_"] := proc(a1, a2) p(a1); b:-append(" `bind_` "); p(a2) end;
bi["Return"] := ufunc("dirac");
bi["Factor"] := ufunc("factor");
bi["unsafeProb"] := ufunc("unsafeProb");
bi["Unit"] := proc() b:-append("unit") end;
bi["Uniform"] := bfunc("uniform ");
bi["Lebesgue"] := proc() b:-append("lebesgue") end;
bi["Pi"] := proc() b:-append("pi_") end;

bi["Bind"] := proc(meas, rng, rest)
  p(meas);
  b:-append(" `bind` \\");
  if type(rng, specfunc(anything,'_Inert_NAME')) then
    b:-append(op(1,rng));
    b:-append(" -> ");
  else
    error "variable range in `bind` not yet handled";
  end if;
  p(rest);
end;

bi["Superpose"] := proc() b:-append("superpose"); sp(); 
  lbrack(); seqp(", ", [_passed]); rbrack();
end;

bi["WM"] := proc(w, m)
  b:-append("("); p(w); b:-append(","); p(m); b:-append(")");
end;

bi["exp"] := ufunc("exp");
bi["exp_"] := ufunc("exp_");

# utility routines:
# =================

# printing
  sp := proc() b:-append(" ") end;
  lbrack := proc() b:-append("[") end;
  rbrack := proc() b:-append("]") end;
  lparen := proc() b:-append("(") end;
  rparen := proc() b:-append(")") end;
  parens := proc(c) b:-append("("); c(); b:-append(")") end;
  ufunc := proc(f) proc(c) parens(proc() b:-append(f); sp(); p(c) end) end; end;
  bfunc := f -> ((x,y) -> parens(proc() b:-append(f); sp(); p(x); sp(); p(y); end));
  seqp := proc(s, l) 
    if nops(l)=0 then error "empty sequence passed where non-empty expected";
    elif nops(l)=1 then p(l[1]) 
    else
      p(l[1]);
      b:-append(s);
      seqp(s, l[2..-1]);
    end if;
  end proc;

# resolve name
  resolve := proc(inrt)
    local s, nm;
    nm := eval(inrt, _Inert_ATTRIBUTE=NULL); # crude but effective
    if typematch(nm, specfunc('s'::'string', '_Inert_NAME')) then
      s
    elif type(nm, specfunc('string', '_Inert_ASSIGNEDNAME')) then
      op(1,nm)
    else
      error "cannot resolve an %1, namely %2", op(0,nm), nm;
    end if;
  end proc;
end module:
