# This module forms part of NewSLO and is `$include`d there

RoundTrip := proc(e, t::t_type)
  local result;
  interface(screenwidth=infinity, prettyprint=0, warnlevel=0,
    showassumed=0,quiet=true);
  kernelopts(assertlevel=0);
  result := eval(ToInert(Simplify(_passed)), _Inert_ATTRIBUTE=NULL);
  lprint(result)
end proc;

Simplify := proc(e, t::t_type, {ctx :: list := []}, $)
  subsindets(SimplifyKB(e, t, build_kb(ctx, "Simplify")),
             And({t_sum, t_product}, anyfunc(anything, anything=range)),
             e -> subsop(0 = `if`(e::t_sum, SumIE, ProductIE),
                         applyop(`+`, [2,2,2], e, 1)))
end proc;

SimplifyKB := proc(e, t::t_type, kb::t_kb, $)
  local patterns, x, kb1, ex;
  if t :: HMeasure(anything) then
    fromLO(improve(toLO(e), _ctx=kb), _ctx=kb)
  elif t :: HFunction(anything, anything) then
    patterns := htype_patterns(op(1,t));
    if patterns :: Branches(Branch(PVar(name),anything)) then
      # Eta-expand the function type
      x := `if`(e::lam(name,anything,anything), op(1,e),
                op([1,1,1],patterns));
      x, kb1 := genType(x, op(1,t), kb, e);
      ex := app(e,x);
      lam(x, op(1,t), SimplifyKB(ex, op(2,t), kb1))
    else
      # Eta-expand the function type and the sum-of-product argument-type
      x := `if`(e::lam(name,anything,anything), op(1,e), d);
      if depends([e,t,kb], x) then x := gensym(x) end if;
      ex := app(e,x);
      lam(x, op(1,t), 'case'(x,
        map(proc(branch)
            local eSubst, pSubst, p1, binds, y, kb1, i, pSubst1;
              eSubst, pSubst := pattern_match([x,e], x, op(1,branch));
              p1 := subs(pSubst, op(1,branch));
              binds := [pattern_binds(p1)];
              kb1 := kb;
              pSubst1 := table();
              for i from 1 to nops(binds) do
                y, kb1 := genType(op(i,binds), op([2,i],branch), kb1);
                pSubst1[op(i,binds)] := y;
              end do;
              pSubst1 := op(op(pSubst1));
              Branch(subs(pSubst1, p1),
                     SimplifyKB(eval(eval(ex,eSubst),pSubst1), op(2,t), kb1))
            end proc,
            patterns)))
    end if
  else
    simplify_assuming(e, kb)
  end if
end proc;

# Testing

TestSimplify := proc(m, t, n::algebraic:=m, {verify:=simplify})
  local s, r;
  # How to pass keyword argument {ctx::list:=[]} on to Simplify?
  s, r := selectremove(type, [_rest], 'identical(ctx)=anything');
  CodeTools[Test](Simplify(m,t,op(s)), n, measure(verify), op(r))
end proc;

TestHakaru := proc(m, n::{set(algebraic),algebraic}:=m,
                   {simp:=improve, verify:=simplify, ctx::list:=[]})
  local kb := build_kb(ctx, "TestHakaru");
  CodeTools[Test](fromLO(simp(toLO(m), _ctx=kb), _ctx=kb), n,
    measure(verify), _rest)
end proc;

  # Test roughly for "efficient" Hakaru measure terms,
  # i.e., those we want simplification to produce.
Efficient := proc(mm, $)
  local m, n;
  m := mm;
  if has(m, 'undefined') then
    return false;
  end if;
  while m :: '{lam(name, anything, anything),
               Context(anything, anything),
               And(specfunc(piecewise), anyfunc(anything, anything, Msum()))}' do
    m := op(`if`(op(0,m)='lam',3,2),m);
  end do;
  if m :: 'Weight(anything, anything)' then m := op(2,m) end if;
  if has(m, '{infinity, Lebesgue, int, Int, Beta, GAMMA}') then
    return false;
  end if;
  for n in `if`(m :: 'specfunc(Msum)', m, [m]) do
    if n :: 'Weight(anything, anything)' then n := op(2,n) end if;
    if has(subsindets(n, 'specfunc(Weight(anything, anything), Msum)',
                      s -> `if`(Testzero(`+`(op(map2(op, 1, s))) - 1),
                                map2(op, 2, s), s)),
           '{Msum, Weight}') then
      return false;
    end if;
  end do;
  return true;
end proc;
