# This module forms part of NewSLO and is `$include`d there

RoundTrip := proc(e, t::t_type)
  local result;
  interface(screenwidth=9999, prettyprint=0, warnlevel=0,
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

SimplifyKB_ := proc(e, t::t_type, kb::t_kb, $)
  local patterns, x, kb1, ex;
  if t :: HMeasure(anything) then
    %fromLO(%improve(%toLO(e), _ctx=kb), _ctx=kb);
  elif t :: HFunction(anything, anything) then
    patterns := htype_patterns(op(1,t));
    if patterns :: Branches(Branch(PVar(name),anything)) then
      # Eta-expand the function type
      x := `if`(e::lam(name,anything,anything), op(1,e),
                op([1,1,1],patterns));
      x, kb1 := genType(x, op(1,t), kb, e);
      ex := app(e,x);
      lam(x, op(1,t), SimplifyKB_(ex, op(2,t), kb1))
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
                     SimplifyKB_(eval(eval(ex,eSubst),pSubst1), op(2,t), kb1))
            end proc,
            patterns)))
    end if
  else
    %simplify_assuming(e, kb)
  end if
end proc;

SimplifyKB := proc(e, t::t_type, kb::t_kb, $)
    eval(SimplifyKB_(eval_for_Simplify(e,kb), t, kb),
     [%fromLO=fromLO,%improve=improve,%toLO=toLO,%simplify_assuming=simplify_assuming]);
end proc;

eval_for_Simplify_tbl := table(
  [ `Int`=`int`
  , `Sum`=`sum`
  , `Product`=`product`
  ]);

eval_for_Simplify := proc(e,kb,$)
  eval_in_ctx(
    proc(x,kb1)
      subsindets(x, {seq(specfunc(q),q=[indices(eval_for_Simplify_tbl, nolist)])},
                 y -> KB:-kb_eval_mb(eval_for_Simplify_tbl[op(0,y)],y,kb1));
    end proc, e, kb);
end proc;

eval_in_ctx_tbl := table(
  [ `PARTITION` = ((e,kb,ev)->KB:-kb_Partition(e,kb,a->a,ev))
  , `piecewise` = ((e,kb,ev)->KB:-kb_piecewise(e,kb,a->a,ev))
  ]);

eval_in_ctx := proc(ev, e, kb, $)
  if assigned(eval_in_ctx_tbl[op(0,e)]) then
    eval_in_ctx_tbl[op(0,e)](e,kb,curry(eval_in_ctx, ev));
  elif has(e, {indices(eval_in_ctx_tbl,nolist)}) then
    map(x->eval_in_ctx(ev,x,kb),e);
  else
    ev(e,kb);
  end if;
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
  local kb := build_kb(ctx, "TestHakaru"), ver := measure(verify);
  ver := `if`(n::set, 'member'(ver), ver);

  CodeTools[Test](fromLO(simp(toLO(m), _ctx=kb), _ctx=kb), n,
    ver, _rest)
end proc;

TestDisint := module()
    export ModuleApply := proc(
      M::{t_Hakaru, list(anything)}, #args to disint, or just 1st arg
      n::set({t_Hakaru, identical(NULL)}), #desired return
      ctx::t_kb_atoms:= [], #context: assumptions, "knowledge"
      TLim::{positive, identical(-1)}:= 80 #timelimit
    )
      local disint_args, disint_var, expected := n;
      if M :: list then
        disint_args := [op(M),ctx];
      else
        disint_var := gensym('t');
        disint_args := [M,disint_var,ctx];
        expected := subs(:-`t`=disint_var,expected);
      end if;
      try
        do_test(disint_args, copy(expected), TLim, _rest);
      catch "time expired":
        error "Time expired while running: disint(%1)", disint_args;
      end try;
    end proc;

    # This is necessary because CodeTools seems to forgot the value
    # of our local variables (but only the `expected result' arg)
    # unless that arg is precisely a formal parameter, and we `copy' the
    # input to this function.
    local do_test := proc(disint_args, expected, tlim)
      timelimit( tlim, CodeTools[Test]
                 ( {disint(op(disint_args))}
                 , expected
                 , '`subset`(measure(simplify))'
                 , _rest));
    end proc;
end module;

TestEfficient := proc(e, t::t_type, t_kb := KB:-empty, {label::string := "Test" })
  local done_, result, todo;
  todo := SimplifyKB_(args[1..3]);
  done_ := eval(todo, [%fromLO=fromLO,%improve=improve,%toLO=toLO,%simplify_assuming=simplify_assuming]);

  _Env_TestTools_Try_printf := false;
  result := TestTools[Try](label, Efficient(done_),true);
  if result = NULL then
    printf("%s passed.\n", label);
  else
    error sprintf("%s FAILED.\n"
                  "The result of\n\t%a\n\tis not efficient.\n"
                 , label, todo );
  end if;
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
               case(anything, Branches(Branch(anything, anything))),
               And(specfunc(piecewise)
                  ,{anyfunc(anything, anything, Msum())
                   ,anyfunc(anything, anything, anything, Msum())})}' do
    m := op(`if`(op(0,m)='lam',3,`if`(op(0,m)='case',[2,1,2],2)),m);
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

# Load a file in concrete Hakaru syntax (using the "momiji" command)
# and return its term (in which Sum and Product are inert) and type.
Concrete := proc(path::string, $)
  local cmd, res, dangerous_chars;
  cmd := FileTools:-AbsolutePath(path,
    (FileTools:-ParentDirectory@@2)(LibraryTools:-FindLibrary(Hakaru)));
  dangerous_chars := [ " ", "'", """", `if`(kernelopts(platform)="windows", [], ["\\"])[] ];
  if ormap((c->StringTools:-Has(cmd,c)), dangerous_chars) then
    error "Dangerous characters in path: %1", cmd;
  end if;
  cmd := cat("momiji ", cmd);
  res := ssystem(cmd);
  if res :: [0, string] then
    parse(cat("use Hakaru in ", op(2,res), " end use"));
  else
    error "ssystem %1: %2", cmd, res;
  end if;
end proc;
