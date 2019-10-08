# This module forms part of NewSLO and is `$include`d there

Commands := [ `Simplify`, `Disintegrate`, `Summarize`, `Reparam` ];

RoundTrip := proc(e, t::t_type, {_ret_type := {'print'}
                                ,_postproc := [['convert','Partition','piecewise'],
                                               'stable_Partition_order']
                                ,_gensym_charset := FAIL
                                ,_debug :: truefalse := false
                                ,_command := Simplify})
  local result, ret_type, cs, ifc_opts, syms0, command, pp;
  ret_type := _ret_type; command := _command;
  if not(ret_type::set) then ret_type := {ret_type}; end if;
  if command::string then command := convert(command, name); end if;
  if not (command in Commands) then
    error "unrecognized command: %1", command;
  end if;
  if _gensym_charset <> FAIL then
    syms0 := copy(gensym:-SymbolsToGen);
    gensym:-SymbolsToGen := _gensym_charset;
  else
    syms0 := gensym:-SymbolsToGen;
  end if;

  ifc_opts[0] :=
     screenwidth=9999,
     `if`('print' in ret_type, prettyprint=0, NULL),
     warnlevel=0,
     showassumed=0,
     quiet=true;

  ifc_opts[1] := interface(ifc_opts[0]);
  try
    if not(_debug) then kernelopts(assertlevel=0); end if;
    result := _command(e,t,_rest);
    for pp in _postproc do
      if assigned(RoundTrip_postproc[op(1,pp)]) then
        result := RoundTrip_postproc[op(1,pp)](result, op(2..-1,pp))
      else
        error "invalid postproc option: %1", pp;
      end if;
    end do;
    if not ('expr' in ret_type) then
      result := eval(ToInert(result), _Inert_ATTRIBUTE=NULL);
      if ({'print','string'} intersect ret_type) <> {} then
        result := sprintf("%a",result);
      end if;
      if 'print' in ret_type then
        printf("%s\n",result);
        result := NULL;
      end if;
    end if;
  finally
    interface(zip(`=`, map(lhs,[ifc_opts[0]]), [ifc_opts[1]])[]);
    gensym:-SymbolsToGen := syms0;
  end try;
  return result;
end proc;

RoundTrip_postproc[convert] := proc(r, f::type, t, $)
  subsindets(r, f, x->convert(x,t));
end proc;
RoundTrip_postproc[stable_Partition_order] := proc(r, $)
  subsindets(r, Partition, Simpl:-stable_order)
end proc;

Reparam := proc(e, t::t_type, {ctx :: list := []})
  SimplifyKB_(
    ((e1,_,kb1)->
     fromLO(ReparamDetermined(toLO(e1),kb1),_ctx=kb1)),
    e,t,build_kb(ctx,"Reparam",KB:-empty))
end proc;

Summarize := proc(e, _) Summary:-Summarize(e,_rest) end proc;

Simplify := proc(e, t::t_type, {ctx :: list := []})
  local res;
  res := subsindets(SimplifyKB(e, t, build_kb(ctx, "Simplify")),
             And({t_sum, t_product}, anyfunc(anything, anything=range)),
             e -> subsop(0 = `if`(e::t_sum, SumIE, ProductIE),
                         applyop(`+`, [2,2,2], e, 1)));
  Rename(res,_rest);
end proc;

Rename := proc(e, {_do_rename :: truefalse := false})
  local ns, i;
  if _do_rename then
    ns := [op(bound_names_in(res))];
    subs(zip(`=`,ns,
             [seq(cat(`x`,convert(i,string)),i=1..nops(ns))]),
         e);
  else e
  end if;
end proc;

Disintegrate := proc(e::t_Hakaru,t::t_type, {ctx::list := []})
  local res;
  res := SimplifyKB_((e,t,kb)->disint(e,disint:-htype_to_disint_wrt(t),kb,'do_lam',_rest),
                     e, t, build_kb(ctx,"Disintegrate",KB:-empty));
  Rename(res,_rest);
end proc;

SimplifyKB_ := proc(leaf, e, t::t_type, kb::t_kb, $)
  local patterns, x, kb1, ex;
  if t :: HFunction(anything, anything) then
    patterns := htype_patterns(op(1,t));
    if patterns :: Branches(Branch(PVar(name),anything)) then
      # Eta-expand the function type
      x := `if`(e::lam(name,anything,anything), op(1,e),
                op([1,1,1],patterns));
      x, kb1 := genType(x, op(1,t), kb, e);
      ex := app(e,x);
      lam(x, op(1,t), SimplifyKB_(leaf,ex, op(2,t), kb1))
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
                     SimplifyKB_(leaf,eval(eval(ex,eSubst),pSubst1), op(2,t), kb1))
            end proc,
            patterns)))
    end if
  else
    leaf(e,t,kb)
  end if
end proc;

SimplifyKB := proc(e,t,kb,$)
  local res;
  res[0] := SimplifyKB_(
  proc(e0,t,kb)
    local e := eval_for_Simplify(e0,kb);
    if t :: HMeasure(anything) then
      fromLO(improve(toLO(e), _ctx=kb), _ctx=kb);
    else
      simplify_assuming(e,kb);
    end if;
  end proc, e, t, kb);

  res[1] := eval(res[0]);
  if res[1] <> res[0] then
    KB:-simplify_assuming(res[1], kb);
  else
    res[0]
  end if;
end proc;

eval_for_Simplify_tbl := table(
  [ `Int`=`int`
  # Some parts (which?) of the simplifier still always need `sum` instead of `Sum`
  , `Sum`=[`sum`,Not(anything)]
  # Some parts (e.g. gmm_gibbs, see #103) of the simplifier still need `product`
  , `Product`=[`product`,Not(satisfies(x->has(x,{Hakaru:-idx,Hakaru:-size})))]
  ]);

eval_for_Simplify := proc(e,kb,$)
  eval_in_ctx(
    proc(x,kb1) local q;
      subsindets(x, {seq(specfunc(q),q=[indices(eval_for_Simplify_tbl, nolist)])},
                 y -> KB:-kb_eval_mb(eval_for_Simplify_tbl[op(0,y)],y,kb1));
    end proc, e, kb);
end proc;

eval_in_ctx_tbl := table(
  [ `PARTITION` = ((e,kb,ev)->KB:-kb_Partition(e,kb,a->a,ev))
  , `piecewise` = ((e,kb,ev)->KB:-kb_piecewise(e,kb,a->a,ev,'no_split_disj'))
  ]);

eval_in_ctx := proc(ev, e, kb, $)
  if assigned(eval_in_ctx_tbl[op(0,e)]) then
    eval_in_ctx_tbl[op(0,e)](e,kb,curry(eval_in_ctx, ev));
  elif has(e, {indices(eval_in_ctx_tbl,nolist)}) then
    ev(map(x->eval_in_ctx(ev,x,kb),e),kb);
  else
    ev(e,kb);
  end if;
end proc;

PrintVersion := proc($)
  local i,v,s;
  s := max(op(map(length@lhs,Hakaru:-Version)));
  for i in map(lhs,Hakaru:-Version) do
    v := table(Hakaru:-Version)[i];
    printf(cat("%-",s,"s : %s\n"), i, `if`(v::string,v,""));
  end do;
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
  local out, result;
  out := SimplifyKB(args[1..3]);

  _Env_TestTools_Try_printf := false;
  result := TestTools[Try](label, Efficient(out),true);
  if result = NULL then
    printf("%s passed\n", label);
  else
    error sprintf("%s FAILED.\n"
                  "The result of\n\tSimplifyKB(%a,%a,%a)\n\tis not efficient.\n"
                 , label, args[1..3] );
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
                   ,anyfunc(anything, Msum(), anything)
                   ,anyfunc(anything, anything, anything, Msum())
                   ,anyfunc(anything, Msum(), anything, anything)})}' do
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
