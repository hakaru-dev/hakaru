# This module forms part of NewSLO and is `$include`d there

Commands := [ `Simplify`, `Disintegrate`, `Summarize` ];

RoundTrip := proc(e, t::t_type, {_ret_type := {'print', [ 'convert', 'Partition', 'piecewise'] }
                                ,_gensym_charset := FAIL
                                ,_command := Simplify})
  local result, ret_type, cs, ifc_opts, syms0, command;
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
    kernelopts(assertlevel=0);
    result := _command(e,t,_rest);
    for cs in select(type, ret_type, [ identical(convert), type, anything ]) do
      result := subsindets(result, op(2,cs), x->convert(x,op(3,cs)));
    end do;
    result := eval(ToInert(result), _Inert_ATTRIBUTE=NULL);
    if ({'print','string'} intersect ret_type) <> {} then
      result := sprintf("%a",result);
    end if;
    if 'print' in ret_type then
      printf("%s\n",result);
      result := NULL;
    end if;
  finally
    interface(zip(`=`, map(lhs,[ifc_opts[0]]), [ifc_opts[1]])[]);
    gensym:-SymbolsToGen := syms0;
  end try;
  return result;
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
  local ns;
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
    ev(map(x->eval_in_ctx(ev,x,kb),e),kb);
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
  local out, result;
  out := SimplifyKB(args[1..3]);

  _Env_TestTools_Try_printf := false;
  result := TestTools[Try](label, Efficient(out),true);
  if result = NULL then
    printf("%s passed.\n", label);
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

Profile := module()
  option package;
  export ModuleApply, GetProf, PPrProf, modules_to_profile, names_to_profile;
  local ModuleLoad, cl, profile_flag_to_ord, name_to_string, take;

  modules_to_profile := proc()
    kernelopts(opaquemodules=false):
    { 'BindingTools', 'Hakaru', 'KB', 'Partition', 'Partition:-Simpl', 'Loop'
    , 'Domain', 'NewSLO', 'Summary'
    , entries(Domain:-Improve:-Simplifiers, nolist)
    };
  end proc();

  cl := proc(f,x,$)
    local rs := f(x) minus x;
    if rs={} then x else cl(f,rs) end if;
  end proc;

  take := proc(xs,n,$)
    op(1,[ListTools[LengthSplit](xs,n)]);
  end proc;

  names_to_profile := proc()
    option remember, system;
    local ns;
    kernelopts(opaquemodules=false):
    ns := cl(curry(map,x->CodeTools:-Profiling:-getMemberFuncs(x,true)), modules_to_profile);
    map(proc(n)
          if n::`module`('ModuleApply') then 'n[ModuleApply]' elif n::procedure then n else NULL end if
        end proc, ns);
  end proc;

  name_to_string := (x->convert(x,'string'));

  profile_flag_to_ord := table(
     ['alpha' = (proc (a, b) lexorder(a[1],b[1]) end proc)
     ,'ralpha' = (proc (a, b) not lexorder(a[1],b[1]) end proc)
     ,'time' = (proc (a, b) evalb(a[4] < b[4]) end proc)
     ,'rtime' = (proc (a, b) evalb(b[4] < a[4]) end proc)
     ,'bytes' = (proc (a, b) evalb(a[6] < b[6]) end proc)
     ,'rbytes' = (proc (a, b) evalb(b[6] < a[6]) end proc)
     ,'load' = (proc (a, b) evalb(a[6]*a[6]*a[4] < b[6]*b[6]*b[4]) end proc)
     ,'rload' = (proc (a, b) evalb(b[6]*b[6]*b[4] < a[6]*a[6]*a[4]) end proc)
     ]);

  GetProf := proc(fns::({list,set})(satisfies(x->member(x,:-profile_profiled)))
                 ,{_flag:='rload'}
                 )
    local i, totaltime, totalbytes, totaldepth, totalcalls, timepc, bytespc, numargs, displist, totaltimepc, totalbytespc
         , ix, get_timepc, get_bytespc, get_nm, nm, flag ;
    global profile_time, profile_bytes, profile_maxdepth, profile_calls, profile_profiled;

    flag := _flag;
    totaltime, totalbytes, totalcalls, totaldepth := 0$4;
    numargs := nops(fns);

    for i to nops(profile_profiled) do
      ix := name_to_string(profile_profiled[i]);
      totaltime := totaltime+profile_time[ix];
      totalbytes := totalbytes+profile_bytes[ix];
      totalcalls := totalcalls+profile_calls[ix];
      totaldepth := totaldepth+profile_maxdepth[ix];
    end do;

    if totaltime = 0 then
      get_timepc := i->0;
      totaltimepc := 0;
    else
      get_timepc := i->100*profile_time[name_to_string(profile_profiled[i])]/totaltime;
      totaltimepc := 100;
    end if;
    for i to nops(profile_profiled) do
      timepc[name_to_string(profile_profiled[i])] := get_timepc(i);
    end do;

    if totalbytes = 0 then
      get_bytespc := i->0;
      totalbytespc := 0;
    else
      get_bytespc := i->100*profile_bytes[name_to_string(profile_profiled[i])]/totalbytes;
      totalbytespc := 100;
    end if;
    for i to nops(profile_profiled) do
      bytespc[name_to_string(profile_profiled[i])] := get_bytespc(i);
    end do;

    displist := [];
    if 0 < numargs then
      get_nm := i->op(i,fns);
    else
      numargs := nops(profile_profiled);
      get_nm := i->profile_profiled[i];
    end if;
    for i to numargs do
      nm := get_nm(i); ix := name_to_string(nm);
      displist := [op(displist),
                   [nm, map(q->q[ix],[profile_maxdepth, profile_calls,
                                      profile_time, timepc, profile_bytes, bytespc])[]  ]];
    end do;

    displist := sort(displist, profile_flag_to_ord[flag]);
    displist, [totaldepth,totalcalls,totaltime,totaltimepc,totalbytes,totalbytespc];
  end proc;

  PPrProf := proc(dat,tot,{_max_name_len:=55,_prof_name:=`function`})
    local i, k, pr_nm;
    k := _max_name_len; pr_nm := _prof_name;

    printf(cat(pr_nm,(" "$k-StringTools[Length](convert(pr_nm,string))),
               `depth    calls     time    time%%     `));
    printf(`    bytes   bytes%%\n`);
    printf(cat("--"$k+1,`\n`));
    for i from 1 to nops(dat) do
      printf(cat(`%-`,convert(k,string),`a%7d%9d%9.3f%9.2f%14d%9.2f\n`),
             op(1..7,dat[i]));
    end do;
    printf(cat("--"$k+1,`\n`));
    printf(cat(`%-`,convert(k,string),`a%7d%9d%9.3f%9.2f%14d%9.2f\n\n`),
           `total:`,op(1..6,tot));
    return NULL
  end proc;

  ModuleApply := proc(f,{_args:=[]})
    local names_prof, res, nppr, rm_ppr, prf, tot, as; as := _args;
    if assigned(_Env_Profile_count_ppr) then
      nppr := _Env_Profile_count_ppr;
    else nppr := 25; end if;
    if assigned(_Env_Profile_remove_ppr) then
      rm_ppr := _Env_Profile_remove_ppr;
    else rm_ppr := (x->andmap(q->op(q,x)<0.001,[3,4,6])); end if;

    unprofile();
    names_prof := names_to_profile();
    profile(op(names_prof));
    if   f::string then res := NULL; read(f);
    else                res := f(op(as)); end if;
    prf, tot := GetProf(names_prof,_rest);
    unprofile();
    prf := remove(rm_ppr, prf);
    PPrProf(take(prf,nppr),tot,_rest);
    res;
  end proc;

  ModuleLoad := proc($)
    unprotect(:-convert);
    :-convert := overload([proc(x::name,_::identical(string),$) option overload(callseq_only); sprintf("%a",x) end proc
                          ,:-convert]);
    protect(:-convert);
    map(unprotect,[modules_to_profile]);
    NULL;
  end proc;
  ModuleLoad();
end module;


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
