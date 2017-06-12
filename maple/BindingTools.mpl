#############################################################################

# make gensym global, so that it can be shared with other 'global' routines
gensym := module ()
  export ModuleApply, SymbolsToGen;
  local gs_counter, utf8, blocks, radix, unicode, bad_name, do_gensym, ModuleLoad;
  gs_counter := -1;
  utf8 := proc(n :: integer, $)
    local m;
    if n<128 then n
    elif n<2048 then 192+iquo(n,64,'m'), 128+m
    elif n<65536 then 224+iquo(n,4096,'m'), 128+iquo(m,64,'m'), 128+m
    elif n<2097152 then 240+iquo(n,262144,'m'), 128+iquo(m,4096,'m'), 128+iquo(m,64,'m'), 128+m
    elif n<67108864 then 248+iquo(n,16777216,'m'), 128+iquo(m,262144,'m'), 128+iquo(m,4096,'m'), 128+iquo(m,64,'m'), 128+m
    elif n<2147483648 then 248+iquo(n,1073741824,'m'), 128+iquo(m,16777216,'m'), 128+iquo(m,262144,'m'), 128+iquo(m,4096,'m'), 128+iquo(m,64,'m'), 128+m
    end if
  end proc;
  SymbolsToGen :=
             [ ["`", "_"]
             , ["0", "9"]
             , ["a", "z"]
             , ["A", "Z"] ];
             # e.g.
             # [[ 19968, 20950 ]] for unicode

  bad_name := n -> type(n, protected) or (x -> assigned(x))(n);
  blocks := proc($)
    map(((l,u)->`[]`(StringTools:-Ord(l), StringTools:-Ord(u) - StringTools:-Ord(l)+1))@op,SymbolsToGen)
  end proc;
  radix := proc($) `+`(op(map2(op, 2, blocks()))) / 2; end proc;
  unicode := proc(nn, $)
    local n, b;
    n := nn;
    for b in blocks() do
      if n < op(2,b) then return n + op(1,b) else n := n - op(2,b) end if
    end do
  end proc;
  ModuleApply := proc(x::name, $)
    local x1 := do_gensym(x);
    if bad_name(x1) then ModuleApply(x) else x1 end if;
  end proc;
  do_gensym := proc(x::name, $)
    gs_counter := gs_counter + 1;
    cat(x, op(map(StringTools:-Char, map(utf8 @ unicode, applyop(`+`, 1, map(`*`, convert(gs_counter, 'base', radix()), 2), 1)))))
  end proc;
  ModuleLoad := proc()
    unprotect(SymbolsToGen);
  end proc;
  ModuleLoad();
end module: # gensym

#############################################################################

BindingTools := module ()
  option package;
  export generic_evalat, generic_evalatstar, load_types_from_table;

  load_types_from_table := proc(types, unload::truefalse:=true, $)
    local ty_nm;
    if unload then
      for ty_nm in [ indices(types, nolist) ] do
        if TypeTools[Exists](ty_nm) then TypeTools[RemoveType](ty_nm) end if;
      end do;
    end if;

    for ty_nm in [ indices(types, nolist) ] do
      TypeTools[AddType]( ty_nm, types[ty_nm] );
    end do;
  end proc;

  generic_evalat := proc(vv::{name,list(name)}, mm, eqs, $)
    local v, m, eqsRemain, eq, rename, funs;
    funs := map2(op, 0, indets(mm, 'function'));
    eqsRemain := select(
      (eq -> op(1,eq) <> op(2,eq)
             and not has(op(1,eq), vv)
             and (not (op(1,eq) :: 'name')
                  or depends(mm, op(1,eq))
                  or member(op(1,eq), funs))),
      eqs);
    if nops(eqsRemain) = 0 then return vv, mm end if;
    m := mm;
    rename := proc(v::name, $)
      local vRename;
      if depends(eqsRemain, v) then
        vRename := gensym(v);
        m := subs(v=vRename, m);
        vRename
      else
        v
      end if
    end proc;
    if vv :: name then
      v := rename(vv)
    else
      v := map(rename, vv);
    end if;
    v, eval(m, eqsRemain);
  end proc:

  generic_evalatstar := proc(body, bound::list, eqs, $)
    local indefinite, e, n, b, j;
    e := foldl(((x,i) -> `if`(i::`=`,
                              lam(lhs(i), rhs(i), x),
                              lam(i, indefinite, x))),
               body, op(bound));
    e := eval(e, eqs); # Piggyback on `eval/lam`
    n := nops(bound);
    b := table();
    for j from n to 1 by -1 do
      b[j] := `if`(op(2,e)=indefinite, op(1,e), `=`(op(1..2,e)));
      e := op(3,e);
    end do;
    e, [entries(b, 'nolist', 'indexorder')]
  end proc:
end module: # BindingTools
