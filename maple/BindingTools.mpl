#############################################################################

# make gensym global, so that it can be shared with other 'global' routines
gensym := module ()
  export ModuleApply;
  local gs_counter, utf8, blocks, radix, unicode;
  gs_counter := -1;
  utf8 := proc(n :: integer)
    local m;
    if n<128 then n
    elif n<2048 then 192+iquo(n,64,'m'), 128+m
    elif n<65536 then 224+iquo(n,4096,'m'), 128+iquo(m,64,'m'), 128+m
    elif n<2097152 then 240+iquo(n,262144,'m'), 128+iquo(m,4096,'m'), 128+iquo(m,64,'m'), 128+m
    elif n<67108864 then 248+iquo(n,16777216,'m'), 128+iquo(m,262144,'m'), 128+iquo(m,4096,'m'), 128+iquo(m,64,'m'), 128+m
    elif n<2147483648 then 248+iquo(n,1073741824,'m'), 128+iquo(m,16777216,'m'), 128+iquo(m,262144,'m'), 128+iquo(m,4096,'m'), 128+iquo(m,64,'m'), 128+m
    end if
  end proc;
  blocks := map((b -> block(convert(op(0,b), decimal, hex), op(1,b))),
                ["4e00"(20950)]);
  radix := `+`(op(map2(op, 2, blocks))) / 2;
  unicode := proc(nn)
    local n, b;
    n := nn;
    for b in blocks do
      if n < op(2,b) then return n + op(1,b) else n := n - op(2,b) end if
    end do
  end proc;
  ModuleApply := proc(x::name)
    gs_counter := gs_counter + 1;
    cat(x, op(map(StringTools:-Char, map(utf8 @ unicode, applyop(`+`, 1, map(`*`, convert(gs_counter, 'base', radix), 2), 1)))))
  end proc;
end module: # gensym

#############################################################################

BindingTools := module ()
  option package;
  export generic_evalat, generic_evalatstar;

  generic_evalat := proc(vv::{name,list(name)}, mm, eqs)
    local v, m, eqsRemain, subsEq, eq, rename, funs;
    funs := map2(op, 0, indets(mm, 'function'));
    eqsRemain := remove((eq -> op(1,eq) = op(2,eq)), eqs);
    eqsRemain, subsEq := selectremove((eq -> type(op(1,eq),'name')), eqsRemain);
    eqsRemain := select((eq -> not has(op(1,eq), vv) and
      (depends(mm, op(1,eq)) or member(op(1,eq), funs))), eqsRemain);
    m := mm;
    rename := proc(v::name)
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
    m := subs(subsEq,m);
    if nops(eqsRemain) > 0 then
      m := eval(m,eqsRemain);
    end if;
    v, m;
  end proc:

  generic_evalatstar := proc(body, bound::list, eqs)
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
