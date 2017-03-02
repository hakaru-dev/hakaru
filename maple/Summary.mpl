`depends/Bucket` := proc(mr, r::(name=range), x, $)
  depends(rhs(r), x) or depends(mr, x minus {lhs(r)})
end proc:

`depends/Index` := proc(n, o::name, e, mr, x, $)
  depends({n,e}, x) or depends(mr, x minus {o})
end proc:

`eval/Bucket` := proc(e::anyfunc(anything,name=range), eqs, $)
  local bvar, body;
  bvar, body := BindingTools:-generic_evalat(op([2,1],e), op(1,e), eqs);
  eval(op(0,e), eqs)(body, bvar = eval(op([2,2],e), eqs))
end proc:

`eval/Index` := proc(e::anyfunc(anything,name,anything,anything), eqs, $)
  local o, mr;
  o, mr := BindingTools:-generic_evalat(op(2,e), op(4,e), eqs);
  eval(op(0,e), eqs)(eval(op(1,e), eqs), o, eval(op(3,e), eqs), mr)
end proc:

Summary := module ()
  option package;
  export bucket, summarize, summarize_throughout;
  global Bucket, Fanout, Index, Split, Nop, Add;
  uses Hakaru, KB;

  bucket := proc(mr, r::(name=range), cond::list:=[], $)
    if mr :: 'Fanout(anything,anything)' then
      Pair(op(map(procname, _passed)))
    elif mr :: 'Split(anything,anything,anything)' then
      Pair(bucket(op(2,mr), r, [    op(1,mr) ,op(cond)]),
           bucket(op(3,mr), r, [Not(op(1,mr)),op(cond)]))
    elif mr :: 'Index(anything,name,anything,anything)' then
      ary(op(1,mr), op(2,mr),
          bucket(op(4,mr), r, [op(2,mr)=op(3,mr),op(cond)]));
    elif mr :: 'Nop()' then
      _Unit
    elif mr :: 'Add(anything)' then
      sum(piecewise_And(cond, op(1,mr), 0), r)
    else
      'procname(_passed)'
    end if;
  end proc;

  summarize := proc(ee,
                    kb :: t_kb,
                    i :: {name,list(name),set(name)},
                    summary, $)
    local e, r, s,
          e1, mr1, f1, e2, mr2, f2,
          variables, var_outerness, outermost, thunk, consider,
          o, t, lo, hi, b, a;

    # Try to ensure termination
    e := simplify_assuming(ee, kb);
    if length(e) >= length(ee) then e := ee end if;

    # Nop rule
    if Testzero(e) then return Nop(), 0 end if;

    r := indets(e, '{relation, logical, specfunc({And,Or})}');
    s, r := selectremove(depends, r, i);
    # Fanout rule
    r := sort(convert(r, 'list'), 'length');
    while nops(r) > 0 do
      e1 := eval(e, r[-1]=true);  if e = e1 then r := r[1..-2]; next end if;
      e2 := eval(e, r[-1]=false); if e = e2 then r := r[1..-2]; next end if;
      mr1, f1 := summarize(e1, kb, i, 'fst(summary)');
      mr2, f2 := summarize(e2, kb, i, 'snd(summary)');
      return Fanout(mr1, mr2), 'piecewise'(r[-1], f1, f2);
    end do;

    variables     := kb_to_variables(kb);
    var_outerness := table(variables =~ [seq(1..nops(variables))]);
    outermost     := -infinity;
    consider      := proc(expr, th, $)
      local outerness;
      outerness := map((n -> var_outerness[n]), indets(expr, 'name'));
      outerness := min(select(type, outerness, 'integer'));
      if outermost < outerness then
        outermost := outerness;
        thunk     := th;
      end if;
    end proc;
    if has(variables, i) then
      error "The loop to be summarized shadows the variable %1", i;
    end if;
    for r in s do
      e1 := eval(e, r=true);  if e = e1 then next end if;
      e2 := eval(e, r=false); if e = e2 then next end if;
      # Index rule
      if r :: `=` and Testzero(e2) then
        for o in indets(r, 'name') minus convert(i, 'set') do
          if not (var_outerness[o] :: integer) then next end if;
          t := getType(kb, o);
          if not (t :: specfunc(HInt)) then next end if;
          lo := op(select(type, t, 'Bound(identical(`>=`), anything)'));
          if lo = NULL then next else lo := op(2,lo) end if;
          hi := op(select(type, t, 'Bound(identical(`<=`), anything)'));
          if hi = NULL then next else hi := op(2,hi) end if;
          if not ispoly(`-`(op(r)), 'linear', o, 'b', 'a') then next end if;
          b := Normalizer(-b/a);
          consider(b, ((e1, o, lo, hi, b) -> proc($)
            local mr, f;
            mr, f := summarize(e1, kb, i, 'idx'(summary, o-lo));
            Index(hi-lo+1, o, b, mr),
              'piecewise'(And(o::integer, lo<=o, o<=hi), f, 0);
          end proc)(e1, o, lo, hi, b));
        end do;
      end if;
      # Split rule
      consider(r, ((e1, e2, r) -> proc($)
        local mr1, f1, mr2, f2;
        mr1, f1 := summarize(e1, kb, i, 'fst(summary)');
        mr2, f2 := summarize(e2, kb, i, 'snd(summary)');
        Split(r, mr1, mr2), f1 + f2;
      end proc)(e1, e2, r));
    end do;
    if thunk :: procedure then
      return thunk();
    else
      # Add rule
      return Add(e), summary;
    end if;
  end proc;

  summarize_throughout := proc(e, kb :: t_kb, $)
    local x, kb1, e1, rng, summary, mr, f;
    if not hasfun(e, '{Sum,sum}', 'piecewise') then
      e;
    elif e :: '{specfunc({Weight, Categorical,
                          Fanout, Split, Nop, Add,
                          exp, log, idx, And, Or, Not}),
                `+`, `*`, `^`, `..`, boolean, indexed, list}' then
      map(procname, _passed);
    elif e :: 'Context(anything, anything)' then
      kb1 := assert(op(1,e), kb);
      applyop(procname, 2, e, kb1);
    elif e :: 'specfunc(piecewise)' then
      kb_piecewise(e, kb, ((lhs, kb) -> lhs), summarize_throughout);
    elif e :: 'lam(name, anything, anything)' then
      x, kb1 := genType(op(1,e), op(2,e), kb);
      e1 := summarize_throughout(eval(op(3,e), op(1,e)=x), kb1);
      subsop(1=x, 3=e1, e);
    elif e :: 'ary(anything, name, anything)' then
      x, kb1 := genType(op(2,e), HInt(closed_bounds(0..op(1,e)-1)), kb);
      e1 := summarize_throughout(eval(op(3,e), op(2,e)=x), kb1);
      subsop(2=x, 3=e1, e);
    elif e :: 'And(specfunc({sum, Sum, product, Product}),
                   anyfunc(anything, name=range))' then
      rng := map(summarize_throughout, op([2,2],e), kb);
      x, kb1 := genType(op([2,1],e), HInt(closed_bounds(rng)), kb);
      e1 := eval(op(1,e), op([2,1],e)=x);
      if op(0, e) in '{sum, Sum}' and has(e1, 'piecewise') then
        mr, f := summarize(e1, kb, x, summary);
        if hasfun(mr, '{Fanout, Index}') then
          mr := summarize_throughout(mr, kb1);
          return Eval(simplify_factor_assuming(f, kb),
                      summary = Bucket(mr, x=rng));
        end if;
      end if;
      e1 := summarize_throughout(e1, kb1);
      subsop(2=(x=rng), 1=e1, e);
    else
      error "summarize_throughout doesn't know how to handle %1", e;
    end if;
  end proc;
end module; # Summary
