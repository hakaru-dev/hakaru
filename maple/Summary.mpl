`depends/Bucket` := proc(mr, r::(name=range), x, $)
  depends(rhs(r), x) or depends(mr, x minus {lhs(r)})
end proc:

`depends/Index` := proc(n, o::name, e, mr, x, $)
  depends({n,e}, x) or depends(mr, x minus {o})
end proc:

# note that v _can_ occur in m1.
`depends/Let` := proc(m1, v::name, m2, x, $)
  depends(m1, x) or depends(m2, x minus {v})
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

`eval/Let` := proc(e, eqs, $)
  local m1, v, m2;
  m1, v, m2 := op(e);
  eval(op(0,e), eqs)(eval(m1, eqs), BindingTools:-generic_evalat(v, m2, eqs))
end proc:

Summary := module ()
  option package;
  export RoundTrip, Summarize, SummarizeKB, bucket, summarize;
  global Bucket, Fanout, Index, Split, Nop, Add, Let,
         SumIE, ProductIE, BucketIE;
  uses Hakaru, KB;

  RoundTrip := proc(e)
    local result;
    interface(screenwidth=9999, prettyprint=0, warnlevel=0,
      showassumed=0,quiet=true);
    kernelopts(assertlevel=0);
    result := eval(ToInert(Summarize(_passed)), _Inert_ATTRIBUTE=NULL);
    lprint(result)
  end proc;

  Summarize := proc(e, {ctx :: list := []}, $)
    local ie;
    ie := table('[sum    =SumIE    , Sum    =SumIE    ,
                  product=ProductIE, Product=ProductIE,
                  bucket =BucketIE , Bucket =BucketIE ]');
    subsindets(SummarizeKB(e, foldr(assert, empty, op(ctx))),
               And(specfunc({indices(ie, 'nolist')}),
                   anyfunc(anything, anything=range)),
               e -> subsop(0 = ie[op(0,e)],
                           applyop(`+`, [2,2,2], e, 1)))
  end proc;

  SummarizeKB := proc(e, kb :: t_kb, $)
    local patterns, x, kb1, e1, rng, summary, mr, f;
    if not hasfun(e, '{Sum,sum}', 'piecewise') then
      e;
    elif e :: '{known_continuous, known_discrete,
                specfunc({Msum, Weight, Fanout, Split, Nop, Add,
                          exp, log, GAMMA, Beta, idx, And, Or, Not}),
                `+`, `*`, `^`, `..`, boolean, indexed, list}' then
      map(procname, _passed);
    elif e :: 'Context(anything, anything)' then
      kb1 := assert(op(1,e), kb);
      applyop(procname, 2, e, kb1);
    elif e :: 'specfunc(piecewise)' then
      kb_piecewise(e, kb, ((lhs, kb) -> lhs), SummarizeKB);
    elif e :: 'lam(name, anything, anything)' then
      patterns := htype_patterns(op(2,e));
      if patterns :: Branches(Branch(PVar(name),anything)) then
        # Eta-expand the function type
        x := op(1,e);
        x, kb1 := genType(x, op(2,e), kb);
        e1 := eval(op(3,e), op(1,e)=x);
        lam(x, op(2,e), SummarizeKB(e1, kb1))
      else
        # Eta-expand the function type and the sum-of-product argument-type
        x := op(1,e);
        if depends([e,kb], x) then x := gensym(x) end if;
        e1 := eval(op(3,e), op(1,e)=x);
        lam(x, op(2,e), 'case'(x,
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
                       SummarizeKB(eval(eval(e1,eSubst),pSubst1), kb1))
              end proc,
              patterns)))
      end if
    elif e :: 'ary(anything, name, anything)' then
      x, kb1 := genType(op(2,e), HInt(closed_bounds(0..op(1,e)-1)), kb);
      e1 := SummarizeKB(eval(op(3,e), op(2,e)=x), kb1);
      subsop(2=x, 3=e1, e);
    elif e :: 'And(specfunc({sum, Sum, product, Product}),
                   anyfunc(anything, name=range))' then
      rng := op([2,2],e);
      x, kb1 := genType(op([2,1],e), HInt(closed_bounds(rng)), kb);
      rng := map(SummarizeKB, rng, kb);
      e1 := eval(op(1,e), op([2,1],e)=x);
      if op(0, e) in '{sum, Sum}' and has(e1, 'piecewise') then
        mr, f := summarize(e1, kb, x=rng, summary);
        if hasfun(mr, '{Fanout, Index}') then
          mr := SummarizeKB(mr, kb1);
          return Let(Bucket(mr, x=rng),
                     summary,
                     NewSLO:-simplify_factor_assuming(f, kb));
        end if;
      end if;
      e1 := SummarizeKB(e1, kb1);
      subsop(2=(x=rng), 1=e1, e);
    else
      error "SummarizeKB doesn't know how to handle %1", e;
    end if;
  end proc;

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

  summarize := proc(ee, kb :: t_kb, ii :: name=range, summary, $)
    local i, rng, e, r, s,
          e1, mr1, f1, e2, mr2, f2,
          variables, var_outerness, outermost, thunk, consider,
          o, t, lo, hi, b, a;
    i, rng := op(ii);

    # Try to ensure termination
    e := simplify_assuming(ee, kb);
    if length(e) >= length(ee) then e := ee end if;

    # Nop rule
    if Testzero(e) then return Nop(), 0 end if;

    # Kronecker expansion (https://github.com/hakaru-dev/hakaru/issues/104):
    # rewrite sum(f(i = b), i=rng) to
    #         sum(f(false), i=rng) +
    #         piecewise(..., eval(f(true) - f(false), i=b), 0)
    for r in select(depends, indets(e, '{`=`, `<>`}'), i) do
      if not ispoly(`-`(op(r)), 'linear', i, 'b', 'a') then next end if;
      b := Normalizer(-b/a);
      e2 := eval(e, {subsop(0=`<>`,r)=true, subsop(0=`=` ,r)=false});
      if length(e2) >= length(e) then next end if;
      e1 := eval(e, {subsop(0=`=` ,r)=true, subsop(0=`<>`,r)=false});
      f1 := 'piecewise'(And(b::integer, lhs(rng)<=b, b<=rhs(rng)),
                        eval(e1-e2, i=b),
                        0);
      if has(f1, '{undefined, infinity, FAIL}') then next end if;
      mr2, f2 := summarize(e2, kb, ii, summary);
      return mr2, f1 + f2;
    end do;

    r := indets(e, '{relation, logical, specfunc({And,Or})}');
    s, r := selectremove(depends, r, i);
    # Fanout rule
    r := sort(convert(r, 'list'), 'length');
    while nops(r) > 0 do
      e1 := eval(e, r[-1]=true);  if e = e1 then r := r[1..-2]; next end if;
      e2 := eval(e, r[-1]=false); if e = e2 then r := r[1..-2]; next end if;
      mr1, f1 := summarize(e1, kb, ii, 'fst(summary)');
      mr2, f2 := summarize(e2, kb, ii, 'snd(summary)');
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
        for o in indets(r, 'name') minus {i} do
          if not (var_outerness[o] :: integer) then next end if;
          if StringTools:-IsPrefix('docUpdate', o) then next end if;
          if StringTools:-IsPrefix('wordUpdate', o) then next end if;
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
            mr, f := summarize(e1, kb, ii, 'idx'(summary, o-lo));
            Index(hi-lo+1, o, b, mr),
              'piecewise'(And(o::integer, lo<=o, o<=hi), f, 0);
          end proc)(e1, o, lo, hi, b));
        end do;
      end if;
      # Split rule
      consider(r, ((e1, e2, r) -> proc($)
        local mr1, f1, mr2, f2;
        mr1, f1 := summarize(e1, kb, ii, 'fst(summary)');
        mr2, f2 := summarize(e2, kb, ii, 'snd(summary)');
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
end module; # Summary
