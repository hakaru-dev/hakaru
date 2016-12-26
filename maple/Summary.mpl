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
  export summarize;
  global Bucket, Fanout, Index, Split, Nop, Add;
  uses Hakaru, KB;

  summarize := proc(ee,
                    kb :: t_kb,
                    i :: {name,list(name),set(name)},
                    summary, $)
    local e, r, s,
          e1, mr1, f1, e2, mr2, f2,
          variables, var_outerness, outermost, thunk, consider,
          o, t, lo, hi, b, a;
    e := simplify_assuming(ee, kb);
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
      consider(r, ((e1, e2) -> proc($)
        local mr1, f1, mr2, f2;
        mr1, f1 := summarize(e1, kb, i, 'fst(summary)');
        mr2, f2 := summarize(e2, kb, i, 'snd(summary)');
        Split(r, mr1, mr2), f1 + f2;
      end proc)(e1, e2));
    end do;
    if thunk :: procedure then
      return thunk();
    else
      # Add rule
      return Add(e), summary;
    end if;
  end proc;
end module; # Summary
