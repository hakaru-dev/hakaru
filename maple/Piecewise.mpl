# Various useful routines for handling piecewise (and piecewise-like) 

Piecewise := module()
  option package;
  local lift1_piecewise;
  export piecewise_And, map_piecewiselike, lift_piecewise, foldr_piecewise,
    make_piece,
    ModuleLoad, ModuleUnload;
  global
     # Structure types for piecewise-like expressions:
     # piecewise, case, and idx into literal array
         t_piecewiselike;
  
  # Try to prevent PiecewiseTools:-Is from complaining
  # "Wrong kind of parameters in piecewise"
  make_piece := proc(rel, $)
    if rel :: {specfunc(anything, {And,Or,Not}), `and`, `or`, `not`} then
      map(make_piece, rel)
    elif rel :: {'`::`', 'boolean', '`in`'} then
      rel
    else
      rel = true
    end if
  end proc;

  # do some trivial simplifications of a piecewise of an And of conditions
  piecewise_And := proc(cond::list, th, el, $)
    if nops(cond) = 0 or th = el then
      th
    else
      piecewise(And(op(cond)), th, el)
    end if
  end proc;

  # map into piecewise, case and idx
  map_piecewiselike := proc(f, p::t_piecewiselike)
    local i, g, h;
    if p :: 'specfunc(piecewise)' then
      piecewise(seq(`if`(i::even or i=nops(p), f(op(i,p),_rest), op(i,p)),
                    i=1..nops(p)))
    elif p :: 't_case' then
      # Mind the hygiene
      subsindets(eval(subsop(2 = map[3](applyop, g, 2, op(2,p)), p),
                      g=h(f,_rest)),
                 'typefunc(specfunc(h))',
                 (e -> op([0,1],e)(op(1,e), op(2..-1,op(0,e)))))
    elif p :: 'idx(list, anything)' then
      idx(map(f,op(1,p),_rest), op(2,p))
    else
      error "map_piecewiselike: %1 is not t_piecewiselike", p
    end if
  end proc;

  # "lift" piecewise from inside `+`, `*`, `^` and exp to outside
  lift_piecewise := proc(e, extra:={}, $)
    local e1, e2;
    e2 := e;
    while e1 <> e2 do
      e1 := e2;
      e2 := subsindets(e1,
              '{extra,
                And(`+`, Not(specop(Not(specfunc(piecewise)), `+`))),
                And(`*`, Not(specop(Not(specfunc(piecewise)), `*`))),
                And(`^`, Not(specop(Not(specfunc(piecewise)), `^`))),
                exp(specfunc(piecewise))}',
              lift1_piecewise)
    end do
  end proc;

  # given an expression where one of the argument operands is a
  # piecewise, lift that piecewise to the top
  lift1_piecewise := proc(e, $)
    local i, p;
    if membertype(t_piecewiselike, [op(e)], 'i') then
      p := op(i,e);
      if nops(p) :: even and not (e :: `*`) and op(-1,p) <> 0 then
        p := piecewise(op(p), 0);
      end if;
      map_piecewiselike((arm->lift1_piecewise(subsop(i=arm,e))), p)
    else
      e
    end if
  end proc;

  foldr_piecewise := proc(cons, nil, pw, $) # pw may or may not be piecewise
    # View pw as a piecewise and foldr over its arms
    if pw :: 'specfunc(piecewise)' then
      foldr(proc(i,x) cons(op(i,pw), op(i+1,pw), x) end proc,
            `if`(nops(pw)::odd, cons(true, op(-1,pw), nil), nil),
            seq(1..nops(pw)-1, 2))
    else
      cons(true, pw, nil)
    end if
  end proc;

  thismodule:-ModuleLoad := proc($)
    TypeTools[AddType](t_piecewiselike,
      '{specfunc(piecewise), t_case, idx(list, anything)}');
  end proc;

  thismodule:-ModuleUnload := proc($)
    TypeTools[RemoveType](t_piecewiselike);
  end proc;

  thismodule:-ModuleLoad();
end:
