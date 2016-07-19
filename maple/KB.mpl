# Date: Thu, 24 Mar 2016 18:55:55 -0400
# From: Chung-chieh Shan <ccshan@indiana.edu>
# To: Jacques Carette <carette@mcmaster.ca>
# Subject: Re: partial implementation
#
# Great, let's say a KB means a set of tuples -- in other words, a n-ary
# relation.  (I'm going to treat all variables as parameters for now.)
# So "empty" means the singleton set containing unit, and "gen*" means
# to increment the dimensionality n by 1, such as taking the Cartesian
# product of a relation with an interval.  And "assert" makes a subset.
#
# [...]  let me define subtraction semantically.  Subtraction means
# coming up with a (hopefully compact) sequence of "gen*" and "assert"
# operations that take you from one KB to another.  Of course, for that
# to be possible, the source KB must be a superset of a projection of the
# destination KB.  (Here by projection I mean in the relational database
# sense.)

KB := module ()
  option package;
  local KB, Introduce, Let, Constrain, t_intro, t_lo, t_hi,
        assert_deny, log_metric, boolean_if, coalesce_bounds, htype_to_property,
        myexpand_product, chilled, chill, warm,
        ModuleLoad, ModuleUnload;
  export empty, genLebesgue, genType, genLet, assert, (* `&assuming` *) 
         kb_subtract, simplify_assuming, kb_to_assumptions, kb_to_equations,
         kb_piecewise, list_of_mul, range_of_HInt;
  global t_kb, `expand/product`, `simplify/int/simplify`;
  uses Hakaru;

  t_intro := 'Introduce(name, specfunc({AlmostEveryReal,HReal,HInt}))';
  t_lo    := 'identical(`>`,`>=`)';
  t_hi    := 'identical(`<`,`<=`)';

  empty := KB();

  genLebesgue := proc(xx::name, lo, hi, kb::t_kb)
    # The value of a variable created using genLebesgue is respected only up to
    # negligible changes
    genType(xx, AlmostEveryReal(Bound(`>`,lo), Bound(`<`,hi)), kb, _rest)
  end proc;

  genType := proc(xx::name, tt::t_type, kb::t_kb)
    # A variable created using genType is a parameter, in the sense that its
    # value is completely respected
    local x, t;
    x := `if`(depends([t,kb,_rest], xx), gensym(xx), xx);
    t := evalindets(tt, identical(Bound(`>` , -infinity),
                                  Bound(`>=`, -infinity),
                                  Bound(`<` ,  infinity),
                                  Bound(`<=`,  infinity)), _->NULL);
    x, KB(Introduce(x, t), op(kb));
  end proc;

  genLet := proc(xx::name, e, kb::t_kb)
    # A let-binding, assigning a known value to a new variable
    local x, t;
    x := `if`(depends([e,kb,_rest], xx), gensym(xx), xx);
    x, KB(Let(x, e), op(kb));
  end proc;

  assert := proc(b, kb::t_kb, $)
    assert_deny(foldl(eval, b, op(kb_to_equations(kb))), true, kb)
  end proc;

  assert_deny := proc(bb, pol::identical(true,false), kb::t_kb, $)
    # Add `if`(pol,bb,Not(bb)) to kb and return the resulting KB.
    local as, b, log_b, k, x, rel, e, ch, c, kb1, y;
    if bb = pol then
      # Ignore literal true and Not(false).
      kb
    elif bb :: `if`(pol, '{specfunc(anything, And), `and`}',
                         '{specfunc(anything, Or ), `or` }') then
      foldr(((b,kb) -> assert_deny(b, pol, kb)), kb, op(bb))
    elif bb :: '{specfunc(anything, Not), `not`}' then
      foldr(((b,kb) -> assert_deny(b, not pol, kb)), kb, op(bb))
    else
      as := chill(kb_to_assumptions(kb));
      b := chill(bb);
      b := simplify(b) assuming op(as);
      b := warm(b);
      # Look through kb for the innermost scope where b makes sense.
      k := select((k -> k :: Introduce(name, anything) and depends(b, op(1,k))),
                  kb);
      if nops(k) > 0 then
        x, k := op(op(1,k));
        # Found the innermost scope where b makes sense.
        # Reduce (in)equality between exp(A) and exp(B) to between A and B.
        do
          try log_b := map(simplify@ln, b) assuming op(as); catch: break; end try;
          if log_metric(log_b, x) < log_metric(b, x)
             and (andmap(e->is(e,real)=true, log_b) assuming op(as)) then
            b := log_b;
          else
            break;
          end if;
        end do;
        if b :: And(relation, Or(anyop(identical(x), freeof(x)),
                                 anyop(freeof(x), identical(x)))) then
          # b is a bound on x, so compare it against the current bound on x.
          # First, express `if`(pol,b,Not(b)) as rel(x,e)
          rel := op(0,b);
          if x = lhs(b) then
            e := rhs(b);
          else#x=rhs(b)
            e := lhs(b);
            rel := subs({`<`=`>`, `<=`=`>=`}, rel);
          end if;
          if not pol then
            rel := subs({`<`=`>=`, `<=`=`>`,
                         `>`=`<=`, `>=`=`<`,
                         `=`=`<>`, `<>`=`=`}, rel);
          end if;
          if k :: 'specfunc(AlmostEveryReal)' then
            rel := subs({`<=`=`<`, `>=`=`>`}, rel);
          end if;
          if rel = `=` then
            # To assert that x=e, it's not enough to supersede the Introduce
            # binding for x with a Let binding.
            kb1 := KB(Bound(x,`=`,e), op(kb));
            # We also need to assert that e is in bounds for x.
            for c in t_lo, t_hi do
              c := [op(map2(subsop, 1=NULL,
                       select(type, kb, Bound(identical(x), c, anything)))),
                    op(select(type, k , Bound(              c, anything)) )];
              if nops(c)>0 then
                kb1 := assert_deny(op([1,1],c)(e,op([1,2],c)), true, kb1)
              end if
            end do;
            return kb1
          end if;
          ch := chill(e);
          if rel = `<>` then
            # Refine <> to > or < if possible.
            if   is(x<=ch) assuming op(as) then rel := `<`
            elif is(x>=ch) assuming op(as) then rel := `>`
            else return KB(Constrain(x<>e), op(kb)) end if
          end if;
          # Strengthen strict inequality on integer variable.
          if op(0,k) = HInt then
            if rel = `>` then
              rel := `>=`;
              ch  := floor(ch)+1 assuming op(as);
              e   := warm(ch)
            elif rel = `<` then
              rel := `<=`;
              ch  := ceil(ch)-1 assuming op(as);
              e   := warm(ch)
            end if
          end if;
          # Look up the current bound on x, if any.
          c := `if`(rel :: t_lo, t_lo, t_hi);
          c := [op(map2(subsop, 1=NULL,
                   select(type, kb, Bound(identical(x), c, anything)))),
                op(select(type, k , Bound(              c, anything)) )];
          if nops(c) > 0 then c := chill(op(1,c)) end if;
          # Compare the new bound rel        (x,e          )
          # against the old bound op([1,1],c)(x,op([1,2],c))
          if e = `if`(rel :: t_lo, -infinity, infinity)
            or nops(c)>0 and (is(rel(y,ch)) assuming
                                op(1,c)(y,op(2,c)),
                                y::htype_to_property(k), op(as)) then
            # The old bound renders the new bound superfluous.
            return kb
          elif nops(c)=0 or (is(op(1,c)(y,op(2,c))) assuming
                               rel(y,ch),
                               y::htype_to_property(k), op(as)) then
            # The new bound supersedes the old bound.
            return KB(Bound(x,rel,e), op(kb))
          end if
        else
          # Try to make b about x using convert/piecewise.
          c := 'piecewise'(chill(b), true, false);
          if not hastype(c, And(name, Not(identical(x)), dependent(x)))
             # Avoid bug in convert/piecewise:
             # > convert(piecewise(i<=size[idx[a,i]]-2,true,false),piecewise,i);
             # Error, (in unknown) too many levels of recursion
          then
            try
              c := convert(c, 'piecewise', x) assuming op(as);
            catch: c := FAIL end try;
            if c :: 'specfunc(boolean, piecewise)' and not has(c, 'RootOf') then
              c := foldr_piecewise(boolean_if, false, warm(c));
              if c <> b then return assert_deny(c, pol, kb) end if
            end if
          end if
        end if
      end if;
      # Normalize `=` and `<>` constraints a bit.
      if not pol then
        # Negate b
        if   b :: `=`  then b := `<>`(op(b))
        elif b :: `<>` then b := `=` (op(b))
        elif b :: `<`  then b := `>=`(op(b))
        elif b :: `<=` then b := `>` (op(b))
        else b := Not(b) end if
      end if;
      if b :: 'Not({name, size(name)})
               = And(name, Not(constant), Not(undefined))' then
        b := (rhs(b)=lhs(b))
      end if;
      # Add constraint to KB.
      ch := chill(b);
      `if`((is(ch) assuming op(as)), kb, KB(Constrain(b), op(kb)))
    end if
  end proc:

  log_metric := proc(e, x, $)
    local m, L;
    m := indets(e, 'exp'('dependent'(x)));
    length(subsindets(map2(op, 1, m), name, _->L));
  end proc:

  boolean_if := proc(cond, th, el, $)
    # boolean_if should be equivalent to `if`, but it assumes
    # all its arguments are boolean conditions, so it basically
    # simplifies "cond and th or not cond and el"
    use
      a = ((x,y)-> `if`(x=true,y, `if`(x=false,x,
                   `if`(y=true,x, `if`(y=false,y, And(x,y)))))),
      o = ((x,y)-> `if`(x=false,y, `if`(x=true,x,
                   `if`(y=false,x, `if`(y=true,y, Or (x,y)))))),
      n = (x    -> `if`(x=false,true,
                   `if`(x=true,false,             Not(x))))
    in
      o(a(cond,th), a(n(cond),el))
    end use
  end proc;

  kb_subtract := proc(kb::t_kb, kb0::t_kb, $)
    local cut;
    cut := nops(kb) - nops(kb0);
    if cut < 0 or KB(op(cut+1..-1, kb)) <> kb0 then
      error "%1 is not an extension of %2", kb, kb0;
    end if;
    map(proc(k, $)
      local x, t;
      if k :: 'Introduce(name, anything)' then
        x, t := op(k);
        if t :: 'specfunc(AlmostEveryReal)' then
          t := [op(t), Bound(`>`, -infinity), Bound(`<`, infinity)];
          [genLebesgue, x,
           op([1,2], select(type, t, Bound(identical(`>`), anything))),
           op([1,2], select(type, t, Bound(identical(`<`), anything)))]
        else
          [genType, x, t]
        end if
      elif k :: 'Let(name, anything)' then
        [genLet, op(k)]
      elif k :: 'Bound(name, anything, anything)' then
        [assert, op(2,k)(op(1,k),op(3,k))]
      elif k :: 'Constrain(anything)' then
        [assert, op(1,k)]
      end if
    end proc, [op(coalesce_bounds(KB(op(1..cut, kb))))])
  end proc;

  coalesce_bounds := proc(kb::t_kb, $)
    local lo, hi, eq, rest, k, x, t, b, s, r;
    for k in select(type, kb, t_intro) do
      x, t := op(k);
      b, t := selectremove(type, t, Bound(t_lo, anything));
      if nops(b) > 0 then lo[x] := op(1,b) end if;
      b, t := selectremove(type, t, Bound(t_hi, anything));
      if nops(b) > 0 then hi[x] := op(1,b) end if;
      rest[x] := [op(t)];
    end do;
    for k in select(type, kb, Bound(name, identical(`=`), anything)) do
      eq[op(1,k)] := op(3,k);
    end do;
    for k in select(type, kb, Bound(name, t_lo, anything)) do
      lo[op(1,k)] := subsop(1=NULL,k);
    end do;
    for k in select(type, kb, Bound(name, t_hi, anything)) do
      hi[op(1,k)] := subsop(1=NULL,k);
    end do;
    map(proc(k, $)
      if k :: t_intro then
        x := op(1,k);
        if eq[x] = evaln(eq[x]) then
          subsop(2=op([2,0],k)(op(select(type, [lo[x],hi[x]], specfunc(Bound))),
                               op(rest[x])),
                 k);
        else
          Let(x, eq[x]);
        end if
      elif k :: 'Bound(name, anything, anything)'
           and rest[op(1,k)] :: 'list' then
        NULL;
      else
        k;
      end if;
    end proc, kb);
  end proc;

  simplify_assuming := proc(ee, kb::t_kb, $)
    local e, as;
    e := foldl(eval, ee, op(kb_to_equations(kb)));
    e := evalindets(e, 'And(specfunc({%product, product}),
                            anyfunc(anything, name=range))', myexpand_product);
    e := evalindets(e, 'specfunc(sum)', expand);
    as := [op(kb_to_assumptions(kb)),
           op(map(`::`, indets(e, 'specfunc(size)'), nonnegint))];
    e := chill(e);
    as := chill(as);
    try
      e := evalindets(e, {logical,
                          specfunc({And,Or,Not}),
                          specop(algebraic,{`<`,`<=`,`=`,`<>`})},
        proc(b, $)
          try
            if is(b) assuming op(as) then return true
            elif false = coulditbe(b) assuming op(as) then return false
            end if
          catch:
          end try;
          b
        end proc);
      e := simplify(e) assuming op(as);
    catch "when calling '%1'. Received: 'contradictory assumptions'":
      # We seem to be on an unreachable control path
      userinfo(1, 'procname', "Received contradictory assumptions.")
    end try;
    e := warm(e);
    eval(e, exp = expand @ exp);
  end proc;

  myexpand_product := proc(prod :: anyfunc(anything, name=range), $)
    local x, p, body, quantifier, l, i;
    (body, quantifier) := op(prod);
    x := op(1, quantifier);
    p := proc(e, $)
      local ee;
      if e :: 'exp(anything)' then
        ee := expand(op(1,e));
        ee := convert(ee, 'list', `+`);
        `*`(op(map(z -> exp(sum(z, quantifier)), ee)));
      elif e :: ('freeof'(x) ^ 'anything') then
        op(1,e) ^ expand(sum(op(2,e), quantifier))
      elif e :: ('anything' ^ 'freeof'(x)) then
        p(op(1,e)) ^ op(2,e)
#  This is the right thing to do, but breaks things.  
#      elif e :: 'idx'('freeof'(x),'anything') then
#        l := op(1,e);
#        product(idx(l,i)^sum(piecewise(op(2,e)=i, 1, 0), quantifier), i=0..size(l)-1);
      else
        product(e, quantifier)
      end if
    end proc;
    maptype(`*`, p, body)
  end proc;

  kb_to_assumptions := proc(kb, $)
    map(proc(k, $)
      local x;
      if k :: t_intro then
        x := op(1,k);
        (x :: htype_to_property(op(2,k))),
        op(map((b -> op(1,b)(x, op(2,b))), op(2,k)))
      elif k :: 'Let(anything, anything)' then
        `=`(op(k))
      elif k :: 'Bound(anything, anything, anything)' then
        op(2,k)(op(1,k), op(3,k))
      elif k :: 'Constrain(anything)' then
        op(1,k)
      else
        NULL # Maple doesn't understand our other types
      end if
    end proc, [op(coalesce_bounds(kb))])
  end proc;

  (*** #Code removed by Carl 2016Jul8. Maybe we'll need it again.
  #Written by Carl 2016Jun24.
  #This is a wrapper for `assuming` that gracefully handles the case of no
  #assumptions and accepts the assumptions in our "knowledge base"/"context"
  #format.
  #
  #Note that the 2nd parameter, corresponding to the right operand, is a list,
  #possibly empty; whereas the right operand of regular `assuming` is a nonNULL
  #expression sequence.

  `&assuming`:= proc(e::uneval, ctx::list, $)
  local as:= kb_to_assumptions(foldr(assert, empty, ctx[]));
       userinfo(3, _KB, print(e &where (e-> e=eval(e))~(<op(e)>)));
       if as = [] then
           eval(e)
       else
           userinfo(3, _KB, "`assuming` clause:", as[]);
           e assuming as[]
       end if
  end proc;
  ***)

  kb_to_equations := proc(kb, $)
    local lets, constraints;

    lets := map2(subsop, 0=`=`, [op(select(type, kb, 'Let(name, anything)'))]);
    constraints := map(op, select(type, kb, 'Constrain(anything = anything)'));
    [op(lets), op(constraints)]
  end proc;

  htype_to_property := proc(t::t_type, $)
    if t :: 'specfunc({AlmostEveryReal, HReal})' then real
    elif t :: 'specfunc(HInt)' then integer
    else TopProp end if
  end proc;

  kb_piecewise := proc(e :: specfunc(piecewise), kb :: t_kb, doIf, doThen, $)
    local kb1, update, n, i;
    kb1 := kb;
    update := proc(c, $)
      local kb0;
      kb0 := assert(    c , kb1);
      kb1 := assert(Not(c), kb1); # Mutation!
      kb0
    end proc;
    n := nops(e);
    piecewise(seq(`if`(i::even, doThen(op(i,e), update(op(i-1,e))),
                   `if`(i=n,    doThen(op(i,e), kb1),
                                doIf  (op(i,e), kb1))),
                  i=1..n))
  end proc;

  # Like convert(e, 'list', `*`) but tries to keep the elements positive
  list_of_mul := proc(e, kb::t_kb, $)
    local rest, should_negate, can_negate, fsn;
    rest := convert(e, 'list', `*`);
    rest := zip(((f,s) -> [f, s, `if`(f::specfunc({Sum,sum}), applyop(`-`,1,f),
                                                              -f)]),
                rest, simplify_assuming(map(''signum'', rest), kb));
    should_negate, rest := selectremove(type, rest,
      '[anything, -1, Not(`*`)]');
    if nops(should_negate) :: even then
      [seq(op(3,fsn), fsn=should_negate),
       seq(op(1,fsn), fsn=rest)]
    else
      can_negate, rest := selectremove(type, rest,
        '[{`+`, specfunc({Sum,sum})}, Not(1), Not(`*`)]');
      if nops(can_negate) > 0 then
        [seq(op(3,fsn), fsn=should_negate),
         op([1,3], can_negate),
         seq(op(1,fsn), fsn=subsop(1=NULL, can_negate)),
         seq(op(1,fsn), fsn=rest)]
      else
        [seq(op(3,fsn), fsn=subsop(-1=NULL, should_negate)),
         op([-1,1], should_negate),
         seq(op(1,fsn), fsn=rest)]
      end if
    end if
  end proc;

  range_of_HInt := proc(t :: And(specfunc(HInt), t_type), $)
       op(1, [op(map((b -> `if`(op(1,b)=`>`, floor(op(2,b))+1, op(2,b))),
                     select(type, t, Bound(t_lo,anything)))),
              -infinity])
    .. op(1, [op(map((b -> `if`(op(1,b)=`<`, ceil(op(2,b))-1, op(2,b))),
                     select(type, t, Bound(t_hi,anything)))),
              infinity]);
  end proc;

  # Avoid FAILure modes of the assumption system
  chilled := '{size, idx}';
  chill := e -> subsindets(e, specfunc(chilled), c->op(0,c)[op(c)]);
  warm := e -> subsindets(e, specindex(chilled), c->map(warm, op(0,c)(op(c))));

  ModuleLoad := proc($)
    Hakaru; # Make sure the KB module is loaded, for the type t_type
    TypeTools[AddType](t_kb,
      'specfunc({
         Introduce(name, t_type),
         Let(name, anything),
         Bound(name, identical(`<`,`<=`,`>`,`>=`,`=`), anything),
         Constrain({`::`, boolean, `in`, specfunc(anything,{Or,Not})})
       }, KB)');

    # Prevent expand(product(f(i),i=0..n-1))
    # from producing (product(f(i),i=0..n))/f(n)
    `expand/product` := overload([
      proc(ff, rr::name=And(`+`,Not(`+`(Not(integer))))..anything)
        option overload(callseq_only);
        thaw(`expand/product`(ff, applyop(freeze, [2,1], rr)))
      end proc,
      proc(ff, rr::name=anything..And(`+`,Not(`+`(Not(integer)))))
        option overload(callseq_only);
        thaw(`expand/product`(ff, applyop(freeze, [2,2], rr)))
      end proc,
      `expand/product`]);

    # Prevent simplify(product(1-x[i],i=0..n-1))
    # from producing (-1)^n*product(-1+x[i],i=0..n-1)
    `simplify/int/simplify` := overload([
      proc (f::identical(product), a::`+`, r::{name,name=anything}, $)
        option overload(callseq_only);
        return 'f'(a,r);
      end proc,
      `simplify/int/simplify`]);
  end proc;

  ModuleUnload := proc($)
    TypeTools[RemoveType](t_kb);
  end proc;

  ModuleLoad();
end module; # KB
