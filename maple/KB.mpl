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
        assert_deny, boolean_if, coalesce_bounds, htype_to_property,
        myexpand_product, chilled, chill, warm,
        ModuleLoad, ModuleUnload;
  export empty, genLebesgue, genType, genLet, assert,
         kb_subtract, simplify_assuming, kb_to_assumptions, kb_to_equations,
         kb_piecewise, range_of_HInt;
  global t_kb;
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
      # Reduce (in)equality between exp(A) and exp(B) to between A and B.
      do
        try log_b := map(ln, b) assuming op(as); catch: break; end try;
        if length(log_b) < length(b)
           and (andmap(is, log_b, real) assuming op(as)) then
          b := log_b;
        else
          break;
        end if;
      end do;
      b := warm(b);
      # Look through kb for the innermost scope where b makes sense.
      k := select((k -> k :: Introduce(name, anything) and depends(b, op(1,k))),
                  kb);
      if nops(k) > 0 then
        x, k := op(op(1,k));
        # Found the innermost scope where b makes sense.
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
          try
            c := 'piecewise'(chill(b), true, false);
            c := convert(c, 'piecewise', x) assuming op(as);
            if c :: 'specfunc(boolean, piecewise)' and not has(c, 'RootOf') then
              c := foldr_piecewise(boolean_if, false, warm(c));
              if c <> b then return assert_deny(c, pol, kb) end if
            end if
          catch:
          end try;
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
      if b :: 'anything=name' then b := (rhs(b)=lhs(b)) end if;
      # Add constraint to KB.
      ch := chill(b);
      `if`((is(ch) assuming op(as)), kb, KB(Constrain(b), op(kb)))
    end if
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
    e := evalindets(e, 'specfunc({%product, product})', myexpand_product);
    e := evalindets(e, 'specfunc(sum)', expand);
    e := chill(e);
    as := chill(kb_to_assumptions(kb));
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
    end try;
    e := warm(e);
    eval(e, exp = expand @ exp);
  end proc;

  myexpand_product := proc(prod, $)
    local x, p, body, quantifier;
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
      else
        product(e, quantifier)
      end if
    end proc;
    `*`(op(map(p, convert(body, list, `*`))));
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

  kb_to_equations := proc(kb, $)
    map2(subsop, 0=`=`, [op(select(type, kb, 'Let(name, anything)'))])
  end proc;

  htype_to_property := proc(t::t_type, $)
    if t :: 'specfunc({AlmostEveryReal, HReal})' then real
    elif t :: 'specfunc(HInt)' then integer
    else TopProp end if
  end proc;

  kb_piecewise := proc(e :: specfunc(piecewise), kb :: t_kb, doIf, doThen, $)
    local kb1, update, n, i;
    kb1 := kb;
    update := proc(c)
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
  end proc;

  ModuleUnload := proc($)
    TypeTools[RemoveType](t_kb);
  end proc;

  ModuleLoad();
end module; # KB
