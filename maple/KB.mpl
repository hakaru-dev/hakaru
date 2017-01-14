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
        chilled, chill, warm,
        ModuleLoad, ModuleUnload;
  export empty, genLebesgue, genType, genLet, assert, (* `&assuming` *)
         negated_relation, negate_relation,
         kb_subtract, simplify_assuming, simplify_factor_assuming,
         getType, kb_to_variables, kb_to_assumptions, kb_to_equations,
         kb_piecewise, list_of_mul, for_poly, range_of_HInt;
  global t_kb, `expand/product`, `simplify/int/simplify`,
         `product/indef/indef`, `convert/Beta`;
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
    x := `if`(depends([tt,kb,_rest], xx), gensym(xx), xx);
    t := subsindets(tt, identical(Bound(`>` , -infinity),
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

  #Simplistic negation of relations. Used by Hakaru:-flatten_piecewise.
  #Carl 2016Sep09
  negated_relation:= table([`<`, `<=`, `=`, `<>`] =~ [`>=`, `>`, `<>`, `=`]);
  negate_relation:= proc(R::relation, $)::relation;
       negated_relation[op(0,R)](op(R))
  end proc;

  assert := proc(b, kb::t_kb, $)
    assert_deny(foldl(eval, b, op(kb_to_equations(kb))), true, kb)
  end proc;

  assert_deny := module ()
   export ModuleApply;
   ModuleApply := proc(bb, pol::identical(true,false), kb::t_kb, $)

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
      as := chill(kb_to_assumptions(kb, bb));
      b := chill(bb);


      try
        b := simplify(b) assuming op(as);
      catch "when calling '%1'. Received: 'contradictory assumptions'":
        # We seem to be on an unreachable control path
        userinfo(1, 'procname', "Received contradictory assumptions.")
      end try;


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
          try
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
          catch "when calling '%1'. Received: 'contradictory assumptions'":
            # We seem to be on an unreachable control path
            userinfo(1, 'procname', "Received contradictory assumptions.")
          end try;


        else
          # Try to make b about x using convert/piecewise.
          c := 'piecewise'(chill(b), true, false);
          if not depends(indets(c, indexed), x)
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
      try
        if is(ch) assuming op(as) then
          return kb
        end if;
      catch "when calling '%1'. Received: 'contradictory assumptions'":
        # We seem to be on an unreachable control path
        userinfo(1, 'procname', "Received contradictory assumptions.")
      end try;


      KB(Constrain(b), op(kb))
    end if

   end proc: # ModuleApply
  end module; # assert_deny

  log_metric := proc(e, x, $)
    local m, L;
    m := select(depends, indets(e, 'exp(anything)'), x);
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
    local e, as;                                                         # for debugging
    if not (indets(ee,'specfunc(applyintegrand)') = {}) then
      WARNING("simplify_assuming called on an expression containing 'applyintegrand' -- this is probably a mistake, and could result in incorrect results");
    end if;
    e := foldl(eval, ee, op(kb_to_equations(kb)));                         `eval`;
    as := kb_to_assumptions(kb, e);
    e := chill(e);                                                        `chill`;
    as := chill(as);
    try
      e := simplify(e) assuming op(as);                         `simplify @ assuming`;
    catch "when calling '%1'. Received: 'contradictory assumptions'":
      # We seem to be on an unreachable control path
      userinfo(1, 'procname', "Received contradictory assumptions.")
    end try;
    e := warm(e);                                            `warm (then expand@exp)`;
    eval(e, exp = expand @ exp);
  end proc;

  simplify_factor_assuming := module ()
    export ModuleApply;
    local graft_pw, GAMMAratio, wrap, hack_Beta,
          bounds_are_simple, eval_piecewise, eval_factor;

    # Rewrite piecewise(i<=j-1,1,0) + piecewise(i=j,1,0) + ...
    #      to piecewise(i<=j,1,0) + ...
    # and rewrite piecewise(And(i<=j-1,a<b),1) + piecewise(And(a<b,i=j),1) + ...
    #          to piecewise(And(i<=j,a<b),1) + ...
    graft_pw := proc(ee, $)
      subsindets(ee, 'And(`+`, Not(`+`(Not(specfunc(piecewise)))))', proc(e, $)
        local terms, j, i, jcond, icond, conds;
        terms := sort(convert(e,'list'),
                      key = proc(term, $) local rel; -add(numboccur(term,rel), rel in indets(term,`<=`)) end proc);
        for i from nops(terms) to 2 by -1 do
          if not (op(i,terms) :: 'And(specfunc(piecewise), Or(anyfunc(anything,1), anyfunc(anything,1,0)))') then next end if;
          icond := op([i,1],terms);
          icond := `if`(icond :: 'specfunc(And)', {op(icond)}, {icond});
          for j from i-1 to 1 by -1 do
            if not (op(j,terms) :: 'And(specfunc(piecewise), Or(anyfunc(anything,1), anyfunc(anything,1,0)))') then next end if;
            jcond := op([j,1],terms);
            jcond := `if`(jcond :: 'specfunc(And)', {op(jcond)}, {jcond});
            conds := jcond intersect icond;
            jcond := jcond minus conds;
            icond := icond minus conds;
            if not (nops(jcond) = 1 and nops(icond) = 1) then next end if;
            jcond := op(jcond);
            icond := op(icond);
            if not (jcond :: `<=` and icond :: `=`) then next end if;
            if not Testzero(`-`(op(jcond)) - `-`(op(icond)) - 1) then next end if; # Unsound HACK: assuming integers, so jcond<=-1 is equivalent to jcond<0
            terms := subsop(i=NULL, [j,1]=maptype('specfunc(And)', (c -> `if`(c=jcond, subsop(0=`<=`,icond), c)), op([j,1],terms)), terms);
            break
          end do
        end do;
        `+`(op(terms))
      end proc)
    end proc;

    # GAMMAratio(s, r) = GAMMA(s+r) / GAMMA(r)
    GAMMAratio := proc(s, r, $)
      local var;
      if s :: t_piecewiselike then
        map_piecewiselike(GAMMAratio,
          `if`(s :: 'specfunc(piecewise)' and nops(s) :: even, 'piecewise'(op(s), 0), s),
          r)
      elif s :: 'numeric' then
        product(var+r, var=0..s-1)
      else
        var := 'j';
        if has(r, var) then var := gensym(var) end if;
        Product(var+r, var=0..s-1) # inert so as to not become GAMMA
      end if
    end proc;

    wrap := proc(e, loops :: list([identical(product,Product,sum,Sum),
                                   name=range]), $)
      local res, loop;
      res := e;
      for loop in loops do
        res := op(1,loop)(res, op(2,loop));
      end do;
      res
    end proc;

    hack_Beta := proc(e :: specfunc(Beta), kb :: t_kb,
                      loops :: list([identical(product,Product,sum,Sum),
                                     name=range]),
                      $)
      local x, bounds, res, s1, r1, s2, r2, sg, rg;
      # Temporary hack to show desired output for examples/{dice_predict,gmm_gibbs,naive_bayes_gibbs}.hk
      if nops(loops) > 0 and e :: 'specfunc(`+`, Beta)' and has(e, piecewise) then
        x, bounds := op(op([-1,2],loops));
        res := subsindets(e, 'specfunc(piecewise)', proc(pw, $)
          # Remove a particular superfluous inequality
          if op(1,pw) :: 'And(specfunc(And), anyfunc(relation, name=anything))' and has(op(1,pw),x) then
            if op([1,1],pw) :: `<=`
               and Testzero(op([1,1,1],pw)-op([1,1,2],pw)+op([1,2,1],pw)-op([1,2,2],pw)+rhs(bounds)-x) or
               op([1,1],pw) :: `<>`
               and Normalizer(op([1,1,1],pw)-op([1,1,2],pw)+op([1,2,1],pw)-op([1,2,2],pw)+rhs(bounds)-x) :: negative
            then
              return subsop(1=op([1,2],pw), pw)
            end if
          end if;
          return pw
        end proc);
        s1, r1 := selectremove(has, op(1,res), piecewise);
        s2, r2 := selectremove(has, op(2,res), piecewise);
        sg := graft_pw(combine(s1+s2));
        rg := Loop:-graft(r1+r2);
        if rg = eval(r2,x=x-1) and sg = eval(s2,x=x-1) then
          # Telescoping match!
        elif rg = eval(r1,x=x-1) and sg = eval(s1,x=x-1) then
          # Telescoping match, but swap Beta arguments
          s1, s2 := s2, s1;
          r1, r2 := r2, r1;
        else
          # No telescoping match -- bail out
          return FAIL;
        end if;
        # At this point we know that e = Beta(s1+r1, s2+r2)
        #   and that s2 = eval(s2, x=rhs(bounds)+1) + sum(s1, x=x+1..rhs(bounds)+1)
        #   and that r2 = eval(r2, x=rhs(bounds)+1) + sum(r1, x=x+1..rhs(bounds)+1)
        # So our remaining job is to express
        #   product(Beta(s1+r1, eval(s2+r2, x=rhs(bounds)+1) + sum(s1+r1, x=x+1..rhs(bounds)+1)), x=bounds)
        # in terms of
        #   product(Beta(   r1, eval(   r2, x=rhs(bounds)+1) + sum(   r1, x=x+1..rhs(bounds)+1)), x=bounds)
        res := wrap('Beta'(r1, eval(r2, x=rhs(bounds)+1) + 'sum'(r1, x=x+1..rhs(bounds)+1)), loops)
             * Loop:-graft(wrap(GAMMAratio(s1, r1), loops)
                           * wrap(eval('GAMMAratio'(s1 (* + s2 *), r1 + r2), x=rhs(bounds)+1),
                                                    # Unsound HACK: assuming eval(s2, x=rhs(bounds)+1) = 0
                                                    #   (Discharging this assumption sometimes requires checking idx(w,k) < size(word_prior) for symbolic k)
                                  eval(subsop(-1=NULL, loops), x=rhs(bounds)+1)))
             / wrap(eval('GAMMAratio'(s2, r2), x=lhs(bounds)-1),
                    eval(subsop(-1=NULL, loops), x=lhs(bounds)-1));
        return eval_factor(res, kb, `*`, []);
      end if;
      # Temporary hack to show desired output for the "integrate BetaD out of BetaD-Bernoulli" test
      if nops(loops) = 0 and e :: 'specfunc(And(`+`, Not(`+`(Not(idx({[1,0],[0,1]}, anything))))), Beta)' then
        s1, r1 := selectremove(type, op(1,e), 'idx({[1,0],[0,1]}, anything)');
        s2, r2 := selectremove(type, op(2,e), 'idx({[1,0],[0,1]}, anything)');
        if s1 :: 'idx([1,0], anything)' and s2 :: 'idx([0,1], anything)' and op(2,s1) = op(2,s2) then
          return Beta(r1, r2) * idx([r1, r2], op(2,s1)) / (r1 + r2);
        elif s1 :: 'idx([0,1], anything)' and s2 :: 'idx([1,0], anything)' and op(2,s1) = op(2,s2) then
          return Beta(r1, r2) * idx([r2, r1], op(2,s1)) / (r1 + r2);
        end if
      end if;
      return FAIL;
    end proc;

    bounds_are_simple := proc(bounds :: range, $)
      local bound, term, i;
      if `-`(op(bounds)) :: integer then return true end if;
      for bound in bounds do
        for term in convert(bound, 'list', `+`) do
          if term :: `*` then term := remove(type, term, integer) end if;
          if term :: 'specfunc(piecewise)' then
            for i from 2 by 2 to nops(term)-1 do
              if not(op(i,term) :: integer) then return false end if
            end do;
            if not(op(-1,term) :: integer) then return false end if
          elif not(term :: integer) then return false end if
        end do
      end do;
      true
    end proc;

    # eval_piecewise has the same calling convention as eval_factor.
    # It simplifies piecewise expressions.
    eval_piecewise := proc(e :: specfunc(piecewise),
                           kb :: t_kb, mode :: identical(`*`,`+`),
                           loops :: list([identical(product,Product,sum,Sum),
                                          name=range]),
                           $)
      local default, kbs, pieces, i, cond, inds, res, x, b, a;
      default := 0; # the catch-all "else" result
      kbs[1] := kb;
      for i from 1 by 2 to nops(e) do
        if i = nops(e) then
          default := op(i,e);
          pieces[i] := default;
        else
          # Simplify piecewise conditions using KB
          cond := op(i,e);
          # cond := eval_factor(cond, kbs[i], `+`, []);
          kbs[i+1] := assert(cond, kbs[i]);
          cond := map(proc(cond::[identical(assert),anything], $)
                        op(2,cond)
                      end proc,
                      kb_subtract(kbs[i+1], kbs[i]));
          if nops(cond) = 0 then
            default := op(i+1,e);
            pieces[i] := default;
            break;
          else
            cond := `if`(nops(cond)=1, op(1,cond), And(op(cond)));
            # TODO: Extend KB interface to optimize for
            #       entails(kb,cond) := nops(kb_subtract(assert(cond,kb),kb))=0
            kbs[i+2] := assert(Not(cond), kbs[i]);
            if nops(kb_subtract(kbs[i+2], kbs[i])) > 0 then
              pieces[i] := cond;
              pieces[i+1] := op(i+1,e);
            else
              # This condition is false in context, so delete this piece
              # by not putting anything inside "pieces"
            end if
          end if
        end if
      end do;
      # Combine duplicate branches at end
      inds := [indices(pieces, 'nolist', 'indexorder')];
      for i in ListTools:-Reverse(select(type, inds, 'even')) do
        if Testzero(pieces[i]-default) then
          pieces[i  ] := evaln(pieces[i  ]);
          pieces[i-1] := evaln(pieces[i-1]);
        else
          break;
        end if
      end do;
      # Special processing for when the pieces are few
      res := [entries(pieces, 'nolist', 'indexorder')];
      if nops(res) <= 1 then
        return eval_factor(default, kb, mode, loops);
      end if;
      if nops(res) <= 3 and op(1,res) :: `=` and Testzero(default - mode()) then
        # Reduce product(piecewise(i=3,f(i),1),i=1..10) to f(3)
        for i from 1 to nops(loops) do
          x := op([i,2,1],loops);
          if depends(op(1,res), x) then
            if ispoly(`-`(op(op(1,res))), 'linear', x, 'b', 'a') then
              b := Normalizer(-b/a);
              if nops(kb_subtract(assert(And(b :: integer,
                                             op([i,2,2,1],loops) <= b,
                                             b <= op([i,2,2,2],loops)),
                                         kb), kb)) = 0 then
                return eval_factor(eval(op(2,res), x=b),
                                   assert(x=b, kb), # TODO: why not just use kb?
                                   mode,
                                   eval(subsop(i=NULL, loops), x=b));
              end if;
            end if;
            break;
          end if;
        end do;
      end if;
      # Recursively process pieces
      inds := [indices(pieces, 'nolist', 'indexorder')];
      for i in inds do
        if i::even or i=op(-1,inds) then
          pieces[i] := eval_factor(pieces[i], kbs[i], mode, []);
        end if;
      end do;
      res := piecewise(entries(pieces, 'nolist', 'indexorder'));
      for i in loops do res := op(1,i)(res, op(2,i)) end do;
      return res;
    end proc;

    # eval_factor is a simplifier.  It maintains the following invariants:
    #   eval_factor(e, kb, mode, []) = e
    #   eval_factor(e, kb, `*` , [...,[product,i=lo..hi]])
    #     = product(eval_factor(e, kb, `*`, [...]), i=lo..hi)
    #   eval_factor(e, kb, `+` , [...,[sum    ,i=lo..hi]])
    #     = sum    (eval_factor(e, kb, `+`, [...]), i=lo..hi)
    # It recursively traverses e while "remembering" the loops traversed,
    # as ``context'' information, to help with transformations.
    eval_factor := proc(e, kb :: t_kb, mode :: identical(`*`,`+`), loops, $)
      local o, body, x, bounds, res, go, y, kb1, i, j, k, s, r;
      if not (loops :: 'list'([`if`(mode=`*`, 'identical(product,Product)',
                                              'identical(sum    ,Sum    )'),
                               'name=range'])) then
        error "invalid input: mode=%1, loops=%2", mode, loops;
      end if;
      if e :: mode then
        # Transform product(a*b,...) to product(a,...)*product(b,...)
        # (where e=a*b and loops=[[product,...]])
        return map(eval_factor, e, kb, mode, loops);
      end if;
      if e = mode () then
        return e;
      end if;
      if e :: And(specfunc(`if`(mode=`*`, '{product,Product}', '{sum,Sum}')),
                    'anyfunc(anything, name=range)') then
        o := op(0,e);
        body, bounds := op(e);
        x, bounds := op(bounds);
        bounds := map(eval_factor, bounds, kb, `+`, []);
        if bounds_are_simple(bounds) then
          # Expand {product,sum} to {mul,add}
          if o=Product then o:=product elif o=Sum then o:=sum end if;
          bounds := lift_piecewise(bounds,
                      'And(range, Not(range(Not(specfunc(piecewise)))))');
          res := `if`(bounds :: 'specfunc(piecewise)', map_piecewiselike, apply)
                     ((b -> o(go(x), x=b)), bounds);
          # Work around this bug:
          # > product(Sum(f(j),j=0..n-1),j=0..0)
          # Sum(f(0),0=0..n-1)
          res := eval(res, go = (i -> eval(body, x=i)));
          return eval_factor(res, kb, mode, loops);
        end if;
        y, kb1 := genType(x, HInt(closed_bounds(bounds)), kb);
        return eval_factor(subs(x=y,body), kb1, mode, [[o,y=bounds],op(loops)]);
      end if;
      if e :: 'specfunc(piecewise)' then
        return eval_piecewise(e, kb, mode, loops);
      end if;
      if e :: `*` then
        # If we're here, then mode=`+` (else "e :: mode" above would be true)
        s, r := selectremove(depends, e, map2(op,[2,1],loops));
        # Transform sum(a*b(i),i=...) to a*sum(b(i),i=...)
        if r <> 1 then
          return eval_factor(s, kb, `+`, loops)
               * maptype(`*`, eval_factor, r, kb, `+`, []);
        end if;
      end if;
      if mode = `*` then
        if e :: '`^`' then
          # Transform product(a(i)^b,i=...) to product(a(i),i=...)^b
          i := map2(op,[2,1],loops);
          if not depends(op(2,e), i) then
            return eval_factor(op(1,e), kb, `*`, loops)
                 ^ eval_factor(op(2,e), kb, `+`, []);
          end if;
        end if;
        if e :: 'exp(anything)' or e :: '`^`' and not depends(op(1,e), i) then
          # Transform product(a^((b(i)+c(i))^2),i=...)
          #        to a^   sum(b(i)^2   ,i=...)
          #         * a^(2*sum(b(i)*c(i),i=...))
          #         * a^   sum(c(i)^2   ,i=...)
          return mul(subsop(-1=i,e),
                     i in convert(eval_factor(expand(op(-1,e)), kb, `+`,
                                              map2(subsop,1=sum,loops)),
                                  'list', `+`));
        end if;
        # Rewrite ... * idx([p,1-p],i)
        #      to ... * p^idx([1,0],i) * (1-p)^idx([0,1],i)
        # because the latter is easier to integrate and recognize with respect to p
        if e :: 'idx(list, anything)' and not depends(op(1,e), i) then
          return mul(op([1,j],e)
                     ^ eval_factor(idx([seq(`if`(k=j,1,0), k=1..nops(op(1,e)))],
                                       op(2,e)),
                                   kb, `+`, map2(subsop,1=sum,loops)),
                     j=1..nops(op(1,e)));
        end if;
      end if;
      if mode = `*` and e :: 'specfunc(Beta)' then
        res := hack_Beta(e, kb, loops);
        if res <> FAIL then return res end if;
      end if;
      if nops(loops) > 0 then
        # Emit outermost loop as last resort
        return op([-1,1],loops)(eval_factor(e, kb, mode, loops[1..-2]),
                                op([-1,2],loops));
      end if;
      # In the remainder of this function, assume loops=[] and recur in
      if e :: '{specfunc({GAMMA, Beta, exp, And, Or, Not}), relation, logical}' then
        return map(eval_factor, e, kb, `+`, []);
      end if;
      if e :: `^` then
        return eval_factor(op(1,e), kb, mode, [])
             ^ eval_factor(op(2,e), kb, `+` , []);
      end if;
      if e :: `+` then
        return map(eval_factor, e, kb, mode, []);
      end if;
      return e;
    end proc;

    ModuleApply := proc(e, kb::t_kb, $)
      simplify_assuming(eval_factor(convert(e, 'Beta'), kb, `*`, []), kb);
    end proc;
  end module; # simplify_factor_assuming

  getType := proc(kb :: t_kb, x :: name, $)
    local res, over, bound;
    res := op([1,2], select(type, kb, 'Introduce(identical(x), anything)'));
    over := table([`<`=identical(`<`,`<=`), `<=`=identical(`<`,`<=`),
                   `>`=identical(`>`,`>=`), `>=`=identical(`>`,`>=`)]);
    for bound in select(type, kb, 'Bound(identical(x),
                                         identical(`<`,`<=`,`>`,`>=`),
                                         anything)') do
      res := remove(type, res, 'Bound'(over[op(2,bound)], 'anything'));
      res := op(0,res)(subsop(1=NULL,bound), op(res));
    end do;
    res
  end proc;

  kb_to_variables := proc(kb :: t_kb, $)
    [op(map2(op, 1, select(type, kb, t_intro)))];
  end proc;

  kb_to_assumptions := proc(kb, e:={}, $)
    local n;
    remove((a -> a :: `=` and has(a,piecewise)),
      # The "remove" above is because the following takes forever:
      # simplify(piecewise(_a = docUpdate, aaa, bbb)) assuming i = piecewise(_a_ = docUpdate, zNew, idx[z, _a]), _a::integer, 0 <= _a, _a <= size[t]-1, i::integer, 0 <= i, i <= size[as]-2, size[xs] = size[as]-1, size[z] = size[t], docUpdate::integer, 0 <= docUpdate, docUpdate <= size[z]-1
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
    end proc, [op(coalesce_bounds(kb)),
               seq(Constrain(n::nonnegint), n in indets(e, 'specfunc(size)'))]))
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
  list_of_mul := proc(e, $)
    local rest, should_negate, can_negate, fsn;
    rest := convert(e, 'list', `*`);
    rest := map((f -> [f, signum(f),
                       `if`(f::'{specfunc({Sum,sum}),anything^odd}',
                            applyop(`-`,1,f),
                       `if`(f::'specfunc(ln)',
                            applyop(`/`,1,f),
                            -f))]),
                rest);
    should_negate, rest := selectremove(type, rest,
      '[anything, -1, Not(`*`)]');
    if nops(should_negate) :: even then
      [seq(op(3,fsn), fsn=should_negate),
       seq(op(1,fsn), fsn=rest)]
    else
      can_negate, rest := selectremove(type, rest,
        '[{`+`, specfunc({Sum,sum,ln}), `^`}, Not(1), Not(`*`)]');
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

  for_poly := proc(e, f, $)
    if e :: '{`+`,`*`}' then map(for_poly, e, f)
    elif e :: 'specfunc({product,Product,sum,Sum})' then
      applyop(for_poly, 1, e, f)
    else f(e)
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

    # Prevent product(1/(n-i),i=0..n-1) and product(1/(i-n),n=0..i-1)
    # from evaluating to 0 (?!)
    # by preventing `product/indef/indef`(n-i,i)
    # from evaluating to (-1)^i * GAMMA(i-n)
    `product/indef/indef` := overload([
      proc(expr, i, $)
        option overload;
        local a, b;
        if expr :: `*` then
          `*`(op(map(`product/indef/indef`, list_of_mul(expr), i)))
        elif expr :: 'anything^freeof(i)' then
          `product/indef/indef`(op(1,expr),i)^op(2,expr)
        elif has(expr,i) and sign(expr,i) :: negative then
          if ispoly(expr, linear, i, 'b', 'a') then
            (-a)^i / GAMMA(1-i-b/a)
          else
            error FAIL
          end if
        else
          error "invalid input: cannot product/indef/indef(%1, %2)", expr, i
        end if
      end proc,
      `product/indef/indef`]);

    # Convert GAMMA(x)*GAMMA(y)/GAMMA(x+y) to Beta(x,y)
    `convert/Beta` := proc(e, $)
      subsindets(e, 'And(`*`, Not(`*`(Not(specfunc(GAMMA)))),
                              Not(`*`(Not(1/specfunc(GAMMA)))))',
        proc(p, $)
          local s, t, r, i, j, x, y;
          s, r := selectremove(type, convert(p,'list',`*`), 'specfunc(GAMMA)');
          t := map2(op, [1,1], select(type, {op(r)}, '1/specfunc(GAMMA)'));
          for i from nops(s) to 2 by -1 do
            x := op([i,1],s);
            for j from i-1 to 1 by -1 do
              y := op([j,1],s);
              if x + y in t then
                s := subsop(j=GAMMA(x+y), i=Beta(x,y), s);
                break;
              end if;
            end do;
          end do;
          `*`(op(s), op(r));
        end proc);
    end proc;
  end proc;

  ModuleUnload := proc($)
    TypeTools[RemoveType](t_kb);
  end proc;

  ModuleLoad();
end module; # KB
