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
# TODO: decide if this should be kept

# KB, short for knowledge base, is an 'abstract' representation
# of constraints on bound variables. Abstractly, it is a (boolean) conjunction
# of clauses, each of which is of one of the following forms:
#  - Introduce(n::Name,t::HakaruType)
#      introduces a new variable "n : t" which scopes over
#      the 'rest' of the KB (to the right (?))
#  - Let(n::Name,e::Hakaru)
#      introduces a new variable "n" which scopes over the rest
#      of the KB whose value is precisely "e"
#  - Constrain(c::Constraint) where
#      where Constraint is essentially a boolean-valued expression
#      on Hakaru terms, containing equalities, inequalities,
#      and boolean algebra on such
KB := module ()
  option package;
  local
     # The 'constructors' of a KB, which should not be used externally to the module
     KB, Introduce, Let, Constrain,

     # Some sort of hideous hack to get built-in maple
     # functions (assuming,eval,is...) to work with
     # Hakaru types
     chilled, chill, warm,

     ModuleLoad, ModuleUnload,

     # Various utilities
     t_intro, t_lo, t_hi, log_metric,
     boolean_if, coalesce_bounds, htype_to_property,
     negate_kb1 , `&assuming_safe`, from_FAIL
     ;
  export
     # Functions which build up KBs from KBs and other pieces
     #  typically ensuring that internal invariants are upheld
     # (i.e. 'smart' constructors)
      empty, genLebesgue, genType, genLet, assert, assert_deny,

     # Negation of 'Constrain' atoms, that is, equality and
     # inequality constraints
     negated_relation, negate_relation,

     # "kb0 - kb1" - that is, kb0 without the knowledge of kb1
     kb_subtract,

     # Simplify a Hakaru term assuming the knowledge of the kb
     simplify_assuming,

     # Like above, but also applies `hack_Beta` and `eval_factor`
     # which helps some things simplify.
     simplify_factor_assuming,

     # Gets the most refined (see refine_given) type of a given name under the
     # assumptions of the KB
     getType,

     # Various 'views' of the KB, in that they take a KB and produce something
     # which is somehow 'representative' of the KB
     kb_to_variables, kb_to_assumptions, kb_to_equations, kb_piecewise,

     # Various utilities ...
     list_of_mul, for_poly, range_of_HInt,

     # Types corresponding to the constructor forms of the 'atoms' of KBs
     t_kb_Introduce, t_kb_Let, t_kb_Bound, t_kb_Constrain;
  global
     # The type of KBs. It is 'assumed' that things 'with this type'
     # are actually KBs in the proper form
     t_kb,

     # Some silly things that KB must do to appease
     # Maple when using Maple functions to work with
     # Hakaru 'terms'.
     `expand/product`, `simplify/int/simplify`,
     `product/indef/indef`, `convert/Beta`;
  uses Hakaru;

  # Some types
  # A particular form of Introduce.. (?)
  t_intro := 'Introduce(name, specfunc({AlmostEveryReal,HReal,HInt}))';

  # Low and high bounds (?)
  t_lo    := 'identical(`>`,`>=`)';
  t_hi    := 'identical(`<`,`<=`)';

  # The 'constructor' forms of KB
  t_kb_Introduce := 'Introduce(name, anything)';
  t_kb_Let       := 'Let(name, anything)';
  t_kb_Bound     := 'Bound(name, anything, anything)';
  t_kb_Constrain := 'Constrain(anything)';

  # The empty KB means "true".
  empty := KB();

  # A smart constructor for introducing Lebesgue integration variables (?)
  #   genLebesgue(var,lo,hi,kb) =
  #     "KB(Introduce(x::AlmostEveryReal(x>lo,x<hi))
  #        ,kb)"
  genLebesgue := proc(xx::name, lo, hi, kb::t_kb)
    # The value of a variable created using genLebesgue is respected only up to
    # negligible changes
    genType(xx, AlmostEveryReal(Bound(`>`,lo), Bound(`<`,hi)), kb, _rest)
  end proc;

  # A smart constructor for type introductions. ensures name binding
  # is done correctly.
  #   genType(var,type,kb) =
  #     "KB(Introduce(x::type),kb)"
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

  # A smart constructor for 'let' introductions. ensures name binding
  # is done correctly.
  #   genLet(var,expr,kb) =
  #     "KB(Let(var=expr),kb)"
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


  # Negate b, where b is an 'atomic' relation of a KB (?)
  # TODO: this should make use of `negated_relation'
  negate_kb1 := proc(b,$)
     if   b :: `=`  then `<>`(op(b))
     elif b :: `<>` then `=` (op(b))
     elif b :: `<`  then `>=`(op(b))
     elif b :: `<=` then `>` (op(b))
     else Not(b) end if
  end proc;

  # Perhaps this exists somewhere
  from_FAIL := proc(e,def,$) if not e::identical(FAIL) then def else e end if; end proc;


  # Catches and reports a contradiction which could arise as result of
  # some forms of simplification and evaluation
  `&assuming_safe` := proc (e :: uneval)
     try
        e assuming args[2 .. -1];
     catch "when calling '%1'. Received: 'contradictory assumptions'":
        # We seem to be on an unreachable control path
        userinfo(1, 'procname', "Received contradictory assumptions.");
        FAIL;
     end try;
  end proc;

  # Like assert_deny, except does not accept a boolean
  # parameter to indicate negation, and evaluates
  # (using Maple's eval, anything can happen!) the
  # new conjunct under the derived knowledge of the KB
  assert := proc(b, kb::t_kb, $)
    assert_deny(foldl(eval, b, op(kb_to_equations(kb))), true, kb)
  end proc;

  # Implements the assert_deny function, which inserts either
  # a constraint or its negation into a KB, essentially, a
  # 'smart constructor'.
  assert_deny := module ()
   export ModuleApply ;
   local t_if_and_or_of, t_not, t_not_eq_and_not_not, bound_simp, not_bound_simp,
         refine_given, t_bound_on;

   # The 'type' of `if(,,)` where the first parameter is the given type
   t_if_and_or_of := proc(pol,$)
       `if`(pol, '{specfunc(anything, And), `and`}', '{specfunc(anything, Or ), `or` }')
   end proc;

   # The 'type' of `not(..)` statements
   t_not := '{specfunc(anything, Not), `not`}';

   # The type representing equalities
   # between something which is neither a name nor 'size' applied to a name
   # and another thing which is a name which is neither constant nor undefined
   t_constraint_flipped := 'Not({name, size(name)}) = And(name, Not(constant), Not(undefined))';

   # The 'type' representing bounds on `x', where `x' is a name
   t_bound_on := proc(x,$) And(relation, Or(anyop(identical(x), freeof(x)), anyop(freeof(x), identical(x)))) end proc;

   # Given (TODO: add these types to the function(?))
   #   k  :: HakaruType
   #   kb :: t_kb
   #   x  :: name
   #   c  :: type
   # a bound name "x" of type "k", produces a 'refinement' of the
   # type "k", which is a type more specific than "k" at which
   # the name "x" is well-typed given the knowledge in the KB,
   # i.e. the conjunction of "x :: $result" with "kb" gives
   # "x :: k" inside the KB
   #
   # Note that if the list is non-empty, the refined knowledge
   #   is given by the first element of the list, and if it
   #   is empty, no refinement is possible.
   #
   # Original enlightenment:
   #   hakaru-dev/hakaru/commit/02b9335669e00921a57c3d2a65a1f5f9f6162aa4
   refine_given := proc(k,kb,x,c,$)
       [ op(map2(subsop
                , 1=NULL
                , select(type, kb, Bound(identical(x), c, anything))
                )
           )
       , op(select(type, k , Bound(              c, anything)) )
       ]
   end proc;

   # Performs simplification(?) in case something of the form `t_bound_on` is
   # found
   # This function signals it has failed to find a result with `FAIL`
   bound_simp := proc(b,x,k,kb,pol,as,e0,$)
      local e, rel, c, kb1,ch;
      e = e0;
      # b is a bound on x, so compare it against the current bound on x.
      # First, express `if`(pol,b,Not(b)) as rel(x,e)
      rel := op(0,b);

      # Account for the symmetric cases of `x' being on the left or right
      # hand side; the predicate is modified(?) in case of a 'flip'
      if x = lhs(b) then
        e := rhs(b);
      else #x=rhs(b)
        e   := lhs(b);
        rel := subs({`<`=`>`, `<=`=`>=`}, rel);
      end if;

      # Change relations to their negations if `pol = false'
      if not pol then
        # A 'table' giving the negations of relations
        rel := subs({`<`=`>=`, `<=`=`>`, `>`=`<=`, `>=`=`<`, `=`=`<>`, `<>`=`=`}, rel);
      end if;

      # Discards a few points (?)
      if k :: 'specfunc(AlmostEveryReal)' then
        # A 'table' giving the negation of strict relations
        rel := subs({`<=`=`<`, `>=`=`>`}, rel);
      end if;

      if rel = `=` then
        # To assert that x=e, it's not enough to supersede the Introduce
        # binding for x with a Let binding.
        kb1 := KB(Bound(x,`=`,e), op(kb));
        # We also need to assert that e is in bounds for x.
        for c in t_lo, t_hi do
          c := refine_given(k,kb,x,c);
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
      c := refine_given(k,kb,x,c);

      # chill but also unwraps `c' (?)
      if nops(c) > 0 then c := chill(op(1,c)) end if;

      # Compare the new bound rel        (x,e          )
      # against the old bound op([1,1],c)(x,op([1,2],c))
      if e = `if`(rel :: t_lo, -infinity, infinity)
          or nops(c)>0 and (is(rel(y,ch)) &assuming_safe
                              (op(1,c)(y,op(2,c)),
                               y::htype_to_property(k), op(as)) ) then
          # The old bound renders the new bound superfluous.
          return kb

      # "assuming" used to be in a try which would
      # cause the return to never be reached if it threw, but now it
      # produces FAIL instead - and `_x or FAIL = FAIL'
      elif nops(c)=0 or (is(op(1,c)(y,op(2,c))) &assuming_safe
                             (rel(y,ch),
                              y::htype_to_property(k), op(as)) ) then
          # The new bound supersedes the old bound.
          return KB(Bound(x,rel,e), op(kb))
      end if;

      FAIL; # No simplification could be done
   end proc;

   # Simplification when the `:: t_bound_on' predicate is false
   not_bound_simp := proc(b,x,kb,pol,as,$)
     local c;

     c := solve({b},[x], 'useassumptions'=true) assuming op(as);
     # success!
     if c::list and nops(c)=1 and nops(c[1])=1 then
       assert_deny(c[1][1], pol, kb);
     else
       FAIL; # No simplification could be done
     end if;
   end proc;

   # Given a constraint "bb" on a KB "kb", this
   #   inserts either "bb" (if "pol" is true) or "Not bb" (otherwise)
   #   or, KB(Constrain(`if`(pol,bb,Not(bb))), kb)
   # Great deal of magic happens behind the scenes
   ModuleApply := proc(bb, pol::identical(true,false), kb::t_kb, $)
    # Add `if`(pol,bb,Not(bb)) to kb and return the resulting KB.
    local as, b, log_b, k, x, rel, e, ch, c, kb0, kb1, y, ret;

    if bb = pol then
      # Ignore literal true and Not(false).
      kb

    elif bb :: t_if_and_or_of(pol) then
      foldr(((b,kb) -> assert_deny(b, pol, kb)), kb, op(bb))

    elif bb :: t_not then
      foldr(((b,kb) -> assert_deny(b, not pol, kb)), kb, op(bb))

    else
      # Setup the assumptions
      as := chill(kb_to_assumptions(kb, bb));

      # Simplify `bb' in context `as' placing result in `b'
      b := chill(bb);
      b := from_FAIL( simplify(b) &assuming_safe op(as) , b );
      b := warm(b);

      # Look through kb for the innermost scope where b makes sense.
      k := select((k -> k :: Introduce(name, anything) and depends(b, op(1,k))),
                  kb);

      # If that scope is not precisely the trivial KB, then ..
      if nops(k) > 0 then
        x, k := op(op(1,k));
        # Found the innermost scope where b makes sense.
        # Reduce (in)equality between exp(A) and exp(B) to between A and B.
        do
          try log_b := map(simplify@ln, b) assuming op(as); catch: break; end try;

          # assuming_safe doesn't work here
          # log_b := map(simplify@ln, b) &assuming_safe op(as);
          # if log_b :: identical(FAIL) then break; end if;

          if log_metric(log_b, x) < log_metric(b, x)
             and (andmap(e->is(e,real)=true, log_b) assuming op(as)) then
            b := log_b;
          else
            break;
          end if;
        end do;

        # If `b' is of a particular form (a bound on `x'), simplification
        # is in order
        if b :: t_bound_on(`x`) then
          kb0 := bound_simp(b,x,k,kb,pol,as,e);
        else
          kb0 := not_bound_simp(b,x,kb,pol,as);
        end if;

        # If it succeeds, return that result
        if not kb0 :: identical(FAIL) then return kb0 end if;
      end if;

      # Normalize `=` and `<>` constraints a bit.
      if not pol then
        b := negate_kb1(b);
      end if;

      # If the name in the simple equality (if it is such) is not
      # on the lhs, then flip the equality
      if b :: t_constraint_flipped then b := (rhs(b)=lhs(b)) end if;

      # If `b' reduces to `true' in the KB environment then there is no need to
      # add it
      ch := chill(b);
      if is(ch) &assuming_safe op(as) then return kb end if;

      # Add constraint to KB.
      KB(Constrain(b), op(kb))
    end if

   end proc: # ModuleApply
  end module; # assert_deny

  # In order to hopefully produce a simplification,
  #   assert_deny will on some occasions repeatedly apply
  #   `simplify@ln` in the hopes of producing an 'improved'
  #   constraint. This metric gives the stopping condition
  # - when the simplification ceases to improve the constraint
  # - which is when the metric is made no less by the `simplify@ln`.
  # Since this is a `length`, this is strictly decreasing,
  #  so such a loop will 'provably' always terminate
  log_metric := proc(e, x, $)
    local m, L;
    m := select(depends, indets(e, 'exp(anything)'), x);
    length(subsindets(map2(op, 1, m), name, _->L));
  end proc:

  # boolean_if should be equivalent to `if`, but it assumes
  # all its arguments are boolean conditions, so it basically
  # simplifies "cond and th or not cond and el"
  boolean_if := proc(cond, th, el, $)
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

  # Given that kb is an extension of kb0
  # (in that all the knowledge in kb0 is contained in kb)
  # then produces kb 'without' kb0.
  # Essentially this just applies coalesce_bounds
  # and then folds over the kb, at each step producing
  # a 'valid' KB by applying the smart constructor
  # (?) What is the role of of coalesce_bounds? why is it necessary?
  kb_subtract := proc(kb::t_kb, kb0::t_kb, $)
    local cut;
    cut := nops(kb) - nops(kb0);
    if cut < 0 or KB(op(cut+1..-1, kb)) <> kb0 then
      error "%1 is not an extension of %2", kb, kb0;
    end if;
    map(proc(k, $)
      local x, t;
      if k :: t_kb_Introduce then
        x, t := op(k);
        if t :: 'specfunc(AlmostEveryReal)' then
          t := [op(t), Bound(`>`, -infinity), Bound(`<`, infinity)];
          [genLebesgue, x,
           op([1,2], select(type, t, Bound(identical(`>`), anything))),
           op([1,2], select(type, t, Bound(identical(`<`), anything)))]
        else
          [genType, x, t]
        end if
      elif k :: t_kb_Let then
        [genLet, op(k)]
      elif k :: t_kb_Bound then
        [assert, op(2,k)(op(1,k),op(3,k))]
      elif k :: t_kb_Constrain then
        [assert, op(1,k)]
      end if
    end proc, [op(coalesce_bounds(KB(op(1..cut, kb))))])
  end proc;

  # This essentially extracts all of the `Bound`s from a
  # KB and then re-inserts them 'directly' by applying their
  # knowledge to the rest of the KB. This may (?) produce
  # an invalid KB
  coalesce_bounds := proc(kb::t_kb, $)
    local lo, hi, eq, rest, k, x, t, b, s, r;

    # For every introduction in kb, remove bounds from
    # the introduction and store them seperately
    #  rest   maps variables to the stripped type
    #  lo,hi  map variables to low,high bounds
    for k in select(type, kb, t_intro) do
      x, t := op(k); # "x = t" is the intro

      # t := minus the lower,upper bounds in t
      b, t := selectremove(type, t, Bound(t_lo, anything));
      if nops(b) > 0 then lo[x] := op(1,b) end if;
      b, t := selectremove(type, t, Bound(t_hi, anything));
      if nops(b) > 0 then hi[x] := op(1,b) end if;
      rest[x] := [op(t)];
    end do;

    # Extract equality bounds, stored in eq (again a map from names)
    for k in select(type, kb, Bound(name, identical(`=`), anything)) do
      eq[op(1,k)] := op(3,k);
    end do;

    # Select `Bound`s in `Constrain`s, i.e. bounds on bound variables
    for k in select(type, kb, Bound(name, t_lo, anything)) do
      lo[op(1,k)] := subsop(1=NULL,k);
    end do;
    for k in select(type, kb, Bound(name, t_hi, anything)) do
      hi[op(1,k)] := subsop(1=NULL,k);
    end do;

    # 'coalesce' the bounds back into each clause of the KB
    map(proc(k, $)
      # when the clause is an introduction
      #  and there are equations on "x" which all evaluate to "a = a"
      #  remove that introduction and substitute
      #  bounds information about "x" back into things about "x"
      if k :: t_intro then
        x := op(1,k);
        if eq[x] = evaln(eq[x]) then
          subsop(2=op([2,0],k)(op(select(type, [lo[x],hi[x]], specfunc(Bound))),
                               op(rest[x])),
                 k);
        else
      #  otherwise, just replace the intro with a Let
          Let(x, eq[x]);
        end if

      # When the clause is a bound, erase it
      elif k :: t_kb_Bound
           and rest[op(1,k)] :: 'list' then
        NULL;

      # otherwise, do nothing
      else
        k;
      end if;
    end proc, kb);
  end proc;

  # Simplfies a given Hakaru term under knowledge of the
  # given KB. Does some magic to appease the Maple simplifier.
  simplify_assuming := proc(ee, kb::t_kb, $)
    local e, as, e0;                                                         # for debugging
    if not (indets(ee,'specfunc(applyintegrand)') = {}) then
      WARNING("simplify_assuming called on an expression containing 'applyintegrand' -- this is probably a mistake, and could result in incorrect results");
    end if;
    e := foldl(eval, ee, op(kb_to_equations(kb)));                         `eval`;
    as := kb_to_assumptions(kb, e);
    e := chill(e);                                                        `chill`;
    as := chill(as);

    e0 := e;
    e := simplify(e) &assuming_safe op(as);
    if e :: identical(FAIL) then e := e0 end if;

    # This causes an additional test to fail compared to the above .. either
    # from_FAIL is wrong or simplify is somehow (for some reason?!)  mutating
    # `e' (?)
    # e := from_FAIL( simplify(e) &assuming_safe op(as), e );

    e := warm(e);                                            `warm (then expand@exp)`;
    eval(e, exp = expand @ exp);
  end proc;

  # Like simplify_assuming, but does a lot of hack-y things
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
      elif k :: t_kb_Let then
        `=`(op(k))
      elif k :: t_kb_Bound then
        op(2,k)(op(1,k), op(3,k))
      elif k :: t_kb_Constrain then
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

    lets := map2(subsop, 0=`=`, [op(select(type, kb, t_kb_Let))]);
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

  # Given an expression containing products and sums, i.e. polynomials
  # and a function , applies this expression to each factor and summand
  for_poly := proc(e, f, $)
    if e :: '{`+`,`*`}' then map(for_poly, e, f)
    elif e :: 'specfunc({product,Product,sum,Sum})' then
      applyop(for_poly, 1, e, f)
    else f(e)
    end if
  end proc;

  # Computes the range of (possible values of) a Hakaru Int,
  # given a Hakaru type for that Int
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
