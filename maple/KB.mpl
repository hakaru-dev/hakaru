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

     # Experimental KB which allows one 'level' of a KB to be a partition along
     # a particular dimension/variable.  Under that split, what is below are other
     # layers of SplitKB.  A KB is a degenerate case of a KB with no split.
     SplitKB,

     # Some sort of hideous hack to get built-in maple
     # functions (assuming,eval,is...) to work with
     # Hakaru types
     chilled, chill, warm,

     ModuleLoad, ModuleUnload,

     # Various utilities
     t_intro, t_lo, t_hi, log_metric,
     boolean_if, coalesce_bounds, htype_to_property

     ;
  export
     # Functions which build up KBs from KBs and other pieces
     #  typically ensuring that internal invariants are upheld
     # (i.e. 'smart' constructors)
      empty, genLebesgue, genType, genLet, assert, assert_deny, build_kb,

     # Negation of 'Constrain' atoms, that is, equality and
     # inequality constraints
     negated_relation, negate_rel,

     # "kb0 - kb1" - that is, kb0 without the knowledge of kb1
     kb_subtract,

     # kb_entails(kb,cond) = "kb => cond"
     kb_entails,

     # Normalize a kb to take advantage of all of
     # the information in it.  Warning: this can completely
     # re-arrange things, so that it is no longer valid to call
     # kb_substract after this operation is performed.
     # In particular, the result may be a SplitKB.
     kb_extract,

     # Like SolveTools.LinearMultivariateSolve, but for KB
     kb_LMS,

     # Simplify a Hakaru term assuming the knowledge of the kb
     # variants do different things in case of simplification error
     # (which should really only occur when the KB contains a contradicition)
     simplify_assuming, simplify_assuming_mb, simplify_assuming_f,

     # Gets the most refined (see refine_given) type of a given name under the
     # assumptions of the KB; & convert such a type to a range.
     getType, kb_range_of_var,

     # Various 'views' of the KB, in that they take a KB and produce something
     # which is somehow 'representative' of the KB
     kb_to_variables, kb_to_assumptions, kb_to_equations, kb_piecewise, kb_Partition,

     # Various utilities ...
     list_of_mul, for_poly, range_of_HInt, eval_kb, kb_is_false,

     # Types corresponding to the constructor forms of the 'atoms' of KBs
     t_kb_Introduce, t_kb_Let, t_kb_Bound, t_kb_Constrain;
  global
     # The type of KBs. It is 'assumed' that things 'with this type'
     # are actually KBs in the proper form
     t_kb, t_kb_atom, t_kb_atoms,

     # Things which should produce a KB, but sometimes don't return this
     # expression
     NotAKB,

     # kb_LMS produces NoSol when it doesn't find a solution.
     NoSol,

     # Some silly things that KB must do to appease
     # Maple when using Maple functions to work with
     # Hakaru 'terms'.
     `expand/product`, `simplify/int/simplify`,
     `product/indef/indef`, `convert/Beta`;
  uses Hakaru, SolveTools:-Inequality ;

  # Some types
  # A particular form of Introduce, containing those types
  # about which Maple currently knows
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

  # The false KB
  NotAKB := proc($)
      'procname'()
  end proc;

  # Check if a kb which might be NotAKB is indeed NotAKB
  kb_is_false := proc(mbkb :: t_kb_mb, $) evalb(mbkb :: t_not_a_kb) end proc;

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
  negated_relation:= table([`<`, `<=`, `=`, `<>`] =~ [`>=`, `>`, `<>`, `=`]);

  # Takes the bool type (true/false) to mean universal and empty relations respectively.
  # i.e. negate R, where R is an 'atomic' relation of a KB
  negate_rel:= proc(R::t_kb_atom, $)::t_kb_atom;
      if R :: truefalse then
        not R
      elif R :: relation then
          negated_relation[op(0,R)](op(R));
      else
          # This is to appease 'piecewise', which won't be happy with Not
          # However, KB doesn't really care - it's already expecting {Not,not}
          # 'Technically' this is a KB 'constructor'!
          not(R);
      end if;
  end proc;

  # Builds a kb from a list of atoms - simply foldr(assert,empty,as) except
  # and extra check is (optionally) done for the resulting KB to be valid.
  build_kb := proc(as::t_kb_atoms, shouldBeValid::{identical(false),string} := false, $)
      local
      kb := foldr(assert,empty, op(as));
      if shouldBeValid :: string then
          ASSERT(type(kb,t_kb), sprintf("%s (in build_kb): KB contains a contradiction.", shouldBeValid));
      end if;
      kb
  end proc;

  # Like assert_deny, except does not accept a boolean
  # parameter to indicate negation, and evaluates
  # (using Maple's eval, anything can happen!) the
  # new conjunct under the derived knowledge of the KB
  assert := proc(b::t_kb_atom, kb::t_kb, $)
    assert_deny(foldl(eval, b, op(kb_to_equations(kb))), true, kb)
  end proc;

  # Implements the assert_deny function, which inserts either
  # a constraint or its negation into a KB, essentially, a
  # 'smart constructor'.
  # Also implements a second way to call it, 'part', which will
  # return a SplitKB instead.
  assert_deny := module ()
   export ModuleApply;
   local t_if_and_or_of, t_not, t_constraint_flipped, bound_simp, not_bound_simp,
         refine_given, t_bound_on, simplify_in_context;

   # Either And or Or type, chosen by boolean pol
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
   bound_simp := proc(b,x,k,kb,pol,as,$)
      local e, rel, c, kb1,ch;
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

      # Make inequalities loose over Real
      # Warning: other code relies on this!!!
      if k :: 'specfunc(AlmostEveryReal)' then
        # A 'table' giving the relaxation of strict relations
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
          or nops(c)>0 and (is(rel(y,ch)) assuming
                              (op(1,c)(y,op(2,c)),
                               y::htype_to_property(k), op(as)) ) then
          # The old bound renders the new bound superfluous.
          return kb

      # "assuming" used to be in a try which would
      # cause the return to never be reached if it threw, but now it
      # produces FAIL instead - and `_x or FAIL = FAIL'
      elif nops(c)=0 or (is(op(1,c)(y,op(2,c))) assuming
                             (rel(y,ch),
                              y::htype_to_property(k), op(as)) ) then
          # The new bound supersedes the old bound.
          return KB(Bound(x,rel,e), op(kb))
      end if;

      FAIL; # No simplification could be done
   end proc;

   # Simplification when the `:: t_bound_on' predicate is false
   # note: k is ignored, but this makes the API the same as
   # bound_simp
   not_bound_simp := proc(b,x,k,kb,pol,as,$)
     local c;

     c := solve({b},[x], 'useassumptions'=true) assuming op(as);
     # success!
     if c::list and nops(c)=1 then
       foldr(((z,kb)->assert_deny(z, pol, kb)), kb, op(c[1]));
     else
       FAIL; # No simplification could be done
     end if;
   end proc;

   # Simplify `bb' in context `as'
   simplify_in_context := proc(bb, as, $)
     local b;
     b := chill(bb);
     b := simplify(b) assuming op(as);
     warm(b);
   end proc;

   # Given a constraint "bb" on a KB "kb", this
   #   inserts either "bb" (if "pol" is true) or "Not bb" (otherwise)
   #   or, KB(Constrain(`if`(pol,bb,Not(bb))), kb)
   # Great deal of magic happens behind the scenes
   ModuleApply := proc(bb::t_kb_atom, pol::identical(true,false), kb::t_kb, $)
    # Add `if`(pol,bb,Not(bb)) to kb and return the resulting KB.
    local as, b, log_b, k, x, rel, e, ch, c, kb0, kb1, y, ret, todo;

    # Setup the assumptions
    as := chill(kb_to_assumptions(kb, bb));

    # Check that the new clause would not cause a contradictory
    # KB. If it does, then produce NotAKB.
    if not coulditbe(`if`(pol,bb,not(bb))) assuming op(as) then
        return NotAKB();
    end if;

    if bb = pol then
      # Ignore literal true and Not(false).
      kb

    elif bb :: t_if_and_or_of(pol) then
      foldr(((b,kb) -> assert_deny(b, pol, kb)), kb, op(bb))

    elif bb :: t_not then
      foldr(((b,kb) -> assert_deny(b, not pol, kb)), kb, op(bb))

    else
      b := simplify_in_context(bb, as);

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

          if log_metric(log_b, x) < log_metric(b, x)
             and (andmap(e->is(e,real)=true, log_b) assuming op(as)) then
            b := log_b;
          else
            break;
          end if;
        end do;

        # syntactic adjustment
        # If `b' is of a particular form (a bound on `x'), simplification
        # is in order
        todo := `if`(b :: t_bound_on(`x`), bound_simp, not_bound_simp);
        kb0 := todo(b,x,k,kb,pol,as);

        # If it succeeds, return that result
        if not kb0 :: identical(FAIL) then return kb0 end if;
      end if;

      # Normalize `=` and `<>` constraints a bit.
      if not pol then
        b := negate_rel(b);
      end if;

      # If the name in the simple equality (if it is such) is not
      # on the lhs, then flip the equality
      if b :: t_constraint_flipped then b := (rhs(b)=lhs(b)) end if;

      # If `b' reduces to `true' in the KB environment then there is no need to
      # add it
      ch := chill(b);
      if is(ch) assuming op(as) then return kb end if;

      # Add constraint to KB.
      KB(Constrain(b), op(kb))
    end if;
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

  # checks that the given condition is fully contained in the given KB,
  # or that `kb => cond'
  kb_entails := proc(kb::t_kb, cond,$)
      local kb0;
      # nothing implies false (other than false, but kb is not false)
      if cond :: t_not_a_kb then
          false
      # if the condition is a kb, subtract from it directly
      elif cond :: t_kb then
          nops(kb_subtract(cond, kb)) = 0
      else # if the condition is an atom, check that asserting it has
           # no effect on the KB
          kb0 := assert(cond,kb);
          if kb0 :: t_kb then
              nops(kb_subtract(kb0,kb)) = 0
          else
              false
          end if;
      end if;
  end proc;

  # the range ("x..y") of a type as produced by `getType'
  # very much partial, but should probably at some point be unified
  # with getType (in the form of an optional param to getType?)
  kb_range_of_var :=
    proc( v, $)
      local lo, hi, lo_b, hi_b, k ;

      if v :: 'specfunc(AlmostEveryReal)' then
          k := nops(v);
          lo_b, hi_b := -infinity, infinity;

          if k = 0 then
              # do nothing

          elif k = 2 then
              lo, hi := op(v);
              lo, lo_b := op(1,lo), op(2, lo);
              hi, hi_b := op(1,hi), op(2, hi);

          elif k = 1 then
              if op([1,1],v) in {`<`, `<=`} then
                  hi_b := op([1,2], v);
              elif op([1,1],v) in {`>`, `>=`} then
                  lo_b := op([1,2], v);
              else
                  error "kb_bounds_of_var: unknown bound %a", op([1,1],v);
              end if;

          end if;
          return lo_b .. hi_b;

      end if;

      error "kb_bounds_of_var: unknown type %a", v;

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

  # Extracts information about the KB in a format suitable for manipulation
  # with standard Maple library functions, which do not typically expect to
  # find Hakaru constructors in their input
  kb_extract := proc(kb::t_kb, $)::[anything, anything, list(t_kb_atom)];
    local vars, parms, constraints;

    # Select all of the relevant subparts
    vars        := select(type, kb, 'Introduce(name, specfunc(AlmostEveryReal))');
    parms       := select(type, kb, 'Introduce(name, specfunc({HReal,HInt}))');
    # constraints := select(type, kb, 'Constrain(relation)');

    # A lot of interesting things will happen here, but maybe they
    # should happen as a 'pre-processing' step inside of kb_LMS

    # get rid of "x::t", in which t is going to be {real,integer}.
    # LMS assumes real implicitly, but it could give entirely bogus
    # solutions if the type is really integer

    # furthermore, kb_to_assumptions is not quite the right thing
    #  here, as it will produce an empty list for e.g.
    #     KB(KB:-Introduce(`x`,AlmostEveryReal()))
    #  but LMS can't do anything with that empty list.

    #  We (maybe?) want to 'trick' LMS here, e.g. if a var "x" occurs in
    #  "vars" but has no constraints (and the constraints are otherwise empty),
    #  just add "x = x" to the constraints, which LMS happily solves to
    #  "x" .
    constraints := remove(type, kb_to_assumptions(kb), `::`);

    [vars, parms, constraints];

  end proc;

  # linear multivariate system solver for KB
  kb_LMS := proc(kb::t_kb, $)
      local vs, vsr, ps, cs, ret;

      vsr, ps, cs := op(kb_extract(kb));

      userinfo(3, 'LMS',
        printf("    LMS extract:\n"
               "      vars     : %a\n"
               "      parms    : %a\n"
               "      cxts     : %a\n"
         , vsr, ps, cs ));

      # extract the data:
      #  from inside of KB,
      #  from inside of KB atom constructors (Constrain, Intro)
      vs, ps := op(map(z -> map[2](op, 1, [op(z)]), [vsr,ps]));

      cs := {op(cs)}:

      userinfo(3, 'LMS',
        printf("      vars2s   : %a\n"
               "      cxts2s   : %a\n"
         , vs, cs ));

      # there are variables to solve for, but no non-trivial
      # constraints which need to be solved.
      if cs = {} and not vs = [] then
        # this matches the output format of LMS; [x,y] -> { [ {true}, {true} ] }
        ret := { map(o->{true}, vs) };

      elif not cs = {} and vs = [] then
        ret := NoSol("There are no variables to solve for, but there are constraints."
                     " This means the variables have not been correctly identified.");

      elif cs = {} and vs = [] then
        ret := NoSol("Something went very wrong");

      else
        try
          ret := LinearMultivariateSystem( cs, vs );
        catch "the system must be linear in %1":
          ret := NoSol(sprintf("The system (%a) must be linear in %a."
                               , cs, vs ));

        catch "inequality must be linear in %1":
          ret := NoSol(sprintf("The system (%a) contains nonlinear inequality in "
                               "one of %a."
                               , cs, vs ));
        end try;

      end if;

      if ret::specfunc('NoSol') then return ret end if;

      userinfo(3, 'LMS',
        printf("      ret     : %a\n"
         , ret ));

      # get rid of any clauses which are already in the context.
      # the result might be a piecewise (so conditions apply conditionally)
      # but the given context applies unconditionally
      # ret := subsindets(ret, set,
      #   p -> remove(x->
      #     (x::{boolean,relation} and evalb(x in cs)) or
      #     (x::name and evalb(x in vs))
      #     ,p)
      #   );

      # userinfo(3, 'LMS',
      #   printf("      ret     : %a\n"
      #    , ret ));

      # the above might trivialize some solutions. simplify
      #   - empty solutions
      #   - singleton (sub)solutions
      # ret := subsindets(ret, list, s->remove(c->c::identical({}),s));

      # userinfo(3, 'LMS',
      #   printf("      ret     : %a\n"
      #    , ret ));

      # ret := subsindets(ret, set, s->`if`(nops(s)=1,op(1,s),s));

      # userinfo(3, 'LMS',
      #   printf("      ret     : %a\n"
      #    , ret ));

      # try to get rid of some 'bad' solutions
      # those which contain variables on both right and left hand sides
      # hopefully this isn't too aggressive, that is, it does not delete
      # a solution by reducing it to zero clauses, and hopefully it
      # produces a single solution (for every branch of a potential piecewise)
      # ret := subsindets(ret, set, proc(s)
      #         local rem;
      #         if nops(s)>1 then
      #            rem :=
      #             remove(z-> not(`or`(seq(
      #              c :: relation and depends(lhs(c),vs)
      #                            and depends(rhs(c),vs)
      #             ,c=op(z)
      #                               )
      #                           ))
      #                  , s );
      #             if nops(rem) = 1 then op(1,rem) else s end if;
      #         else s end if; end proc
      #        );


      # replace single variables in the 'solution' (which should be a boolean
      # valued expression, which a name really is not) with 'true'
      ret := subsindets(ret, set, s-> map(c->`if`(c::name,true,c),s));

      # remove the otherwise clause if it is empty (outside the domain, which is
      # going to be reprsented in the kb and "cs" anyways)
      # ret := `if`(ret :: specfunc('piecewise') and nops(ret) :: odd and
      #             op(ret)[-1] :: identical({})
      #            ,piecewise(op(ret)[1..-2])
      #            ,ret);

      # TODO: postprocessing on the output
      #   in particular, if LMS produces a piecewise,
      #    - we probably want it to be a partition
      #    - it may contain cases which we can simply throw away
      #       ("var = val" for var : almost every real)
      #    - it may contain cases which are redundant, i.e.
      #        with pw(var=val, e0, ..), simplifying e0 under "var=val"
      #        produces an expression identical to another one of the pieces

      [ ret, vsr, ps ];
  end proc;


  eval_kb := proc(e,kb::t_kb, $)
    foldl(eval, e, op(kb_to_equations(kb)));
  end proc;

  # Simplfies a given Hakaru term under knowledge of the
  # given KB. Does some magic to appease the Maple simplifier.
  # simplification might fail, in which case `failure(e)` where `e`
  # is the un-simplified (and chilled) expression is taken to be the result of
  # simplification. 'mb' for 'maybe'
  simplify_assuming_mb := proc(ee, kb::t_kb, failure, $)
    local e, as, e0;                                                         # for debugging
    if not (indets(ee,'specfunc(applyintegrand)') = {}) then
      WARNING("simplify_assuming called on an expression containing 'applyintegrand' -- this is probably a mistake, and could result in incorrect results");
    end if;
    e := eval_kb(ee,kb);                                                  `eval`;
    as := kb_to_assumptions(kb, e);
    e := chill(e);                                                        `chill`;
    as := chill(as);

    # The assumptions may be contradictory - I'm not sure why the right thing to
    # do is to return the original expression. Assuming false one can derive
    # anything - hence exception - so who calls this function under which
    # contexts that they expect `false` to mean something other than `false`?
    e0 := e;
    try e := simplify(e) assuming op(as); catch: e := failure(e0); end try;

    e := warm(e);                                            `warm (then expand@exp)`;
    eval(e, exp = expand @ exp);
  end proc;

  simplify_assuming := proc(ee, kb::t_kb, $)
    simplify_assuming_mb(ee,kb,e->e);
  end proc;

  # like simplify_assuming but propgates the failure (as FAIL) instead of
  # silently consuming it and returning the unsimplified expression.  'f' for
  # 'failure'
  simplify_assuming_f := proc(ee, kb::t_kb, $)
    simplify_assuming_mb(ee,kb,e->FAIL);
  end proc;

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

  # extract all introduced variables from a KB
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

  # extract Lets and equality constraints (only!) from a KB
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

  # implementing this in terms of Partition (as opposed to algebraic
  # manipulations with the piecewise) cause d0_2(DisintT) to fail
  kb_piecewise := proc(e :: specfunc(piecewise), kb :: t_kb, doIf, doThen, $)
    Partition:-PartitionToPW(
        kb_Partition( Partition:-PWToPartition(e), kb, doIf, doThen )
        ) ;
  end proc;

  #For now at least, this procedure is parallel to kb_piecewise.
  kb_Partition:= proc(e::Partition, kb::t_kb, doIf, doThen, $)::Partition;
  local br;
    #Unlike `piecewise`, the conditions in a Partition are necessarily
    #disjoint, so the `update` used in kb_piecewise isn't needed. We may
    #simply `assert` the condition (i.e., roll it into the kb) without
    #needing to `assert` the negation of all previous conditions.

    Partition:-Amap([doIf, doThen, z -> kb], e);
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
  # This transforms {size,idx}(a,b,..x) to {size,id}[a,b,..x] (that is, a
  # subscript operator, which doesn't evaluate) and back. Some functions
  # evaluating causes simplification to fail because information is lost
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

    # KB 'atoms' , i.e. single pieces of knowledge, in "maple form".
    # Note that boolean already includes `Bound`s in the form `x R y`
    TypeTools[AddType](t_kb_atom,
      '{`::`, boolean, `in`, specfunc(anything,{Or,Not,And})}');
    TypeTools[AddType](t_kb_atoms,list(t_kb_atom));

    # The 'false' KB, produced when a contradiction arises in a KB
    TypeTools[AddType](t_not_a_kb, 'specfunc(NotAKB)');

    # Something that might be a KB, or is the false KB
    TypeTools[AddType](t_kb_mb, '{t_kb, t_not_a_kb}');

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
