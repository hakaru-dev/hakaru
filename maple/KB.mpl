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
     chilled,

     ModuleLoad, ModuleUnload, TYPES,

     # Various utilities
     t_intro, t_lo, t_hi,
     coalesce_bounds, htype_to_property,
     bad_assumption, bad_assumption_pw, bad_assumption_SumProdInt,
     array_size_assumptions, array_elem_assumptions, kb_intro_to_assumptions,

     simpl_range_of_htype,
     known_assuming_expections,

     splitHkName, array_base_type

     ;
  export
     # Functions which build up KBs from KBs and other pieces
     #  typically ensuring that internal invariants are upheld
     # (i.e. 'smart' constructors)
      empty, genLebesgue, genType, genSummation, genIntVar, genLet,
      assert, assert_deny, assert_mb, assert_deny_mb, build_kb,

     # for debugging
     build_unsafely,

     chill, warm,

     # "kb0 - kb1" - that is, kb0 without the knowledge of kb1
     kb_subtract,

     # kb_entails(kb,cond) = "kb => cond"
     kb_entails,

     # Simplify a Hakaru term assuming the knowledge of the kb
     # variants do different things in case of simplification error
     # (which should really only occur when the KB contains a contradicition)
     kb_assuming_mb, kb_eval_mb, simplify_assuming, simplify_assuming_mb, simplify_assuming_f,

     # Gets the most refined (see refine_given) type of a given name under the
     # assumptions of the KB; & convert such a type to a range.
     getType,

     # Various 'views' of the KB, in that they take a KB and produce something
     # which is somehow 'representative' of the KB
     kb_to_variables, kb_to_assumptions, kb_to_constraints, kb_to_equations, kb_piecewise, kb_Partition,

     kb_atom_to_assumptions,

     # Various utilities ...
     range_of_HInt, range_of_htype, eval_kb, kb_is_false,

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
  uses Hakaru, Utilities, SolveTools:-Inequality ;

  # The type of introductions about which we want to pass some useful
  # information to Maple.
  t_intro := 'Introduce(name, And(t_type, Not(specfunc({HMeasure,HFunction}))))';

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
  genLebesgue := genIntVar(proc(lo,hi,$) `AlmostEveryReal`(Bound(`>`,lo), Bound(`<`, hi)) end proc);

  # Another type of integration variable
  genSummation := genIntVar(proc(lo,hi,$) `HInt`(Bound(`>=`,lo), Bound(`<=`, hi)) end proc);

  # A smart constructor for 'integration' (of which summation is a variety)
  # variables.
  genIntVar := proc (kind,$) proc(xx::name, lo, hi, kb::t_kb)
      genType(xx, kind(lo,hi), kb, _rest);
  end proc; end proc;

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

  # The base type of a (possibly) array type is the outermost non-array type
  array_base_type := proc(x::t_type,$)
    if x::specfunc(HArray) then
      array_base_type(op(1,x))
    else x end if;
  end proc;

  # Builds a kb from:
  # - a list of atoms - simply foldr(assert,initKB,as) except
  #   and extra check is (optionally) done for the resulting KB to be valid; or
  # - a kb, in which case the first kb is deconstructed into a list of atoms
  # additionally takes an initial KB into which to fold the atoms; if one KB is
  # empty and the other is not, returns the non-empty one directly.
  build_kb := proc(as_::{t_kb_atoms,t_kb}, shouldBeValid::{identical(false),string} := false, initKb::t_kb := empty, $)
      local kb := initKb, as := as_;
      if as :: t_kb then
        if initKb = empty then
          return as;
        elif as = empty then
          return initKB;
        else # initKb <> empty
          as := kb_to_constraints(as);
        end if;
      end if;

      kb := foldr(assert,kb, op(as));
      if shouldBeValid :: string then
          ASSERT(type(kb,t_kb), sprintf("%s (in build_kb): KB contains a contradiction.", shouldBeValid));
      end if;
      kb
  end proc;

  assert_mb := proc(b::t_kb_atom, mkb::t_kb_mb, $)
      if mkb :: t_kb then
          assert(b,mkb);
      else
          NotAKB();
      end if;
  end proc;

  assert_deny_mb := proc(bb0::t_kb_atom, pol::identical(true,false), kb::t_kb_mb, $)
      if kb :: t_kb then
          assert_deny(bb0,pol,kb);
      else
          NotAKB();
      end if;
  end proc;

  # Like assert_deny, except does not accept a boolean
  # parameter to indicate negation, and evaluates
  # (using Maple's eval, anything can happen!) the
  # new conjunct under the derived knowledge of the KB
  assert := proc(b::t_kb_atom, kb::t_kb, $)
    option remember, system;
    assert_deny(foldl(eval, b, op(kb_to_equations(kb))), true, kb)
  end proc;

  # Implements the assert_deny function, which inserts either
  # a constraint or its negation into a KB, essentially, a
  # 'smart constructor'.
  # Also implements a second way to call it, 'part', which will
  # return a SplitKB instead.
  assert_deny := module ()
   export ModuleApply;
   local t_if_and_or_of, t_not, t_bad_assumption, t_constraint_flipped, bound_simp, not_bound_simp, postproc_for_solve, do_assert_deny,
         refine_given, t_match_array_type, simplify_in_context, expr_indp_errMsg;

   # Either And or Or type, chosen by boolean pol
   t_if_and_or_of := proc(pol,$)
       `if`(pol, '{specfunc(anything, And), `and`}', '{specfunc(anything, Or ), `or` }')
   end proc;

   # The 'type' of `not(..)` statements
   t_not := '{specfunc(anything, Not), `not`}';

   t_bad_assumption := '{t_not({specfunc(And),`and`}), specfunc(Or),satisfies(bad_assumption_pw)}';

   # The type representing equalities
   # between something which is neither a name nor 'size' applied to a name
   # and another thing which is a name which is neither constant nor undefined
   t_constraint_flipped := 'Not({name, size(name)}) = Name';

   # Given a Hakaru type which may be an array type, produce the type matching
   # expressions corresponding to indices into that array type
   t_match_array_type := proc(x::t_type,k:=anything)
     if x :: specfunc(HArray) then
       'idx'( t_match_array_type(op(1,x),k), anything );
     else
       k
     end if;
   end proc;

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

   # Performs simplification in case something of the form `t_bound_on` is
   # found.  This function signals it has failed to find a result with `FAIL`.
   #  rel(x,e)  : relation =  the constraint to add to the KB
   #  k         : t_type   =  type of `x'
   #  kb        : t_kb     =  the KB
   #  pol       : bool     =  add the constraint or its relation
   #  as                  :=  assumptions of the KB
   bound_simp := proc(rel_,x,e_,k,kb,pol,as0,$)
      local c, kb1, ch, as := as0, e := e_, rel := rel_;

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
            kb1 := assert_deny_mb(op([1,1],c)(e,op([1,2],c)), true, kb1)
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

      # Remove assumptions which seem to cause problems (see issue #46).
      as := remove(a->a::relation and
                   is_lhs((s,_)->
                           hastype(s,{specfunc({Sum,Product,Int
                                               ,`sum`,`product`,`int`})})
                          , a)<>FAIL
                   ,as);

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
   not_bound_simp := proc(b,x,kb,pol,as,$)
     local c, bad;
     if _Env_HakaruSolve=false or pol=false then return FAIL; end if;
     if x::relation then
       userinfo(6, 'KB', printf("Chose not to solve %a\n",x));
       return FAIL;
     end if;

     # don't even try to solve bad cases, we might get a RootOf !
     bad := select(depends, indets(b, specfunc(chilled)),x);
     if not (bad = {}) then return FAIL; end if;

     # don't try to solve `var = e' where `depends(e,var)' and
     # `has(e,piecewise)'. this produces an error:
     #     (in Piecewise:-Apply) invalid subscript selector
     if b::{`=`,`<>`} and
        is_lhs((q,r)->q::name and depends(r,q) and has(r,piecewise), b)
          <> FAIL
     then return FAIL;
     end if;

     # otherwise go ahead
     try
       c := kb_assuming_mb(b->solve({chill(b)},[x], 'useassumptions'=true),b,kb,_->FAIL);
       if c = b then
         # sometimes solve returns unevaluated which confuses postproc because
         # it expects the typical output of solve
         return FAIL
       elif has(c,signum) then
         WARNING( "Solving %1 in ctx %2 produced %3 which contains `signum`. "
                  "Probably a bug in `solve`?", b, kb, c);
         return FAIL
       end if;

       c := postproc_for_solve(warm(c), kb);
       if c = FAIL or c = b then
         FAIL
       else
         assert_deny_mb(c, pol, kb);
       end if;
     catch "when calling '%1'. Received: 'side relations must be polynomials in (name or function) variables'":
       WARNING( sprintf( "siderels bug:\n\t'%s'\nwhen calling solve(%%1, %%2) assuming (%%3)"
                         , StringTools[FormatMessage](lastexception[2..-1])), b, x, as );
       return FAIL;
     end try;
   end proc;

   postproc_for_solve := proc(c, kb, $)
     local p, c0, c1;
     if c=FAIL then
       return FAIL;

     elif c :: list and nops(c) = 0 then # false
       return FAIL;

     elif c :: relation then
       return c;

     elif c :: list({relation, specfunc(`And`), `and`}) then # conjunction
       c0 := map(c -> if c::{specfunc(`And`),`and`} then op(c) else c end if,c);
       return bool_And(op(map(postproc_for_solve, c0, kb)));

     elif c :: list(list) then # disjunction
       return bool_Or(op(map(postproc_for_solve, c, kb)));

     elif c :: specfunc(`Not`) then # atom
       return bool_Not(postproc_for_solve(op(1,c), kb));

     elif c :: specfunc(`piecewise`) then # try to make it into a conjunction
       p := Partition:-PWToPartition(c);
       p := Partition:-Simpl:-remove_false_pieces(p, kb);
       c0, c1 := Partition:-Simpl:-single_nonzero_piece(p, _testzero=(x->x=[]));
       if not c0 :: identical(true) then
         if c1 :: relation then
         elif c1 :: list and nops(c1) = 1 then
             c1 := op(1,c1);
             if c1 :: list then c1 := op(c1) end if;
         else
             return FAIL;
         end if;
         try return postproc_for_solve([ c0, c1 ], kb);
         catch "when calling '%1'. Received: 'cannot assume on a constant object'": NULL; end try;
       end if;
       return FAIL;
     end if;

     error "don't know what to do with %1 (in ctx %2)", c, kb;
   end proc;

   # Simplify `bb' in context `as'
   simplify_in_context := proc(bb, as, $)
     local b;
     b := chill(bb);
     b := simplify(b) assuming op(as);
     warm(b);
   end proc;

   ModuleApply := ProfileFn(do_assert_deny, 1);
   # Given a constraint "bb" on a KB "kb", this
   #   inserts either "bb" (if "pol" is true) or "Not bb" (otherwise)
   #   or, KB(Constrain(`if`(pol,bb,Not(bb))), kb)
   # Great deal of magic happens behind the scenes
   do_assert_deny := proc(bb::t_kb_atom, pol::identical(true,false), kb::t_kb)
    # Add `if`(pol,bb,Not(bb)) to kb and return the resulting KB.
    local as, bbv, b, k, x, log_b, todo, kb0, ch, t_x, t_m, t_x0, c;
    b := bb;

    if b = pol then
      # Ignore literal true and Not(false).
      kb

    elif b :: t_if_and_or_of(pol) then
      foldr(((b1,kb) -> assert_deny_mb(b1, pol, kb)), kb, op(b))

    elif b :: t_not then
      assert_deny_mb(op(1,b), not pol, kb)

    else # b::relation
      b  := subsindets(b, Partition, Partition:-PartitionToPW);
      as := chill(kb_to_assumptions(kb, b));
      as := remove(type, as, thismodule:-t_bad_assumption);
      b  := chill(b);

      # try to evaluate under the assumptions, but some assumptions break
      # with eval, so remove any of those we tried to chill to prevent them breaking
      b  := subsindets(b, relation, x-> kb_assuming_mb(x1->map(eval,x1), x, kb, _->x));

      # Simplify the condition, esp. needed before `coulditbe' as it may not get
      # the right answer before simplification (see RoundTrip/testKernel). At
      # worst, this may cause a 'contradictory assumptions' error in a later
      # call.
      b  := simplify_in_context(b, as);

      # Check that the new clause would not cause a contradictory
      # KB. If it does, then produce NotAKB.
      if not bad_assumption(bb) and not rel_coulditbe(`if`(pol,b,Not(b)), as) then
          return NotAKB();
      end if;

      # Look through kb for the innermost scope where b makes sense.
      k := select((k -> k :: Introduce(name, anything) and depends(b, op(1,k))),
                  kb);

      # If that scope is not precisely the trivial KB, then ..
      if nops(k) > 0 then
        x, t_x := op(op(1,k));
        b := try_improve_exp(b, x, as);
        t_x0 := array_base_type(t_x);
        t_m := t_match_array_type(t_x, identical(`x`));

        # if b is a relation of the form `op(identical(x),freeof(x))' where
        # `x::HkName' ...
        if b::relation then
          c := classify_relation(b, t_m);
          if c = FAIL or hastype(op(4,c), t_m) then
            todo := curry(not_bound_simp, b, x);
          else
            todo := curry(bound_simp, op(2..4,c), t_x0)
          end if;
          kb0 := todo(kb, pol, as);

          # If it succeeds, return that result
          if not kb0 :: identical(FAIL) then return kb0 end if;
        end if;
      end if;

      # Normalize `=` and `<>` constraints a bit.
      if not pol then
        b := bool_Not(b);
      end if;

      # If the name in the simple equality (if it is such) is not
      # on the lhs, then flip the equality
      if b :: t_constraint_flipped then b := (rhs(b)=lhs(b)) end if;

      # If `b' reduces to `true' in the KB environment then there is no need to
      # add it; or if it reduces to `false', then the result is NotAKB
      ch := chill(b);
      try
        if is(ch) assuming op(as)     then return kb       end if;
        if not(rel_coulditbe(ch, as)) then return NotAKB() end if;
      catch "when calling '%1'. Received: 'side relations must be polynomials in (name or function) variables'":
        WARNING( sprintf( "siderels bug:\n\t'%s'\nwhen calling is(%%1) assuming (%%2)"
                        , StringTools[FormatMessage](lastexception[2..-1])), b, as );
      end try;

      # Add constraint to KB.
      KB(Constrain(b), op(kb))
    end if;
   end proc: # ModuleApply
  end module; # assert_deny

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
    if cut < 0 or [op(cut+1..-1, kb)] <> [op(kb0)] then
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

  # The constraints do not include type assumptions
  kb_to_constraints := proc(kb::t_kb)::list(t_kb_atom);
    remove(type, kb_to_assumptions(kb,_rest), `::`);
  end proc;

  eval_kb := proc(e,kb::t_kb, $)
    foldl(eval, e, op(kb_to_equations(kb)));
  end proc;

  # The known exceptions which kb_assuming_mb will catch and
  # return as a failure; all others are rethrown
  known_assuming_expections :=
  { "when calling '%2'. Received: '%1 is an invalid property'"  #assume/ProcessTerm
  , "when calling '%1'. Received: 'Can not process Or() or Not(And()) assumption if the object is not a name'" #assume/ProcessTerm
  };

  kb_assuming_mb := proc(simpl, ee, kb::t_kb, failure, $)
    local e, as, e0;                                                         # for debugging

    e := eval_kb(ee,kb);                                                  `eval`;
    as := kb_to_assumptions(kb, e);
    e0 := e;
    e  := chill(e);
    as := chill(as);

    userinfo(3, procname, printf("Trying\n%a(%a) assuming op(%a)\n", simpl, e, as));
    try e := simpl(e) assuming op(as);
    catch :
      if lastexception[2] in known_assuming_expections then
        userinfo(3, procname, printf("...threw a known exception:\n%s",
                                     StringTools[FormatMessage](lastexception[2..-1])));
        return failure(e0);
      else error; end if;
    end try;

    e := warm(e);
  end proc;

  # Given a function `f', 'evaluates' the given expression `e' as follows:
  #  - removes op(0) (`op(e)')
  #  - applies `f' to op(1..nops)
  #  - if the result satisifies the check, return the original expression, else
  #    the result
  # The function `f' can additionally be a pair whose first component is the
  # actual function, and whose second component is the "check" used in the final
  # step. By default, the check is to determine if the result `has' the given
  # function `f'
  # The intended use of this function is to evaluate an expression of a known
  # 'type', and sometimes reject the evaluated result (by default, reject if it
  # contains the evaluation function itself, i.e. if that function 'failed' by
  # returning itself unevaluated.)
  kb_eval_mb := proc(f,e,kb,$)
    local fn, ty, e1;
    fn,ty := `if`(f::[anything$2],f,[f,satisfies(q->has(q,f))])[];
    e1 := kb_assuming_mb(fn@op, e, kb, _->e);
    if e1::ty then e else e1 end if;
  end proc;

  # Simplfies a given Hakaru term under knowledge of the
  # given KB. Does some magic to appease the Maple simplifier.
  # simplification might fail, in which case `failure(e)` where `e`
  # is the un-simplified (and chilled) expression is taken to be the result of
  # simplification. 'mb' for 'maybe'
  simplify_assuming_mb := curry(kb_assuming_mb, simplify@(e->subsindets(e,Partition,Partition:-PartitionToPW)));

  simplify_assuming := proc(ee, kb::t_kb, $)
    simplify_assuming_mb(ee,kb,e->e);
  end proc;

  # like simplify_assuming but propgates the failure (as FAIL) instead of
  # silently consuming it and returning the unsimplified expression.  'f' for
  # 'failure'
  simplify_assuming_f := proc(ee, kb::t_kb, $)
    simplify_assuming_mb(ee,kb,e->FAIL);
  end proc;

  splitHkName := proc(x :: HkName, $)::(list(appliable),name);
    local x1, q, s, b;
    if x :: name then
      [] , x
    elif x :: 'idx'(anything, anything) then
      x1 , q := op(x);
      s , b := splitHkName(x1);
      [ (i->idx(i,q)), op(s) ], b
    end if;
  end proc;

  getType := proc(kb :: t_kb, x_ :: HkName, $)
    local res, over, bound, cs, s, x1, k, mkt, x := x_;

    s, x1 := splitHkName(x);
    k   := nops(s);
    mkt := foldr(`@`,(a->a),HArray$k);

    res := select(type, kb, 'Introduce'(identical(x1), mkt(anything)));
    if nops(res)<>1 then FAIL else
      res := op([1,2,1$k], res);
      # Bounds
      over := table([`<`=identical(`<`,`<=`), `<=`=identical(`<`,`<=`),
                     `>`=identical(`>`,`>=`), `>=`=identical(`>`,`>=`)]);
      for bound in select(type, kb, 'Bound'(identical(x),
                                           identical(`<`,`<=`,`>`,`>=`),
                                           anything)) do
        res := remove(type, res, 'Bound'(over[op(2,bound)], 'anything'));
        res := op(0,res)(subsop(1=NULL,bound), op(res));
      end do;

      # Constrains
      cs := select(type, kb, 'Constrain'(relation));
      # those relations whose left or right hand side is identically the variable
      cs := map(a -> classify_relation(op(1,a), identical(x)), cs);
      cs := select(type, cs, Not(identical(FAIL)));
      cs := op(map(a -> Bound(op(2,a), op(4,a)), cs));
      res := op(0,res)(cs, op(res));

      mkt(res);
    end if;
  end proc;

  # extract all introduced variables from a KB
  kb_to_variables := proc(kb :: t_kb, $)
    [op(map2(op, 1, select(type, kb, t_intro)))];
  end proc;

  # This case is because the following takes forever:
  # simplify(piecewise(_a = docUpdate, aaa, bbb)) assuming i = piecewise(_a_
  # = docUpdate, zNew, idx[z, _a]), _a::integer, 0 <= _a, _a <= size[t]-1,
  # i::integer, 0 <= i, i <= size[as]-2, size[xs] = size[as]-1, size[z] =
  # size[t], docUpdate::integer, 0 <= docUpdate, docUpdate <= size[z]-1
  bad_assumption_pw := (x->x::`=` and has(x,piecewise));

  # This case is because the following takes forever:
  # is(y <= Hakaru:-size[topic_prior]-2) assuming
  #  (.., j <= Sum(piecewise(docUpdate = Hakaru:-idx[doc, i2],
  #                          piecewise(And(i = zNew0, i1 = Hakaru:-idx[w, i2]),
  #                                    1, 0),
  #                          0),
  #                i2 = 0 .. Hakaru:-size[w]-1)-1
  bad_assumption_SumProdInt := proc(a,$)
    local a1,v,r;
    if not(a::relation) then return false; end if;
    a1 := is_lhs((s,_)->s::name, a);
    if a1=FAIL then return false end if;
    v := indets[flat](rhs(a1),specfunc({Int,Sum,Product,`int`,`sum`,`product`}));
    r := evalb(
      v<>{} and
      ormap(x->has(x,piecewise) and has(x,idx),[op(v)]));
    if r then
      userinfo(3, procname, printf("%a is a bad assumption\n",a));
    end if;
    r;
  end proc;

  # Returns true if the assumption is bad, false otherwise
  bad_assumption := proc(a, $)
    bad_assumption_pw(a) or
    ( a :: `=` and
      ormap(f->f(a)::name,[lhs,rhs]) and
      indets(a,'{specindex,specfunc}'(chilled))<>{} ) or
    # These are dealt with otherwise and aren't understood by Maple
    bad_assumption_SumProdInt(a)
  end proc;

  # Note that this returns potentially any number of operands.
  kb_atom_to_assumptions := proc(k, $)
    if k :: t_intro then
      kb_intro_to_assumptions(op(k));
    elif k :: t_kb_Let then
      `=`(op(k))
    elif k :: t_kb_Bound then
      op(2,k)(op(1,k), op(3,k))
    elif k :: t_kb_Constrain then
      op(1,k)
    else
      NULL # Maple doesn't understand our other types
    end if
  end proc;

  # converts an introduction form (a pair of a 'name' and a type) into a
  # sequence of assumtions. `x' is typically an actual name, but need not be;
  # it may be any algebraic term which can appear on the lhs of a `::`
  kb_intro_to_assumptions := proc(x,x_ty::t_type, $)
    local x_typ;
    x_typ := htype_to_property(x_ty);
    (x :: x_typ),
    op(`if`(x_typ<>TopProp, map((b -> `if`(nops(b)>=2,[op(1,b)(x, op(2,b))],[])[]), x_ty),[]))
  end proc;

  kb_to_assumptions := proc(kb, e:={}, to_remove := bad_assumption, $)
    local n, as;
    as := remove(to_remove,
          [ map( kb_atom_to_assumptions ,
                 [op(coalesce_bounds(kb))] )[]

            # additional assumptions which are derived from the expression
            # to be simplified; these are to do with arrays
            ,array_size_assumptions(kb,e)
            ,array_elem_assumptions(kb,e) ] );
  end proc;

  array_size_assumptions := proc(kb,e,$)
    seq(n::nonnegint, n in indets({kb,e}, 'specfunc(size)'));
  end proc;

  array_elem_assumptions := proc(kb,e,$)
    op( map(proc(a)
              local ar := a, lv := 0, ty, l;
              while ar :: 'idx(anything,anything)' do
                ar := op(1,ar);
                lv := lv + 1;
              end do;
              if not(ar :: name) then return NULL end if;
              ty := getType(kb, ar);
              if ty = FAIL then return NULL end if;
              for l from 1 to lv do
                if not(ty::specfunc(HArray)) then
                  WARNING("in array_elem_assumptions; Subterm %1 of %2 is a %3-level array index; but "
                          "%4 is not even a %5-level array in %6!", a, e, lv, ar, l, kb);
                  return NULL;
                end if;
                ty := op(1, ty);
              end do;
              kb_intro_to_assumptions(a, ty);
            end proc,
            indets({kb,e}, 'idx(anything,anything)')) );
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

  # See kb_Partition
  kb_piecewise := proc(e :: specfunc(piecewise), kb :: t_kb, doIf, doThen)
    Partition:-PartitionToPW(
        kb_Partition(Partition:-PWToPartition(e, _rest), kb, doIf, doThen)
        ) ;
  end proc;

  # A sort of map over a Partition with the given KB as a context, such that:
  #    kb_Partition( PARTITION ( Piece( c_i , v_i ), .. )  , kb, doIf, doThen )
  #    =
  #    PARTITION ( Piece( doIf(c_i, kb), doThen(v_i, assert(c_i, kb)) ) )
  # Semantics originally given here:
  #  https://github.com/hakaru-dev/hakaru/commit/6f1c1ea2d039a91c157462f09f15760c98884303
  kb_Partition:= proc(e::Partition, kb::t_kb, doIf, doThen,$)::Partition;
  local pr;
    #Unlike `piecewise`, the conditions in a Partition are necessarily
    #disjoint, so the `update` used in kb_piecewise isn't needed. We may
    #simply `assert` the condition (i.e., roll it into the kb) without
    #needing to `assert` the negation of all previous conditions.

    pr := Partition:-Amap([(x,_) -> doIf(x, kb), (x,c) -> %doThen(x, assert(c,kb)), z -> z], e);
    pr := applyop(ps -> remove(x->type(op([2,2],x),t_not_a_kb),ps), 1, pr);
    eval(pr, %doThen=doThen);
  end proc;

  # Computes the range of (possible values of) a Hakaru Int,
  # given a Hakaru type for that Int.
  range_of_HInt := proc(t :: And(specfunc(HInt), t_type), $)
    range_of_htype(t);
  end proc;

  simpl_range_of_htype :=
    table(
      [`HInt`=[(b -> `if`(op(1,b)=`>`, floor(op(2,b))+1, op(2,b))),
               (b -> `if`(op(1,b)=`<`, ceil (op(2,b))-1, op(2,b)))]
      ,`HReal`=[(b->`if`(op(1,b)in{`>`,`<`},Open,x->x)(op(2,b)))$2]
      ,`AlmostEveryReal`=[curry(op,2) $ 2]
      ]);

  range_of_htype := proc(t :: And(specfunc({HInt,HReal,AlmostEveryReal}),t_type),$)
    `..`(op(
      zip_k((tt,db,sb)->
            op(1,map(sb,[op(select(type, t, Bound(tt,anything))),db])) ,
            [t_lo, t_hi] ,
            [Bound(`>`,-infinity),Bound(`<`,infinity)] ,
            simpl_range_of_htype[op(0,t)] )));
  end proc;

  # Avoid FAILure modes of the assumption system
  # This transforms {size,idx}(a,b,..x) to {size,id}[a,b,..x] (that is, a
  # subscript operator, which doesn't evaluate) and back. Some functions
  # evaluating causes simplification to fail because information is lost
  chilled := '{size, idx}';
  chill := curry(chillFns,chilled);
  warm  := curry(warmFns,chilled);

  # The KB constructors are local, but sometimes for debugging purposes one
  # would like to construct the KB directly. This converts the global names
  # Introduce,Constrain,Let, and Bound to KB:-<..> and replaces the 0-th operand
  # with KB:-KB.
  build_unsafely := proc(kb,$)
    KB(op(subs([ :-Introduce=Introduce, :-Let=Let, :-Bound=Bound, :-Constrain=Constrain ], kb)));
  end proc;

  TYPES := table(
    [(t_kb=
      ''specfunc({
         Introduce(name, t_type),
         Let(HkName, anything),
         Bound(HkName, identical(`<`,`<=`,`>`,`>=`,`=`), anything),
         Constrain({`::`, boolean, `in`, specfunc(anything,{Or,Not})})
       }, KB)'')

    # KB 'atoms' , i.e. single pieces of knowledge, in "maple form".
    # Note that boolean already includes `Bound`s in the form `x R y`
    ,(t_kb_atom = ''Relation'')
    ,(t_kb_atoms = 'list(t_kb_atom)')

    # The 'false' KB, produced when a contradiction arises in a KB
    ,(t_not_a_kb = ''specfunc(NotAKB)'')

    # Something that might be a KB, or is the false KB
    ,(t_kb_mb = ''{t_kb, t_not_a_kb}'')
    ,(HkName = ''Or(name,'idx'(HkName,anything))'')
    ]);

  ModuleLoad := proc($)
    # Make sure modules are loaded for types
    Hakaru; Utilities;

    BindingTools:-load_types_from_table(TYPES);

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
    NULL;
  end proc;
  ModuleLoad();
end module; # KB
