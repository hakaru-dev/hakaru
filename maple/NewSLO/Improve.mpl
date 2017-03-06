
# Step 2 of 3: computer algebra

  improve := proc(lo :: LO(name, anything), {_ctx :: t_kb := empty}, $)
  local r, `&context`;
       userinfo(3, improve, "input: ", print(lo &context _ctx));
       userinfo(3, improve, NoName, fflush(terminal));
       r:= LO(op(1,lo), reduce(op(2,lo), op(1,lo), _ctx));
       userinfo(3, improve, "output: ", print(r));
       r
  end proc;

  # Walk through integrals and simplify, recursing through grammar
  # h - name of the linear operator above us
  # kb - domain information
  reduce := proc(ee, h :: name, kb :: t_kb, $)
    local e, subintegral, w, ww, x, c, kb1;
    e := ee;
    if e :: 'And(specfunc({Int,Sum}), anyfunc(anything,name=range))' then
      x, kb1 := `if`(op(0,e)=Int,
        genLebesgue(op([2,1],e), op([2,2,1],e), op([2,2,2],e), kb),
        genType(op([2,1],e), HInt(closed_bounds(op([2,2],e))), kb));
      reduce_IntSum(op(0,e),
        reduce(subs(op([2,1],e)=x, op(1,e)), h, kb1), h, kb1, kb)
    elif e :: 'And(specfunc({Ints,Sums}),
                   anyfunc(anything, name, range, list(name=range)))' then
      x, kb1 := genType(op(2,e),
                        mk_HArray(`if`(op(0,e)=Ints,
                                       HReal(open_bounds(op(3,e))),
                                       HInt(closed_bounds(op(3,e)))),
                                  op(4,e)),
                        kb);
      if nops(op(4,e)) > 0 then
        kb1 := assert(size(x)=op([4,-1,2,2],e)-op([4,-1,2,1],e)+1, kb1);
      end if;
      reduce_IntsSums(op(0,e), reduce(subs(op(2,e)=x, op(1,e)), h, kb1), x,
        op(3,e), op(4,e), h, kb1)
    elif e :: 'applyintegrand(anything, anything)' then
      map(simplify_assuming, e, kb)
    elif e :: `+` then
      map(reduce, e, h, kb)
    elif e :: `*` then
      (subintegral, w) := selectremove(depends, e, h);
      if subintegral :: `*` then error "Nonlinear integral %1", e end if;
      subintegral := convert(reduce(subintegral, h, kb), 'list', `*`);
      (subintegral, ww) := selectremove(depends, subintegral, h);
      reduce_pw(simplify_factor_assuming(`*`(w, op(ww)), kb))
        * `*`(op(subintegral));
    elif e :: t_pw then
      e:= flatten_piecewise(e);
      e := kb_piecewise(e, kb, simplify_assuming,
                        ((rhs, kb) -> %reduce(rhs, h, kb)));
      e := eval(e, %reduce=reduce);
      # big hammer: simplify knows about bound variables, amongst many
      # other things
      Testzero := x -> evalb(simplify(x) = 0);
      reduce_pw(e)
    elif e :: t_case then
      subsop(2=map(proc(b :: Branch(anything, anything))
                     eval(subsop(2='reduce'(op(2,b),x,c),b),
                          {x=h, c=kb})
                   end proc,
                   op(2,e)),
             e);
    elif e :: 'Context(anything, anything)' then
      kb1 := assert(op(1,e), kb);
      # A contradictory `Context' implies anything, so produce 'anything'
      # In particular, 42 :: t_Hakaru = false, so a term under a false
      # assumption should never be inspected in any way.
      if kb1 :: t_not_a_kb then
          return 42
      end if;
      applyop(reduce, 2, e, h, kb1);
    elif e :: 'integrate(anything, Integrand(name, anything), list)' then
      x := gensym(op([2,1],e));
      # If we had HType information for op(1,e),
      # then we could use it to tell kb about x.
      subsop(2=Integrand(x, reduce(subs(op([2,1],e)=x, op([2,2],e)), h, kb)), e)
    else
      simplify_assuming(e, kb)
    end if;
  end proc;

  #
  kb_bounds_of_var :=
    proc( kb::t_kb, x::name, $)
      local v := getType(kb, x)
         , lo, hi, lo_b, hi_b, k ;

      if v :: 'AlmostEveryReal' then
          k := nops(v);
          if k = 0 then
              return (-infinity..infinity);
          elif k = 2 then
              lo, hi := ops(v);
              lo, lo_b := op(1,lo), op(2, lo);
              hi, hi_b := op(1,hi), op(2, hi);

              return (lo_b..hi_b);
          end if;
      end if;

      error "kb_bounds_of_var: unknown type %a", v;

  end proc;

  app_dom_spec_IntSum_LMS :=
   proc( mk :: identical(Int, Sum), ee, h, kb0 :: t_kb
       , sol_, vs_
       , $)

      local sol := sol_, vs := vs_, e := ee;

      if sol :: identical({}) then
          # an empty solution
          DONE(0);

      elif sol :: set(list) then
          # a disjunction of solutions. we need to pick one, or try them
          # all
          e

      elif sol :: set({relation,boolean}) then
          # a single atomic solution, with (hopefully) at most two conjuncts
          # one which becomes incorporated into the lower bound, and the other
          # into the upper bound
          e

      elif sol :: list then
          # a (nonempty, hopefully) conjunction of constraints which
          # are hopefully in a nice form...

          # if we have fewer conjuncts than variables, pad the conjunts
          # with trivial solutions (for the recursive call)

          # sort the conjs by the number of variables which they mention

          # check that the `k'th (from 1) conjunct mentions at most `k'
          # variables. we can (hopefully) integrate these things in
          # a way that differentiation (due to disintegration) eliminates
          # the integral, by making the body free of that integration variable

          # get the list of variables in the order we hope to integrate

          # assign to each variable the range of integration as given in the
          # context. the range will be contracted as we apply the solution

          # starting with the leftmost solution, apply them all
          # hopefully this should only produce valid integrals (i.e. we've done
          # enough checks to guarantee it)

          # determine if this conj is an upper or lower bound for the
          # variable we are now integrating
          e


      elif sol :: Partition then


          # e := `+`( seq( _
          #              , p=( seq( [ op(2*i, sol), op(2*i+1, sol) ]
          #                       , i=1..iquo(nops(sol))
          #                       ), `if`(nops(sol)::odd, [ {}, op(-1,sol) ], NULL)
          #                  )
          #              )
          #         ) ;

          e

      else
          # can't deal with such solutions (what are they?)
          FAIL

      end if;

  end proc;

  app_dom_spec_IntSum :=
    proc(mk :: identical(Int, Sum), ee, h, kb0 :: t_kb
        ,dom_spec_
        ,$)
    local new_rng, make, var, elim, w,
          dom_spec := dom_spec_, e := ee ;

    new_rng, dom_spec := selectremove(type, dom_spec,
      {`if`(mk=Int, [identical(genLebesgue), name, anything, anything], NULL),
       `if`(mk=Sum, [identical(genType), name, specfunc(HInt)], NULL),
       [identical(genLet), name, anything]});
    if not (new_rng :: [list]) then
      error "kb_subtract should return exactly one gen*"
    end if;
    make    := mk;
    new_rng := op(new_rng);
    var     := op(2,new_rng);
    if op(1,new_rng) = genLebesgue then
      new_rng := op(3,new_rng)..op(4,new_rng);
    elif op(1,new_rng) = genType then
      new_rng := range_of_HInt(op(3,new_rng));
    else # op(1,new_rng) = genLet
      if mk=Int then
          # this was just a return, but now is in its own
          # local function and the control flow must be handled
          # up above. although calling 'reduce' on 0 will probably
          # return immediately anyways(?)
          return DONE(0)
      else
          make := eval;
          new_rng := op(3,new_rng)
      end if;
    end if;

    userinfo(3, 'LMS',
        printf("    dom-spec        : %a\n"
               "    dom-var         : %a\n"
         , dom_spec, var ));

    e := `*`(e, op(map(proc(a::[identical(assert),anything], $)
                         Indicator(op(2,a))
                       end proc,
                       dom_spec)));

    userinfo(3, 'LMS',
        printf("    expr-ind        : %a\n"
         , e ));

    elim := elim_intsum(make(e, var=new_rng), h, kb0);

    userinfo(3, 'LMS',
        printf("    expr-elimed     : %a\n"
         , elim ));

    if elim = FAIL then
      e, w := selectremove(depends, list_of_mul(e), var);

      userinfo(3, 'LMS',
          printf("    expr-pull-mull : %a\n"
           , e ));

      DONE( reduce_pw(simplify_factor_assuming(`*`(op(w)), kb0))
        * make(`*`(op(e)), var=new_rng) );
    else
      elim
    end if;

  end proc;

  reduce_IntSum := proc(mk :: identical(Int, Sum),
                        ee, h :: name, kb1 :: t_kb, kb0 :: t_kb, $)
    local e, dom_spec, elim, kb2, lmss, vs, e2, _;

    # if there are domain restrictions, try to apply them
    (dom_spec, e) := get_indicators(ee);

    kb2 := foldr(assert, kb1, op(dom_spec));

    ASSERT(type(kb2,t_kb), "reduce_IntSum : domain spec KB contains a contradiction.");

    dom_spec := kb_subtract(kb2, kb0);

    lmss := kb_LMS(kb2);

    userinfo(3, 'LMS',
         printf("    LMS     : %a\n"
                "    kb Big  : %a\n"
                "    kb small: %a\n"
                "    domain  : %a\n"
                "    var     : %a\n"
         , lmss, kb2, kb0, dom_spec, h ));


    if not lmss :: specfunc('NoSol') then
        lmss, vs, _ := op(lmss);

        if lmss :: 'piecewise' then
            lmss := PWToPartition(lmss) ;
        end if;

        e2 := app_dom_spec_IntSum_LMS( mk, ee, h, kb0, lmss, vs );

        userinfo(3, 'LMS',
                 printf("    LMS-sol  : %a\n"
                , e2 ));
    end if;

    # apply the domain restrictions, which can produce
    #   DONE(x) - produced something which can't be simplified further
    #   x       - more work to be done
    elim := app_dom_spec_IntSum(mk, e, h, kb0, dom_spec);

    userinfo(3, 'LMS',
        printf("    expr            : %a\n"
               "    expr after dom  : %a\n"
         , e, elim ));

    if elim :: specfunc('DONE') then
      op(1,elim);
    else
      elim := reduce(elim, h, kb0);
      userinfo(3, 'LMS',
        printf("    expr-reduced    : %a\n"
         , elim ));
      elim;
    end if;
  end proc;

  reduce_IntsSums := proc(makes, ee, var::name, rng, bds, h::name, kb::t_kb, $)
    local e, elim;
    # TODO we should apply domain restrictions like reduce_IntSum does.
    e := makes(ee, var, rng, bds);
    elim := elim_intsum(e, h, kb);
    if elim = FAIL then e else reduce(elim, h, kb) end if
  end proc;

  get_indicators := proc(e, $)
    local sub, inds, rest;
    if e::`*` then
      sub := map((s -> [get_indicators(s)]), [op(e)]);
      `union`(op(map2(op,1,sub))), `*`(op(map2(op,2,sub)))
    elif e::`^` then
      inds, rest := get_indicators(op(1,e));
      inds, subsop(1=rest, e)
    elif e::'Indicator(anything)' then
      {op(1,e)}, 1
    else
      {}, e
    end if
  end proc;

  elim_intsum := proc(e, h :: name, kb :: t_kb, $)
    local t, var, f, elim;
    t := 'applyintegrand'('identical'(h), 'anything');
    if e :: Int(anything, name=anything) and
       not depends(indets(op(1,e), t), op([2,1],e)) then
      var := op([2,1],e);
      f := 'int_assuming';
    elif e :: Sum(anything, name=anything) and
       not depends(indets(op(1,e), t), op([2,1],e)) then
      var := op([2,1],e);
      f := 'sum_assuming';
    elif e :: Ints(anything, name, range, list(name=range)) and
         not depends(indets(op(1,e), t), op(2,e)) then
      var := op(2,e);
      f := 'ints';
    elif e :: Sums(anything, name, range, list(name=range)) and
         not depends(indets(op(1,e), t), op(2,e)) then
      var := op(2,e);
      f := 'sums';
    else
      return FAIL;
    end if;
    # try to eliminate unused var
    elim := banish(op(1,e), h, kb, infinity, var,
      proc (kb,g,$) do_elim_intsum(kb, f, g, op(2..-1,e)) end proc);
    if has(elim, {MeijerG, undefined, FAIL}) or e = elim or elim :: SymbolicInfinity then
      return FAIL;
    end if;
    elim
  end proc;

  do_elim_intsum := proc(kb, f, ee, v::{name,name=anything})
    local w, e, x, g, t, r;
    w, e := get_indicators(ee);
    e := piecewise_And(w, e, 0);
    e := f(e,v,_rest,kb);
    x := `if`(v::name, v, lhs(v));
    g := '{sum, sum_assuming, sums}';
    if f in g then
      t := {'identical'(x),
            'identical'(x) = 'Not(range(Not({SymbolicInfinity, undefined})))'};
    else
      g := '{int, int_assuming, ints}';
      t := {'identical'(x),
            'identical'(x) = 'anything'};
      if not f in g then g := {f} end if;
    end if;
    for r in indets(e, 'specfunc'(g)) do
      if 1<nops(r) and op(2,r)::t then return FAIL end if
    end do;
    e
  end proc;

  int_assuming := proc(e, v::name=anything, kb::t_kb, $)
    simplify_factor_assuming('int'(e, v), kb);
  end proc;

  sum_assuming := proc(e, v::name=anything, kb::t_kb)
    simplify_factor_assuming('sum'(e, v), kb);
  end proc;

  reduce_pw := proc(ee, $) # ee may or may not be piecewise
    local e;
    e := nub_piecewise(ee);
    if e :: t_pw then
      if nops(e) = 2 then
        return Indicator(op(1,e)) * op(2,e)
      elif nops(e) = 3 and Testzero(op(2,e)) then
        return Indicator(Not(op(1,e))) * op(3,e)
      elif nops(e) = 3 and Testzero(op(3,e)) then
        return Indicator(op(1,e))*op(2,e)
      elif nops(e) = 4 and Testzero(op(2,e)) then
        return Indicator(And(Not(op(1,e)),op(3,e))) * op(4,e)
      end if
    end if;
    return e
  end proc;

  nub_piecewise := proc(pw, $) # pw may or may not be piecewise
    foldr_piecewise(piecewise_if, 0, pw)
  end proc;

  piecewise_if := proc(cond, th, el, $)
    # piecewise_if should be equivalent to `if`, but it produces
    # 'piecewise' and optimizes for when the 3rd argument is 'piecewise'
    if cond = true then
      th
    elif cond = false or Testzero(th - el) then
      el
    elif el :: t_pw then
      if nops(el) >= 2 and Testzero(th - op(2,el)) then
        applyop(Or, 1, el, cond)
      else
        piecewise(cond, th, op(el))
      end if
    elif Testzero(el) then
      piecewise(cond, th)
    else
      piecewise(cond, th, el)
    end if
  end proc;
