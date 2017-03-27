### Domain abstraction

# A domain is abstractly a pair of a "square" domain (a product of square
# domains, or an interval), the domain "bounds", and a domain "shape". The
# domain "bounds" are essentially the variables, each with the type of domain
# (Int,Sum, etc) ; the domains "shape" is sums of products of constraints
# (relations) on the domain, interspersed with 'makes' (DInto) which parametrize
# a subdomain by one of the domain variables ('picking' a particular
# parametrization of the domain, in which one variable is fixed in subsequent
# "shape" constructors).

# the seperation between the two 'stages' of domain exists mainly because
# certain simplifications need to happen after extracting the domain
# bounds but before extracting the domain shape, as the shape ends up
# becoming part of the bounds of an inner simplification.

# Note that large parts of this are not very nice. It is a very literal
# translation of the code which it replaced, which a very thin amount
# of abstraction on top. But it does the hard work of factoring
# out all of the domain-related code into a single module.
# At some point, the interface should be improved, and the implementation
# should get rid of all sorts of unnecessary conversions.
Domain := module()

# TODO: formalize this with maple types (I don't actually know how...)
#   Domain = DOMAIN(DomBound, DomShape)
#   DomBound = DOMBOUND(list(name), KB)
#   DomShape =
#     | DConstrain(relation*)
#     | DSum (DomShape*)
#     | DSplit(Partition(DomShape))
#     | DInto(name, BoundType, DomShape)

    # todo: DOMAIN should perform certain 'simplifications' to make sure the
    # domain is well-formed. e.g.,
    #   DOMAIN( DBound( [x,y], [xt,yt] ), DConstrain(..) )
    #      should  become
    #                                     DInto(x,xt,DInto(y,yt,DConstrain(..)))
    # basically, when we see an 'unbound' variable in the 'RHS' , we should bind
    # it with the default 'DInto'.
    # The two-part nature of Domain requires that this be done by the DOMAIN
    # constructor itself. Alternatively, it can be part of the logic of
    # 'Apply'. It is probably cheaper to put it there, since it duplicates less information.

    global DOMAIN;
    global DBound;

    global DConstrain;
    global DSum;
    global DSplit;
    global DInto;

    global DNoSol;

    # Checks if an expression has domain bounds/shape, and check for either one.
    export Has := module ()

       export Bound := proc(e, $)
               assigned(Domain:-ExtBound[op(0,e)]) and
               evalb(e :: Domain:-ExtBound[op(0,e)]:-MapleType);
       end proc;

       export Shape := proc(e, $)
               assigned(Domain:-ExtShape[op(0,e)]) and
               evalb(e :: Domain:-ExtShape[op(0,e)]:-MapleType);
       end proc;

       export ModuleApply := proc(e, $)
               Bound(e) or Shape(e);
       end proc;

    end module;

    # Convert Domain to a KB. Very partial, mainly for backwards compatibility
    # for parts of the code which still work with KB.
    export Bound := module ()

       export toKB := proc(dom, kb, $)
         local kb0 := op(2, dom)
             , kb1 := op(0, kb0)( op(kb0), op(kb) ); # huge hack...
         kb1;
       end proc;

    end module;

    export Shape := module ()
         export asConstraints := proc(sh_, $)
           local sh := sh_;

           if sh :: specfunc(`DConstrain`) then
               [ op(sh) ];

           # elif sh :: specfunc(`DSum`) then
           # elif sh :: specfunc(`DSplit`) then

           elif sh :: specfunc(`DInto`) then
               asConstraints(op(3, sh));
           else
               error "don't know how to apply %1", sh
           end if;

         end proc;

    end module;

    # Extending domain extraction and replacement.
    export ExtBound := table();
    export ExtShape := table();

    local ModuleLoad := proc($)
           ExtBound[`Int`] :=
               Record('MakeKB'=(e -> kb -> genLebesgue(op([1],e), op([2,1],e), op([2,2],e), kb))
                     ,'MakeEqn'=`=`
                     ,'MapleType'='And(specfunc({Int}), anyfunc(anything,name=range))'
                     ,'HType'=AlmostEveryReal
                     ,'RangeOf'= # extracts a range (`..`) from a hakaru type
                      (proc(v,$)
                         local lo, hi, lo_b, hi_b, k ;

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
                                 error "unknown bound %1", op([1,1],v);
                             end if;

                         end if;
                         return lo_b .. hi_b;
                       end proc)
                     );

           ExtBound[`Sum`] :=
               Record('MakeKB'=(e -> kb -> genSummation(op([1],e), op(op([2],e)), kb))
                     ,'MakeEqn'=`=`
                     ,'MapleType'='And(specfunc({Sum}), anyfunc(anything,name=range))'
                     ,'HType'=HInt
                     ,'RangeOf'=KB:-range_of_HInt
                     );

           ExtShape[`Indicator`] :=
               Record('MakeCtx'=(e -> ( {op(1,e)}, 1 ))
                     ,'MapleType'='Indicator(anything)'
                     );

           ExtShape[`PARTITION`] :=
               Record('MakeCtx'=Partition:-Simpl:-single_nonzero_piece
                     ,'MapleType'='Partition'
                     );

    end proc;

    # Extract a domain from an expression
    export Extract := module ()

           # Map from hakaru types to types of domain bounds
           export MakeOfType := module()
              local makeTable := proc()
                 table([seq( ExtBound[e]:-HType=e,e=[indices(ExtBound,'nolist')])]);
              end proc;

              export ModuleApply := proc(t, $)
                 makeTable()[op(0,t)];
              end proc;
           end module;

           # Extract a domain bound from an expression
           # This pops off the integration constructors recursively, keeping
           # track of the bounds in a KB (which literally become the DBound).
           export Bound := module ()
             local do_extract_arg := proc(kb1_, vars, kind, arg_, bound, $)
               local kb1 := kb1_, x0, x, vars1, ty, arg := arg_;

               x0 := op(1, bound);
               x, kb1 := ExtBound[kind]:-MakeKB(bound)(kb1);

               vars1 := [ x, op(vars) ];
               arg   := subs(ExtBound[kind]:-MakeEqn(x0,x), arg);

               do_extract(kb1, vars1, arg);
             end proc;

             local do_extract := proc(kb1, vars, arg, $)
               if Domain:-Has:-Bound(arg) then
                   do_extract_arg(kb1, vars, op(0,arg), op(arg));
               else
                   arg, vars, kb1
               end if;

             end proc;

             export ModuleApply := proc(e, $)
                        local arg, vars, kb;
                        arg, vars, kb := do_extract(KB:-empty, [], e);

                        arg, DBound(vars, kb);
             end proc;
           end module;


           # Extract a domain shape from an expression
           # This extracts the domain shape from individual multiplicands of
           # expressions, and multiplies the subexpressions back together.
           # essentially this assumes a distributive law (of domain shapes over
           # products)
           export Shape := module ()

             local do_get := proc(f, f_ty, $) proc(e, $)
               local sub, inds, rest;
               if e::`*` then
                 sub := map((s -> [do_get(f, f_ty)(s)]), [op(e)]);
                 `union`(op(map2(op,1,sub))), `*`(op(map2(op,2,sub)))
               elif e::`^` then
                 inds, rest := do_get(f, f_ty)(op(1,e));
                 inds, subsop(1=rest, e)
               elif e:: f_ty then
                 f(e)
               else
                 {}, e
               end if

             end proc; end proc;

             # apply a list of extractors, in order, until all fail to produce
             # any output .
             local do_gets := proc(todo::list, w, e, $)
                       local t0, ts, w1, e1;
                       if nops(todo) = 0 then
                           w, e
                       else
                           t0 := op(1, todo);
                           ts := op(subsop(1=NULL, todo));
                           if indets(e, specfunc(t0)) <> {} then
                               w1, e1 :=
                                 do_get(ExtShape[t0]:-MakeCtx
                                       ,ExtShape[t0]:-MapleType
                                       )(e);
                               ts := `if`(w1={}, [ts], [ts, t0]);

                               do_gets( ts, w1 union w, e1 );
                           else
                               do_gets( [ ts ], w, e );
                           end if;
                       end if;
             end proc;

             # todo: simplify the shape
             local simpl_shape := (x->x);

             export ModuleApply := proc(e, $)
                        local ixs, w, e1;
                        ixs := [indices(ExtShape, 'nolist')];
                        w, e1 := do_gets(ixs, {}, e);

                        w := DConstrain(op(w));
                        w := simpl_shape(w);

                        w, e1
             end proc;
           end module;

           export ModuleApply := proc(e, $)
                      local b, eb, s, es;
                      b, eb := Bound(e);
                      s, es := Shape(eb);
                      DOMAIN(b, s), es;
           end proc;
    end module;


    # Apply a domain to an expression.
    export Apply := module ()
           local do_mk := proc(e, vs_ty, vn, ty_, $)
              local mk, rng, ty := ty_;

              # somewhat of a hack to get around inconsistent representations
              # of domain intervals.
              if ty :: t_type then
                  mk := Extract:-MakeOfType(ty);
                  rng := Domain:-ExtBound[mk]:-RangeOf(ty);

              elif ty :: `..` then
                  mk := Extract:-MakeOfType( getType(vs_ty, vn) );
                  rng := ty;

              else
                  error "don't know how to make %1", ty
              end if;

              rng := Domain:-ExtBound[mk]:-MakeEqn(vn, rng);

              mk(e, rng);

           end proc;

           # main loop of the apply function
           # e     := expr
           # vs    := variables
           # vs_ty := domain bounds (as a kb)
           # sh    := domain shape
           local do_apply := proc(e, vs, vs_ty, sh_, $)
              local sh := sh_, e1, vn, vt, shv, ty, vn_ty, kb1, cond;

              # If the solution is a constraint, and the constraint is true,
              # then just produce the expression. If it isn't necessarily true
              # (i.e. trivial) then produce a Partition with the constraint as a
              # guard.
              if sh :: specfunc(`DConstrain`) then
                  cond := `and`(op(sh));
                  if is(cond) then
                      e
                  else
                      PWToPartition(piecewise(cond, e, 0));
                  end if;

              # if the solution is a sum of solutions, produce the algebraic sum
              # of each summand of the solution applied to the expression.
              elif sh :: specfunc(`DSum`) then
                  `+`(seq(do_apply(e, vs, vs_ty, s), s=sh))

              # if the solution is a split solution, just make `do_apply' over
              # the values of the Partition (the subsolutions)
              elif sh :: specfunc(`DSplit`) then
                  sh := op(1, sh);
                  Partition:-Pmap(p-> do_apply(e, vs, vs_ty, p), sh);

              # performs the 'make' on the expression after recursively
              # applying the solution
              elif sh :: specfunc(`DInto`) then
                  # deconstruction
                  vn, vt, shv := op(sh);

                  # recursively apply
                  e1 := do_apply(e, [vn], vs_ty, shv);

                  # build this integral
                  do_mk(e1, vs_ty, vn, vt);
              else
                  error "don't know how to apply %1", sh
              end if;
           end proc;

           export ModuleApply := proc(dom, e, $)
             local vs, sh, vs_ty, vn, e1, ty, _;
             vs, sh := op(dom);
             vs, vs_ty := op(vs);

             # kb_as := kb_to_assumptions(kb);
             # vs_ty := build_kb( kb_as, "Domain/Apply", vs_ty );

             do_apply(e, vs, vs_ty, sh);
           end proc;
    end module;

    export Improve := module ()
           export Simplifiers := table();

           export ModuleLoad := proc($)

             Simplifiers[`LMS`] := (
                 module()

                   local countVs := vs -> (c-> nops(indets(c, name) intersect {op(vs)} ));

                   # Sorts the solutions so that resulting integrals are
                   # well-scoped
                   local orderSols := proc(sol,vs,$)
                     local sol2, solOrder ;

                     # sort the conjs by the number of variables which they mention
                     sol2, solOrder :=
                               sort( sol, key= (x-> -(countVs(vs)(x)))
                                   , output=[sorted,permutation]
                                   );

                   end proc;

                   # given a solution for a single variable,
                   # either extracts upper and/or lower bounds from the solution
                   # or leaves that solution as a constraint.
                   local classifySol1 :=
                     proc(v, vs_ty, sol :: set({relation,boolean}), ctx, $)
                         local hi, lo, v_t;

                         # try to check if we can extract upper and lower bounds from the
                         # solution directly
                         hi := subsindets( sol , {relation,boolean} , extract_bound_hi(v) );
                         lo := subsindets( sol , {relation,boolean} , extract_bound_lo(v) );

                         if `and`(nops(sol) = 2
                                 ,nops(hi) = 1
                                 ,nops(lo) = 1
                                 ) then
                             v_t := op(1,lo) .. op(1,hi) ;

                             DInto(v, v_t, ctx);

                         elif nops(sol) = 1 and (nops(hi) = 1 or nops(lo) = 1) then
                             lo := `if`( nops(lo) = 1 , op(1,lo), -infinity );
                             hi := `if`( nops(hi) = 1 , op(1,hi),  infinity );

                             v_t := lo .. hi;

                             DInto(v, v_t, ctx);

                         else
                             subsindets( ctx, specfunc(`DConstrain`)
                                       , x-> DConstrain(op(x), op(sol))
                                       );
                         end if;
                 end proc;

                 # Orders the solution, then classifies each solution, and
                 # builds the single solution with the correct variable order.
                 local classifySols := proc(vs, vs_ty, $) proc( sol :: list(set({relation,boolean})), $ )
                    local sol1, ctx, dmk, s, solOrd, vso, v;
                    sol1, solOrd := orderSols(sol, vs);
                    vso := vs[solOrd];

                    sol1 := zip(proc() [_passed] end proc, sol1, vso);

                    ctx := DConstrain();
                    for v in sol1 do
                        ctx := classifySol1(op(2,v), vs_ty, op(1, v), ctx);
                    end do;

                    ctx;
                 end proc; end proc;

                 # classifyAtom maps
                 # `true' (produced by LMS for trivial systems) - to the
                 #    interval for the variable corresponding to this index in
                 #    the sequence.
                 # `c : name' - to the interval for `v'
                 # everything else - to itself
                 local classifyAtom := proc(c, vs_ty, v, $)
                    local ty, mk, bnd, lo, hi;

                    if c :: identical(true) then
                        ty := getType(vs_ty, v);

                        mk   := Extract:-MakeOfType(ty);
                        bnd  := ExtBound[mk]:-RangeOf(ty);

                        lo, hi := op(bnd);

                        lo <= v, v <= hi;

                    elif c :: name and depends(vs_ty, c) then
                        ty := getType(vs_ty, c);

                        mk   := Extract:-MakeOfType(ty);
                        bnd  := ExtBound[mk]:-RangeOf(ty);

                        lo, hi := op(bnd);

                        lo <= c, c <= hi;
                    else
                        c
                    end if;
                 end proc;

                 # transforms the solution to the form required by Domain
                 # this would be a straightforward syntactic manipulation,
                 # but for the facts that we have to:
                 #  decide the order of integration
                 #  decide which solutions become integrations and which
                 #     become constrains
                 local postproc := proc(sol, vs, vs_ty, $)
                   local ret := sol;

                   ret := subsindets(ret, specfunc('piecewise')
                                    , x-> DSplit(Partition:-PWToPartition(x)));

                   ret := subsindets(ret
                                    , Or(identical({}), set(list))
                                    , x -> DSum(op(x)) );

                   ret := subsindets(ret, list(set({relation,boolean, name}))
                                    , classifySols(vs, vs_ty) @
                                      ( ls -> [ seq( map(a->classifyAtom(a, vs_ty, vs[si]), op(si, ls)) , si=1..nops(ls) ) ] )
                                     );

                   ret;
                 end proc;

                 # ask Maple for a solution to our system
                 local do_LMS := proc( sh, vs_, ctx, $ )
                   local vs := vs_, cs := ctx, ret;

                   if sh :: specfunc(`DConstrain`) then
                       cs := KB:-build_kb([op(sh)], "do_LMS", cs);
                   else
                       error "don't know how to solve %1", sh;
                   end if;

                   cs := op(3, kb_extract(cs));
                   cs := {op(cs)};

                  # there are variables to solve for, but no non-trivial
                  # constraints which need to be solved.
                   if cs = {} and not vs = [] then
                     # this matches the output format of LMS; [x,y] -> { [ {true}, {true} ] }
                     ret := { map(o->{true}, vs) };

                   elif not cs = {} and vs = [] then
                       ret := DNoSol("There are no variables to solve for, but there are constraints."
                                   " This means the variables have not been correctly identified.");

                   elif cs = {} and vs = [] then
                       ret := DNoSol("Something went very wrong");

                   else
                       try
                           ret := LinearMultivariateSystem( cs, vs );
                       catch "the system must be linear in %1":
                           ret := DNoSol(sprintf("The system (%a) must be linear in %a."
                                                , cs, vs ));

                       catch "inequality must be linear in %1":
                           ret := DNoSol(sprintf("The system (%a) contains nonlinear inequality in "
                                                "one of %a."
                                                , cs, vs ));
                       end try;

                   end if;

                   ret;
                 end proc;

                 export ModuleApply := proc(dom, $)
                    local dbnds, dshape, db_vars, db_ctx, sol, domKb, domCtx, res;
                    dbnds, dshape := op(dom);
                    db_vars, db_ctx := op(dbnds);

                    sol := do_LMS( dshape , db_vars, db_ctx );
                    if sol :: specfunc(`DNoSol`) then return sol end if;

                    sol := postproc(sol, db_vars, db_ctx);
                    DOMAIN( dbnds, sol );
                 end proc;

                 end module);

           end proc;

           # TODO: this should keep errors (esp. if everything fails to
           # simplify), or print them as a warning(?)
           local cmp_simp := proc(s0, s1, $) proc(dom, $)
              local dom1 := s0(dom);
              if not dom1 :: specfunc(`DNoSol`) then
                  s1(dom1);
              else
                  s1(dom);
              end if;
           end proc; end proc;

           export ModuleApply := proc(dom, $)
               local es := entries(Simplifiers)
                   , mk := foldr( cmp_simp , (x->x), op(es) );
               mk(dom);
           end proc;
    end module;

    uses Hakaru, KB, Partition, SolveTools[Inequality] ;

end module;
