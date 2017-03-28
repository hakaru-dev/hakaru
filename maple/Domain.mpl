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

option package;

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

       export Bound := proc(e, $)::truefalse;
               assigned(Domain:-ExtBound[op(0,e)]) and
               evalb(e :: Domain:-ExtBound[op(0,e)]:-MapleType);
       end proc;

       export Shape := proc(e, $)::truefalse;
               assigned(Domain:-ExtShape[op(0,e)]) and
               evalb(e :: Domain:-ExtShape[op(0,e)]:-MapleType);
       end proc;

       export ModuleApply := proc(e, $)::truefalse;
               Bound(e) or Shape(e);
       end proc;

    end module;

    # Convert Domain to a KB. Very partial, mainly for backwards compatibility
    # for parts of the code which still work with KB.
    export Bound := module ()

       export toKB := proc(dom :: DomBound, kb0 :: t_kb, $)::[t_kb_mb, anything];
         local kb := kb0, vs := op(1, dom), rn := []
             , vn, vt, make, lo, hi, vn_rn, rn_t, v ;

         for v in vs do
             vn, vt, make := op(v);
             lo, hi := ExtBound[make]:-SplitBound(vt);
             vn_rn, kb := ExtBound[make]:-MakeKB( vn, lo, hi, kb );

             rn := [ vn=vn_rn, op(rn) ];
         end do;

         rn_t := map(x->apply(rhs=lhs,x), rn);
         [ kb, (proc(f,e0,$)
                  local e := e0;
                  e := subs(rn, e); e := f(e); e := subs(rn_t, e);
                  e;
                end proc) ];

       end proc;

       export varsOf := proc(dom :: DomBound, $)::list(name);
         map(x->op(1,x), op(1, dom));
       end proc;

       export get := proc(dom :: DomBound, var :: name, $)
         local th;
         th := select(x->op(1,x)=var, op(1,dom));
         if nops(th) = 1 then
             op([1,2], th), op([1,3], th)
         elif nops(th) = 0 then
             error "cannot find var %1 in %2", var, dom;
         else
             error "multiple references in %1", dom;
         end if;

       end proc;

    end module;

    export Shape := module ()

         export asConstraints := proc(sh_ :: DomShape, $)::list({boolean,relation});
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

    # Domain types which are registered/unregistered with TypeTools.
    # Note that the types have to be quoted (additionally to the quote one would
    # normally place on certain types) to work properly
    local DomainTypes := table(
           # Domain bounds
           [(DomBoundBinder = ''DInto(name, range, DomBoundKind)'' )
           ,(DomBoundKind   = 'And(name, satisfies(nm->assigned(Domain:-ExtBound[nm])))' )

           ,(DomBound       = ''DBound(list(DomBoundBinder))'' )

           # Domain shape
           ,(DomConstrain = 'specfunc({relation, specfunc({`And`,`Not`,`Or`}), `and`, `not`, `or`}, `DConstrain`)' )
           ,(DomSum       = 'specfunc(DomShape, `DSum`)' )
           ,(DomSplit     = ''DSplit(Partition(DomShape))'' )
           ,(DomInto      = ''DInto(name, range, DomShape)'' )
           ,(DomShape     = 'Or( DomConstrain, DomSum, DomSplit, DomInto )' )

           # Domain
           ,('Domain' = ''DOMAIN(DomBound, DomShape)'' )

           # Maybe domain
           ,(DomNoSol  = 'specfunc(`DNoSol`)' )
           ,(Domain_mb = ''Or(Domain, DomNoSol)'' )
           ] );


    # Extending domain extraction and replacement.
    export ExtBound := table();
    export ExtShape := table();

    local ModuleLoad := proc($)
           local ty_nm;

           unprotect(`type/Domain`);
           unassign(`type/Domain`);

           for ty_nm in [ indices(DomainTypes, nolist) ] do
               TypeTools[AddType]( ty_nm, DomainTypes[ty_nm] );
           end do;

           unprotect(Domain:-ExtBound);
           ExtBound[`Int`] :=
               Record('MakeKB'=KB:-genLebesgue
                     ,'ExtractVar'=(e->op(1,e))
                     ,'ExtractBound'=(e->op(2,e))
                     ,'SplitBound'=(e->op(e))
                     ,'Constrain'=`<`
                     ,'MakeEqn'=`=`
                     ,'MapleType'='And(specfunc({Int}), anyfunc(anything,name=range))'
                     );

           ExtBound[`Sum`] :=
               Record('MakeKB'=KB:-genSummation
                     ,'ExtractVar'=(e->op(1,e))
                     ,'ExtractBound'=(e->op(2,e))
                     ,'SplitBound'=(e->op(e))
                     ,'Constrain'=`<=`
                     ,'MakeEqn'=`=`
                     ,'MapleType'='And(specfunc({Sum}), anyfunc(anything,name=range))'
                     );
           protect(Domain:-ExtBound);

           unprotect(Domain:-ExtShape);
           ExtShape[`Indicator`] :=
               Record('MakeCtx'=(e -> ( {op(1,e)}, 1 ))
                     ,'MapleType'='Indicator(anything)'
                     );

           ExtShape[`PARTITION`] :=
               Record('MakeCtx'=Partition:-Simpl:-single_nonzero_piece
                     ,'MapleType'='Partition'
                     );
           unprotect(Domain:-ExtShape);
    end proc;

    local ModuleUnload := proc($)
        local ty_nm;
        for ty_nm in [ indices(DomainTypes, nolist) ] do
            if TypeTools[Exists](ty_nm) then TypeTools[RemoveType](ty_nm) end if;
        end do;

    end proc;

    # Extract a domain from an expression
    export Extract := module ()

           # Extract a domain bound from an expression
           # This pops off the integration constructors recursively, keeping
           # track of the bounds in a KB (which literally become the DBound).
           export Bound := module ()
             local do_extract_arg := proc(vars, kind, arg_, bound, $)
               local x0, x, vars1, arg := arg_, rng;

               x0  := ExtBound[kind]:-ExtractVar(bound);   # variable name
               rng := ExtBound[kind]:-ExtractBound(bound); # variable range
               x   := DInto(x0, rng, kind);                # the variable spec
               vars1 := [ x, op(vars) ];

               do_extract(vars1, arg);
             end proc;

             local do_extract := proc(vars, arg, $)
               if Domain:-Has:-Bound(arg) then
                   do_extract_arg(vars, op(0,arg), op(arg));
               else
                   arg, vars
               end if;

             end proc;

             export ModuleApply := proc(e, $) :: [ DomBound, anything ];
                        local arg, vars, kb;
                        arg, vars := do_extract([], e);

                        [ DBound(vars), arg ];
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

             export ModuleApply := proc(e, $) :: [ DomShape, anything ];
                        local ixs, w, e1;
                        ixs := [indices(ExtShape, 'nolist')];
                        w, e1 := do_gets(ixs, {}, e);

                        w := DConstrain(op(w));
                        w := simpl_shape(w);

                        [ w, e1 ];
             end proc;
           end module;

           export ModuleApply := proc(e, $) :: [ Domain, anything ];
                      local b, eb, s, es;
                      b, eb := op(Bound(e));
                      s, es := op(Shape(eb));
                      [ DOMAIN(b, s), es ];
           end proc;
    end module;


    # Apply a domain to an expression.
    export Apply := module ()
           local do_mk := proc(e, vn, ty_, mk, $)
              mk(e, Domain:-ExtBound[mk]:-MakeEqn(vn, ty_));
           end proc;

           # main loop of the apply function
           # e     := expr
           # vs    := variables
           # vs_ty := domain bounds (as a kb)
           # sh    := domain shape
           local do_apply := proc(done__, e, vs, sh_, $)
              local sh := sh_, done_ := done__
                  , cond, r, vs_td, v_td, vn_td, vt_td, vt_mk, vn, vt, shv, vars, deps
                  , e1, v, vvn, vvt, vmk,  with_kb1 ;

              # If the solution is a constraint, and the constraint is true,
              # then just produce the expression. If it isn't necessarily true
              # (i.e. trivial) then produce a Partition with the constraint as a
              # guard.
              if sh :: DomConstrain then
                  cond := `and`(op(sh));
                  if is(cond) then
                      r := e
                  else
                      r := PWToPartition(piecewise(cond, e, 0));
                  end if;

                  # if there are still integrals which have not been applied,
                  # apply them now
                  vs_td := select(x -> not(op(1, x) in done_), op(1, vs));
                  for v_td in vs_td do
                      vn_td, vt_td, vt_mk := op(v_td);
                      r := do_mk(r, vn_td, vt_td, vt_mk);
                  end do;

                  r;

              # if the solution is a sum of solutions, produce the algebraic sum
              # of each summand of the solution applied to the expression.
              elif sh :: DomSum then
                  `+`(seq(do_apply(done_, e, vs, s), s=sh))

              # if the solution is a split solution, just make `do_apply' over
              # the values of the Partition (the subsolutions)
              elif sh :: DomSplit then
                  sh := op(1, sh);
                  Partition:-Pmap(p-> do_apply(done_, e, vs, p), sh);

              # performs the 'make' on the expression after recursively
              # applying the solution
              elif sh :: DomInto then
                  # deconstruction
                  vn, vt, shv := op(sh);

                  # extract bounds which have not been applied upon which this
                  # bound depends. Those are applied after this one, so are not
                  # in 'scope' in the recursive call
                  vars := {op(Domain:-Bound:-varsOf(vs))};
                  deps := (indets(vt, name) intersect vars) minus done_ ;
                  done_ := `union`(done_, deps, {vn}) ;

                  # recursively apply
                  e1 := do_apply(done_, e, vs, shv);

                  # build this integral, and the other this one depended on
                  for v in op(1,vs) do
                      vvn, vvt, vmk := op(v);
                      if vvn in deps then
                          e1 := do_mk(e1, vvn, vvt, vmk);
                      elif vvn = vn then
                          e1 := do_mk(e1, vvn,  vt, vmk);
                      end if;
                  end do;

                  e1;

              else
                  error "don't know how to apply %1", sh
              end if;
           end proc;

           export ModuleApply := proc(dom :: Domain_mb, e, $)
             local vs, sh;
             if dom :: DomNoSol then
                 error "cannot apply %1", dom;
             end if;

             vs, sh := op(dom);

             # This 'simplification' removes redundant information, but it is
             # entirely pointless as the result should be the same anyways. This
             # is mainly here as an assertion that Apply properly
             # re-applies integrals when the domain shape does not explicitly
             # state them.
             sh := subsindets( sh, DomInto
                             , proc (x, $)
                                   local x_vn, x_t0, x_rest, x_t, x_mk;
                                   x_vn, x_t0, x_rest := op(x);
                                   x_t, x_mk := Domain:-Bound:-get(vs, x_vn);
                                   if x_t = x_t0 then
                                       x_rest
                                   else
                                       x
                                   end if;
                              end proc );

             do_apply({}, e, vs, sh);
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
                     proc(sol :: set({relation,boolean}), v, ctx, $)
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
                             subsindets( ctx, DomConstrain
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
                        ctx := classifySol1(op(v), ctx);
                    end do;

                    ctx;
                 end proc; end proc;

                 # transforms the solution to the form required by Domain
                 # this would be a straightforward syntactic manipulation,
                 # but for the facts that we have to:
                 #  decide the order of integration
                 #  decide which solutions become integrations and which
                 #     become constrains
                 local postproc := proc(sol, ctx, $)
                   local ret := sol, vs;

                   ret := subsindets(ret, specfunc('piecewise')
                                    , x-> DSplit(Partition:-PWToPartition(x)));

                   ret := subsindets(ret
                                    , Or(identical({}), set(list))
                                    , x -> DSum(op(x)) );

                   vs := Domain:-Bound:-varsOf(ctx);

                 # `true' (produced by LMS for trivial systems) - to the
                 #    interval for the variable corresponding to this index in
                 #    the sequence.
                 # `c : name' - to the interval for `v'
                 # everything else - to itself
                   ret := subsindets(ret, list(set({relation,boolean, name}))
                                    , classifySols(vs, ctx) @
                                      (ls->map(si->remove(x->x::identical(true) or x::name, si), ls))
                                     );

                   ret;
                 end proc;

                 # ask Maple for a solution to our system
                 local do_LMS := proc( sh, ctx, $ )
                   local vs := Domain:-Bound:-varsOf(ctx)
                       , cs, do_rn, ret;
                   cs, do_rn := op(Domain:-Bound:-toKB(ctx, KB:-empty)) ;

                   cs := do_rn(proc(cs_,$)
                            local cs := cs_;
                            if sh :: DomConstrain then
                                cs := KB:-build_kb([op(sh)], "do_LMS", cs);
                            else
                                error "don't know how to solve %1", sh;
                            end if;

                            cs := op(3, KB:-kb_extract(cs));
                            cs := {op(cs)}; cs;
                               end proc , cs);

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

                    sol := do_LMS( dshape , dbnds );
                    if sol :: DomNoSol then return sol end if;

                    sol := postproc(sol, dbnds );
                    DOMAIN( dbnds, sol );
                 end proc;

                 end module);

           end proc;

           # TODO: this should keep errors (esp. if everything fails to
           # simplify), or print them as a warning(?)
           local cmp_simp := proc(s0, s1, $) proc(dom :: Domain_mb , $)
                                                 ::Domain_mb;
              local dom1 := s0(dom), r;
              if not dom1 :: DomNoSol then
                  s1(dom1);
              else
                  r := s1(dom);
                  if r :: DomNoSol then
                      r := op(0, r)( dom1, op(r) );
                  end if;
                  r
              end if;
           end proc; end proc;

           export ModuleApply := proc(dom :: Domain, $)::Domain_mb;
               local es := entries(Simplifiers)
                   , mk := foldr( cmp_simp , (_->_), op(es) );
               mk(dom);
           end proc;
    end module;

    uses Hakaru, Partition, SolveTools[Inequality] ;

end module;
