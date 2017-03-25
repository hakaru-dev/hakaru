Domain := module()

#   Domain = DOMAIN(DomBound, DomShape)
#   DomBound = DOMBOUND(list(name), KB)
#   DomShape =
#     | DConstrain(relation*)
#     | DSum (DomShape*)
#     | DSplit(Partition(DomShape))
#     | DInto(name, BoundType, DomShape)

    export DOMAIN := proc() 'procname'(_passed) end proc;
    export DBound := proc() 'procname'(_passed) end proc;

    export DConstrain := proc() 'procname'(_passed) end proc;
    export DSum := proc() 'procname'(_passed) end proc;
    export DSplit := proc() 'procname'(_passed) end proc;
    export DInto := proc() 'procname'(_passed) end proc;

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

    export ToKB := module ()

       export Bound := proc(dom, $)
         op(2, dom);
       end proc;

       export Shape := module ()
         export AsConstraints := proc(dom, $)
           {} # TODO
         end proc;

         export ModuleApply := proc(dom, $)
           build_kb(AsConstraints(dom), "Domain/ToKB/Shape");
         end proc;

       end module;

       export ModuleApply := proc(dom, $)
          build_kb(AsConstraints(op(2,dom)), "Domain/ToKB", Bound(op(1,dom)));
       end proc;
    end module;

    export ExtBound := table();
    export ExtShape := table();


    local ModuleLoad := proc($)
           ExtBound[`Int`] :=
               Record('MakeKB'=(e -> kb -> genLebesgue(op([1],e), op([2,1],e), op([2,2],e), kb))
                     ,'MakeEqn'=`=`
                     ,'MapleType'='And(specfunc({Int}), anyfunc(anything,name=range))'
                     ,'HType'=AlmostEveryReal
                     ,'RangeOf'=
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


    export Extract := module ()

           export MakeOfType := module()
              local makeTable := proc()
                 table([seq(apply(rhs=lhs,e),e=indices(ExtBound,'nolist'))]);
              end proc;

              export ModuleApply := proc(t, $)
                 makeTable()[op(0,t)];
              end proc;
           end module;

           export Bound := module ()
             local do_extract_arg := proc(kb1_, kb, vars, kind, arg_, bound, $)
               local kb1 := kb1_, x0, x, vars1, ty, arg := arg_;

               x0 := op(1, bound);
               x, kb1 := ExtBound[kind]:-MakeKB(bound)(kb1);

               vars1 := [ x, op(vars) ];
               arg   := subs(ExtBound[kind]:-MakeEqn(x0,x), arg);

               do_extract(kb1, kb, vars1, arg);
             end proc;

             local do_extract := proc(kb1_, kb, vars, arg, $)

               if Domain:-Has:-Bound(arg) then
                   do_extract_arg(kb1, kb, vars1, op(0,arg), op(arg));
               else
                   arg, vars1, kb1
               end if;

             end proc;

             export ModuleApply := proc(e, {ctx := empty}, $)
                        local arg, vars, kb;
                        arg, vars, kb := do_extract(ctx, ctx, [], e);

                        arg, Domain:-DBound(vars, kb);
             end proc;
           end module;



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

             local do_gets := proc(todo, w, e, $)
                       local t0, ts, w1, e1;
                       if nops(todo) = 0 then
                           w, e
                       else
                           t0, ts := op(todo);
                           if indets(e, specfunc(t0)) <> {} then
                               w1, e1 :=
                                 do_get(ExtShape[t0]:-MakeCtx
                                       ,ExtShape[t0]:-MapleType
                                       )(e);
                               do_gets( [ ts, t0 ], w, e1 );
                           else
                               do_gets( [ ts ], w, e );
                           end if;
                       end if;
             end proc;

             local simpl_shape := (x->x);

             export ModuleApply := proc(e, $)
                        local ixs, w, e1;
                        ixs := indices(ExtShape, 'nolist');
                        w, e1 := do_gets(ixs, e);

                        w := Domain:-DConstrain(op(w));
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



    export Apply := module ()
           local do_mk := proc(e, vn, ty, $)
              local mk, rng;

              mk := Extract:-MakeOfType(ty);
              rng := Extract:-ExtBound[mk]:-RangeOf(ty);
              rng := Extract:-ExtBound[mk]:-MakeEqn(vn, rng);

              mk(e, rng);
           end proc;

           local get_subdom := proc(vn, vs_ty)
                  local vn_ty, ty;
                  vn_ty := op(0, vs_ty)( KB:-getType(vs_ty, vn) );
                  ty := op([1,2], vn_ty);

                  ty, vn_ty
           end proc;

           local do_apply := proc(e, vs, vs_ty, sh_, kb, $)
              local sh := sh_, e1, vn, vt, shv, ty, vn_ty, kb1;
              if sh :: specfunc('DConstrain') then
                  foldr(`*`, e, op( map(c->Indicator(c), sh) ));

              elif sh :: specfunc('DSum') then
                  `+`(seq(do_apply(e, vs, vs_ty, s, kb), s=op(sh)))

              elif sh :: specfunc('DSplit') then
                  sh := op(1, sh);
                  Partition:-Pmap(p-> do_apply(e, vs, vs_ty, p, kb), sh);

              elif sh :: specfunc('DInto') then
                  # deconstruction
                  vn, vt, shv := op(sh);
                  ty, vn_ty := get_subdom(vn, vs_ty);

                  # this solution is added to the recursive call
                  kb1 := KB:-assert(vn :: vt, kb);

                  # recursively apply
                  e1 := do_apply(e, [vn], vn_ty, shv, kb1);

                  # build this integral
                  do_mk(e1, vn, ty);
              else
                  error "don't know how to apply %1", sh
              end if;
           end proc;

           export ModuleApply := proc(e, dom, kb, $)
             local vs, sh, vs_ty, vn, e1, ty, _;
             vs, sh := op(dom);
             vs, vs_ty := op(vs);

             e1 := do_apply(e, vs, vs_ty, sh, kb);

             for vn in vs do
                 ty, _ := get_subdom(vn, vs_ty);
                 e1 := subsindets(e1, Not(freeof(vn))
                                 ,x -> do_mk(x, vn, ty));
             end do;

             e1;
           end proc;
    end module;

    export Improve := module ()
           export Simplifiers := table();

           export ModuleLoad := proc($)

             Simplifiers[`LMS`] := (
                 module()

                   local countVs := vs -> (c-> nops(indets(c, name) intersect {op(vs)} ));

                   local orderSols := proc(sol,vs,$)
                     local sol2, solOrder ;

                     # sort the conjs by the number of variables which they mention
                     sol2, solOrder :=
                               sort( sol, key= (x-> -(countVs(vs)(x)))
                                   , output=[sorted,permutation]
                                   );

                   end proc;

                   local classifySol1 :=
                     proc(v0, vs_ty, sol :: set({relation,boolean}), $)
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

                             {}, (ctx-> Domain:-DInto(v, v_t, ctx));
                         else
                             sol, (x->x);
                         end if;
                 end proc;

                 local classifySols := proc(vs, vs_ty, $) proc( sol :: list(set({relation,boolean})), $ )
                    local sol1, ctx, dmk, s, solOrd, vso;
                    sol1, solOrd := orderSols(sol);
                    vso := vs[solOrd];

                    sol1 := zip(proc(s,v,$) classifySol1(v, vs_ty, s) end proc, sol1, vso);

                    ctx := {}; dmk := (x->x);
                    for s in sol1 do
                        ctx := ctx union op(1,s);
                        dmk := op(2,s) @ dmk;
                    end do;

                    dmk(Domain:-DConstrain(op(ctx)));
                 end proc; end proc;

                 local postproc := proc(sol, vs, vs_ty, $)
                   local ret := sol;

                   ret := subsindets(ret, specfunc('piecewise')
                                    , x-> Domain:-DSplit(Partition:-PWToPartition(x)));

                   ret := subsindets(ret, list(set({relation,boolean}))
                                    , classifySols(vs, vs_ty) );

                   ret := subsindets(ret
                                    , Or(identical({}), set(list))
                                    , x -> Domain:-DSum(op(x)) );


                   ret;
                 end proc;

                 local do_LMS := proc( ctx, vs_, $ )
                   local vs := vs_, cs, ret;

                   cs := op(1, kb_extract(ctx));
                   cs := {op(cs)};

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

                   ret;
                 end proc;

                 export ModuleApply := proc(dom, $)
                    local dbnds, dshape, db_vars, db_ctx, sol;
                    dbnds, dshape := op(dom);
                    db_vars, db_ctx := op(dbnds);

                    sol := do_LMS( ToKB(dom), db_vars );
                    postproc(sol, db_Vars, db_ctx);

                 end proc;

                 end module);

           end proc;

           local cmp_simp := proc(s0, s1, $) proc(dom, $)
              local dom1 := s0(dom);
              if not dom1 :: DNoSol then
                  s1(dom1);
              else
                  s1(dom);
              end if;
           end proc; end proc;

           export ModuleApply := proc(dom, $)
               foldr(cmp_smpl, (x->x), entries(Simplifiers))(dom);
           end proc;
    end module;

    uses Hakaru, KB, Partition;

end module;



  # app_dom_spec_IntSum :=
  #   proc(mk :: identical(Int, Sum), ee, h, kb0 :: t_kb
  #       ,dom_spec_
  #       ,$)
  #   local new_rng, make, var, elim, w,
  #         dom_spec := dom_spec_, e := ee ;

  #   new_rng, dom_spec := selectremove(type, dom_spec,
  #     {`if`(mk=Int, [identical(genLebesgue), name, anything, anything], NULL),
  #      `if`(mk=Sum, [identical(genType), name, specfunc(HInt)], NULL),
  #      [identical(genLet), name, anything]});
  #   if not (new_rng :: [list]) then
  #     error "kb_subtract should return exactly one gen*"
  #   end if;
  #   make    := mk;
  #   new_rng := op(new_rng);
  #   var     := op(2,new_rng);
  #   if op(1,new_rng) = genLebesgue then
  #     new_rng := op(3,new_rng)..op(4,new_rng);
  #   elif op(1,new_rng) = genType then
  #     new_rng := range_of_HInt(op(3,new_rng));
  #   else # op(1,new_rng) = genLet
  #     if mk=Int then
  #         # this was just a return, but now is in its own
  #         # local function and the control flow must be handled
  #         # up above. although calling 'reduce' on 0 will probably
  #         # return immediately anyways(?)
  #         return DONE(0)
  #     else
  #         make := eval;
  #         new_rng := op(3,new_rng)
  #     end if;
  #   end if;

  #   userinfo(3, 'LMS',
  #       printf("    dom-spec        : %a\n"
  #              "    dom-var         : %a\n"
  #        , dom_spec, var ));

  #   e := `*`(e, op(map(proc(a::[identical(assert),anything], $)
  #                        Indicator(op(2,a))
  #                      end proc,
  #                      dom_spec)));

  #   userinfo(3, 'LMS',
  #       printf("    expr-ind        : %a\n"
  #        , e ));

  #   elim := elim_intsum(make(e, var=new_rng), h, kb0);

  #   userinfo(3, 'LMS',
  #       printf("    expr-elimed     : %a\n"
  #        , elim ));

  #   if elim = FAIL then
  #     DONE( reduce_on_prod(p->make(p,var=new_rng), e, var, kb0) );
  #   else
  #     elim
  #   end if;

  # end proc;

  # do_app_dom_spec := proc(mk, e, h, kb0, kb2)
  #     local e2, dom_spec;

  #     dom_spec := kb_subtract(kb2, kb0);

  #     # apply the domain restrictions, which can produce
  #     #   DONE(x) - produced something which can't be simplified further
  #     #   x       - more work to be done
  #     e2 := app_dom_spec_IntSum(mk, e, h, kb0, dom_spec);

  #     userinfo(3, 'LMS',
  #              printf("    expr            : %a\n"
  #                     "    expr after dom  : %a\n"
  #                     , e, e2 ));

  #     if e2 :: specfunc('DONE') then
  #         e2 := op(1,e2);
  #     else
  #         e2 := reduce(e2, h, kb0);
  #         userinfo(3, 'LMS',
  #                  printf("    expr-reduced    : %a\n"
  #                         , e2 ));
  #     end if;

  #     e2;

  # end proc;






    # end if;

    # if e :: 'And(specfunc({Int,Sum}), anyfunc(anything,name=range))' then
    # userinfo(3, 'disint_trace',
    #     printf("case Int/Sum \n"
    #            "  expr : %a\n"
    #            "  h    : %a\n"
    #            "  ctx  : %a\n\n"
    #      , ee, h, kb ));

    #   x, kb1 := `if`(op(0,e)=Int,
    #     genLebesgue(op([2,1],e), op([2,2,1],e), op([2,2,2],e), kb),
    #     genSummation(op([2,1],e), op(op([2,2],e)), kb));
    #   reduce_IntSum(op(0,e),
    #     reduce(subs(op([2,1],e)=x, op(1,e)), h, kb1), h, kb1, kb)








  # reduce_IntSum := proc(mks, h :: name, dom_specw, kb1 :: t_kb, kb0 :: t_kb, $)
  #   local dom_spec, kb2, lmss, vs; # , e2, e3, _;


  #   # if there are domain restrictions, try to apply them
  #   # (dom_specw, e) := getDomainSpec(ee);

  #   kb2 := foldr(assert, kb1, op(dom_specw));

  #   if kb2 :: t_not_a_kb then
  #       error "not a kb: %1 + %2", dom_specw, kb1;
  #   end if;

  #   # userinfo(3, 'disint_trace',
  #   #     printf("reduce_IntSum input:\n"
  #   #            "  integral type: %a\n"
  #   #            "  expr : %a\n"
  #   #            "  h    : %a\n"
  #   #            "  ctx expr  : %a\n"
  #   #            "  ctx above : %a\n"
  #   #            "  ctx below : %a\n\n"
  #   #      , mks, ee, h, kb2, kb1, kb0 ));

  #   lmss := kb_LMS(kb2, mks);

  #   # userinfo(3, 'LMS',
  #   #      printf("    LMS     : %a\n"
  #   #             "    kb Big  : %a\n"
  #   #             "    kb small: %a\n"
  #   #             "    domain  : %a\n"
  #   #             "    var     : %a\n"
  #   #      , lmss, kb2, kb0, dom_spec, h ));

