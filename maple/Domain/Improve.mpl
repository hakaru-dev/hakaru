export Improve := module ()
    export Simplifiers := table();
    export ModuleApply := proc(dom :: HDomain, $)::HDomain_mb;
        local es := map(si->Simplifiers[si]:-DO
                       , sort( [indices(Domain:-Improve:-Simplifiers,nolist) ]
                             , key=(si->Simplifiers[si]:-Order)));
        foldr(cmp_simp , (_->_), op(es))(dom);
    end proc;

    local LMS := module()
        export ModuleApply := proc(dom :: HDomain, $) :: HDomain_mb;
            local dbnds, dshape, sol, res, errs, vs;
            dbnds, dshape := op(dom);
            vs := Domain:-Bound:-varsOf(dbnds);
            # We use the opposite "integration order" than LMS, so
            # reverse the variables. The scare quotes are because LMS
            # knows nothing about domains or integration, but it does
            # try to place the first variable "outermost" (probably
            # because it solves for each variable one by one, at starts
            # at the left) which will flip things around for no reason.
            vs := ListTools[Reverse](vs);
            sol := do_LMS( dshape , dbnds, vs );
            errs := indets(sol, DomNoSol);
            if errs <> {} then return DNoSol(seq(op(e), e=errs)) end if;
            DOMAIN( dbnds, sol );
        end proc;

        local countVs := vs -> (c-> nops(indets(c, name) intersect {op(vs)} ));
        # Sorts the solutions so that resulting integrals are
        # well-scoped
        local orderSols := proc(sol,vs,$)
            local sol2, solOrder ;
            # sort the conjs by the number of variables which they mention
            sol2, solOrder :=
                      sort( sol, key= (x-> -(countVs(vs)(x)))
                          , output=[sorted,permutation]);
        end proc;

        # given a solution for a single variable,
        # either extracts upper and/or lower bounds from the solution
        # or leaves that solution as a constraint.
        local classifySol1 := proc(sol :: set({relation,boolean}), v, ctx, $)
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
                            , x-> DConstrain(op(x), op(sol)));
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
            end do; ctx;
        end proc; end proc;

        # transforms the solution to the form required by Domain
        # this would be a straightforward syntactic manipulation,
        # but for the facts that we have to:
        #  decide the order of integration
        #  decide which solutions become integrations and which
        #     become constrains
        local postproc := proc(sol, ctx, vs, $)
            local ret := sol;
            ret := subsindets(ret, specfunc('piecewise')
                             , x-> DSplit(Partition:-PWToPartition(x, 'do_solve')));
            ret := subsindets(ret
                             , Or(identical({}), set(list))
                             , x -> DSum(op(x)) );
            # vs := Domain:-Bound:-varsOf(ctx);
            # `true' (produced by LMS for trivial systems) - to the
            #    interval for the variable corresponding to this index in
            #    the sequence.
            # `c : name' - to the interval for `v'
            # everything else - to itself
            subsindets(ret, list(set({relation,boolean, name}))
                          , classifySols(vs, ctx) @
                            (ls->map(si->remove(x->x::identical(true) or x::name, si), ls)) );
        end proc;

        # Note this will not simplify solutions, in the sense that if
        # there are multiple places to apply LMS, the resulting
        # solution after applying LMS is not simplified any
        # further. This should probably be done by a seperate
        # simplifier.
        local do_LMS := proc( sh :: DomShape, ctx :: DomBound, vs, $)
            local sol;
            if sh :: DomConstrain then
                sol := do_LMS_Constrain(sh, ctx, vs);
                if sol :: DomShape then
                    sol
                else
                    postproc(sol, ctx, vs);
                end if;
            elif sh :: DomSplit then
                # todo: incorporate piece condition into context
                DSplit( Partition:-Pmap(p->do_LMS(p, ctx, vs), op(1, sh)) );
            elif sh :: DomSum then
                map(s->do_LMS(s, ctx, vs), sh);
            else
                DNoSol(sprintf("Don't know how to solve DOMAIN(%a, %a)", ctx, sh));
            end if;
        end proc;

        # ask Maple for a solution to our system
        local do_LMS_Constrain := proc( sh :: DomConstrain , ctx, vs_, $ )
            local vs := vs_, cs, do_rn, ret;
            cs := { op( Domain:-Bound:-toConstraints(ctx,'no_infinity') )
                  , op(sh) } ;
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
    end module;

    local redundant_DIntos := proc(dom, $)
        local vs, sh;
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
        DOMAIN(vs, sh);
    end proc;

$include "Domain/Improve/constraints_about_vars.mpl"
$include "Domain/Improve/singular_pts.mpl"

    export ModuleLoad := proc($)
        unprotect(Domain:-Improve:-Simplifiers):
        Simplifiers["Obviously redundant 'DInto's"] :=
             Record('Order'=2
                   ,'DO'=Domain:-Improve:-redundant_DIntos);
        Simplifiers["Make constraints abouts vars"] :=
             Record('Order'=6
                   ,'DO'=Domain:-Improve:-constraints_about_vars);
        Simplifiers["LMS"] :=
             Record('Order'=10
                   ,'DO'=evaln(Domain:-Improve:-LMS));
        Simplifiers["Single_pts"] :=
             Record('Order'=14
                   ,'DO'=Domain:-Improve:-singular_pts);
    end proc;#ModuleLoad

    local combine_errs := proc(e0 :: DomNoSol, e1 :: DomNoSol, $) :: DomNoSol;
       DNoSol( op(e0), op(e1) );
    end proc;
    # TODO: this should keep errors (esp. if everything fails to
    # simplify), or print them as a warning(?)
    local cmp_simp := proc(s0, s1, $) proc(dom :: HDomain_mb , $)::HDomain_mb;
       local dom1 := s0(dom), r;
       if not dom1 :: DomNoSol then
           s1(dom1);
       else
           r := s1(dom);
           if r :: DomNoSol then
               r := combine_errs( dom1, r );
           end if;
           r
       end if;
    end proc; end proc;
end module;
