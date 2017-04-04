export Improve := module ()
    export Simplifiers := table();
    export ModuleApply := proc(dom :: HDomain, $)::HDomain_mb;
        local es := map(si->Simplifiers[si]:-DO
                       , sort( [indices(Domain:-Improve:-Simplifiers,nolist) ]
                             , key=(si->Simplifiers[si]:-Order)));
        foldr(cmp_simp , (_->_), op(es))(dom);
    end proc;

# our simplifiers
$include "Domain/Improve/LMS.mpl"
$include "Domain/Improve/redundant_DIntos.mpl"
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
