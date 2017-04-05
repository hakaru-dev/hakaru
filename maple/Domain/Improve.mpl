export Improve := module ()
    export Simplifiers := table();
    export ModuleApply := proc(dom :: HDomain, $)::HDomain_mb;
        local es := map(si->Simplifiers[si]:-DO
                       , sort( [indices(Domain:-Improve:-Simplifiers,nolist) ]
                             , key=(si->Simplifiers[si]:-Order)))
             , bnd, sh;
        bnd, sh := op([1..2], dom);
        sh := foldr(cmp_simp_sh, (proc(_,b,$) b end proc), op(es))(bnd, sh);
        DOMAIN(bnd, sh);
    end proc;

# our simplifiers
$include "Domain/Improve/LMS.mpl"
$include "Domain/Improve/redundant_DIntos.mpl"
$include "Domain/Improve/constraints_about_vars.mpl"
$include "Domain/Improve/singular_pts.mpl"
$include "Domain/Improve/single_case_Partition.mpl"

    export ModuleLoad := proc($)
        unprotect(Domain:-Improve:-Simplifiers):
        Simplifiers["Push context down"] :=
             Record('Order'=1
                   ,'DO'=Domain:-Improve:-push_ctx_down);
        Simplifiers["Obviously redundant 'DInto's"] :=
             Record('Order'=2
                   ,'DO'=Domain:-Improve:-redundant_DIntos);
        Simplifiers["Make constraints abouts vars"] :=
             Record('Order'=6
                   ,'DO'=Domain:-Improve:-constraints_about_vars);
        Simplifiers["LMS"] :=
             Record('Order'=10
                   ,'DO'=evaln(Domain:-Improve:-LMS));
        Simplifiers["Single case partition"] :=
             Record('Order'=11
                   ,'DO'=Domain:-Improve:-single_case_Partition);
        Simplifiers["Single_pts"] :=
             Record('Order'=14
                   ,'DO'=Domain:-Improve:-singular_pts);
        Simplifiers["Pull context out"] :=
             Record('Order'=20
                   ,'DO'=Domain:-Improve:-pull_ctx_out);
        # protect(Domain:-Improve:-Simplifiers):
    end proc;#ModuleLoad

    local combine_errs := proc(err::DomNoSol, mb, $)
        if mb :: DomNoSol then
            DNoSol(op(err),op(mb));
        else
            mb
        end if;
    end proc;

    # compose two simplifiers, combining errors if both fail
    local cmp_simp_sh :=
        proc(simp0, simp1, $)
        proc(bnd, sh :: {DomShape,DomNoSol}, $)::{DomShape,DomNoSol};
            local res, sh1; sh1 := simp0(bnd, sh);
            if not sh1 :: DomNoSol then
                res := simp1(bnd, sh1); res;
            else
                res := combine_errs( sh1, simp1(bnd, sh) ); res;
            end if;
    end proc end proc;
end module;
