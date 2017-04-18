LMS := module()
    uses SolveTools[Inequality];
    # export SimplName  := "LMS";
    export SimplOrder := 6+(1/2);

    # We use the opposite "integration order" than LMS, so
    # reverse the variables. The scare quotes are because LMS
    # knows nothing about domains or integration, but it does
    # try to place the first variable "outermost" (probably
    # because it solves for each variable one by one, at starts
    # at the left) which will flip things around for no reason.
    export ModuleApply := proc(dbnds :: DomBound, dshape :: DomShape, $)
        local vs;
        vs := ListTools[Reverse](Domain:-Bound:-varsOf(dbnds));
        vs := map(v->if v::list then op(1,v) else v end if, vs);
        do_LMS( dshape , dbnds, vs );
    end proc;

    # transforms the solution to the form required by Domain
    # this is (now) a straightforward syntactic manipulation,
    local postproc := proc(sol, $)
      foldl((x,k)->subsindets(x,op(k)), sol
           ,[specfunc('piecewise')
            ,x->DSplit(Partition:-PWToPartition(x, 'do_solve'))]
           ,[Or(identical({}), set(list))
            ,x -> DSum(op(x))]
           ,[list(set({relation,boolean, name}))
            ,x -> DConstrain(indets(x,{relation,boolean})[])]
           ,['[DomShape]',op]);
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
            if sol :: DomShape then sol
            else postproc(sol) end if;
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
        if nops(ctx) >= 2 then
          # LMS doesn't understand constraints (those are excluded by default
          # in Bound:-toConstraints)
          cs := remove(x->not(x::{`<`,`<=`,`=`}), cs union op(2,ctx));
        end if;

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
