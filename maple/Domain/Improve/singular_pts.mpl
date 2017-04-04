# todo; this should actually solve for a variable, then substitute
# that variable in. In most cases, it would probably be enough to
# leave that as it is; it would simplify later.
local singular_pts := module()
    export ModuleApply := proc(dom :: HDomain, $)
        local bnds, sh, vs, todo, sh1, vs_ty;
        bnds, sh := op(dom);
        vs := applyop(bl -> select(b->op(3,b)=`Int`, bl), 1, bnds);
        vs := Domain:-Bound:-varsOf(vs);
        vs_ty := satisfies(x->x in {op(vs)});
        todo := select( x -> nops(x) = 1 and op(1,x) :: `=`
                             # one side mentions exactly one
                             # var, and the other none
                             and nops ( (indets(lhs(op(1,x)), vs_ty))
                                  union (indets(rhs(op(1,x)), vs_ty)) ) = 1
                      , indets(sh, specfunc(`DConstrain`)) ) ;
        sh1 := subs([seq(t=DSum(),t=todo)], sh);
        DOMAIN(bnds, sh1);
    end proc;
end module;
