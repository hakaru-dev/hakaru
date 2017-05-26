export Shape := module ()
    uses Domain_Type;
    export toConstraints := proc(sh_ :: DomShape, $)
           ::specfunc({boolean,relation,specfunc(`Or`)}, `And`);
        local sh := sh_;
        if sh :: specfunc(`DConstrain`) then
            And( op(sh) );
        elif sh :: specfunc(`DSum`) then
            sh := Or(op(map(toConstraints, sh)));
            Domain:-simpl_relation(sh, norty='CNF');
        elif sh :: specfunc(`DInto`) then
            toConstraints(op(3, sh));
        else
            error "don't know how to convert to constraints %1", sh
        end if;
    end proc;
end module;
