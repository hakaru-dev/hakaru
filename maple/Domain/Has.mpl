# Checks if an expression has domain bounds/shape, and check for either one.
local Has := module ()
    export ModuleApply := proc(e, $)::truefalse;
        Bound(e) or Shape(e);
    end proc;

    export Bound := proc(e, $)::truefalse;
        assigned(Domain:-ExtBound[op(0,e)]) and
        evalb(e :: Domain:-ExtBound[op(0,e)]:-MapleType);
    end proc;

    export Shape := proc(e, $)::truefalse;
        assigned(Domain:-ExtShape[op(0,e)]) and
        evalb(e :: Domain:-ExtShape[op(0,e)]:-MapleType);
    end proc;
end module;
