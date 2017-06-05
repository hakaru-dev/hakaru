# Domain types which are registered/unregistered with TypeTools.
# Note that the types have to be quoted (additionally to the quote one would
# normally place on certain types) to work properly
local DomainTypes := table(
       # Domain bounds
       [(DomBoundVar = 'DomBoundVar_type')
       ,(DomBoundRange = 'DomBoundRange_type')
       ,(DomBoundBinder = ''DInto(DomBoundVar, DomBoundRange, DomBoundKind)'' )
       ,(DomBoundKind   = 'And(name, satisfies(nm->assigned(Domain:-ExtBound[nm])))' )
       ,(DomBound       = ''And(specfunc(DBound)
                               ,{anyfunc(list(DomBoundBinder))
                                ,anyfunc(list(DomBoundBinder),DomCtx)
                                ,anyfunc(list(DomBoundBinder),DomCtx,table) })'' )
       # Domain shape
       ,(DomConstrain = 'specfunc(relation, `DConstrain`)' )
       ,(DomSum       = 'specfunc(DomShape, `DSum`)' )
       ,(DomSplit     = ''DSplit(Partition(DomShape))'' )
       ,(DomInto      = ''Or(DInto(DomBoundVar, DomBoundRange, DomShape)
                            ,DInto(DomBoundVar, DomShape) )'' )
       ,(DomShape     = 'Or( DomConstrain, DomSum, DomSplit, DomInto )' )
       # Domain
       ,(DomCtx = ''t_kb'')
       ,(HDomain = ''DOMAIN(DomBound, DomShape)'' )
       # Maybe domain
       ,(DomNoSol  = ''Not(freeof(`DNoSol`))'' )
       ,(HDomain_mb = ''Or(HDomain, DOMAIN(DomBound, DomNoSol))'' )
       ] );

local DomBoundVar_type := proc(nm)
    local ixs := [indices(Domain:-ExtBound, nolist)], vs;
    ormap(i->type(nm,Domain:-ExtBound[i]:-VarType), ixs);
end proc;

local DomBoundRange_type := proc(nm)
    local ixs := [indices(Domain:-ExtBound, nolist)], vs;
    ormap(i->type(nm,Domain:-ExtBound[i]:-RangeType), ixs);
end proc;
