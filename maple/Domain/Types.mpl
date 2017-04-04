# Domain types which are registered/unregistered with TypeTools.
# Note that the types have to be quoted (additionally to the quote one would
# normally place on certain types) to work properly
local DomainTypes := table(
       # Domain bounds
       [(DomBoundVar = 'DomBoundVar_type')
       ,(DomBoundRange = 'DomBoundRange_type')
       ,(DomBoundBinder = ''DInto(DomBoundVar, DomBoundRange, DomBoundKind)'' )
       ,(DomBoundKind   = 'And(name, satisfies(nm->assigned(Domain:-ExtBound[nm])))' )
       ,(DomBound       = ''Or(DBound(list(DomBoundBinder))
                              ,DBound(list(DomBoundBinder),anything) )'' )
       # Domain shape
       ,(DomConstrain = 'specfunc(relation, `DConstrain`)' )
       ,(DomSum       = 'specfunc(DomShape, `DSum`)' )
       ,(DomSplit     = ''DSplit(Partition(DomShape))'' )
       ,(DomInto      = ''Or(DInto(DomBoundVar, DomBoundRange, DomShape)
                            ,DInto(DomBoundVar, DomShape) )'' )
       ,(DomShape     = 'Or( DomConstrain, DomSum, DomSplit, DomInto )' )
       # Domain
       ,(DomCtx = ''set({relation, `::`})'')
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

local GLOBALS := table(
  ['DOMAIN' =
   (proc()
      local errs := indets([args[2..-1]], DomNoSol);
      if errs <> {} then
          'procname'(args[1], 'DNoSol'(map(op,errs)[]));
      end if;
      'procname'(args);
    end proc)
 , 'DConstrain' =
   (proc()
     local as := {args};
     if false in as then return DSum() end if;
     as := remove(x->x::identical(false),as);
     'procname'(op(as));
   end proc)
 , 'DSum' =
   (proc()
     local as := [args];
     as := subsindets(as, specfunc(`DSum`), xs->
           subsindets(xs, specfunc(`DSum`), op));
     if nops(as) = 1 then return op(1,as) end if;
     'procname'(op(as));
   end proc) ]);
