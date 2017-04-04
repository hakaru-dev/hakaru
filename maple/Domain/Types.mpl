# Domain types which are registered/unregistered with TypeTools.
# Note that the types have to be quoted (additionally to the quote one would
# normally place on certain types) to work properly
local DomainTypes := table(
       # Domain bounds
       [(DomBoundBinder = ''DInto(name, range, DomBoundKind)'' )
       ,(DomBoundKind   = 'And(name, satisfies(nm->assigned(Domain:-ExtBound[nm])))' )
       ,(DomBound       = ''DBound(list(DomBoundBinder))'' )
       # Domain shape
       ,(DomConstrain = 'specfunc(relation, `DConstrain`)' )
       ,(DomSum       = 'specfunc(DomShape, `DSum`)' )
       ,(DomSplit     = ''DSplit(Partition(DomShape))'' )
       ,(DomInto      = ''DInto(name, range, DomShape)'' )
       ,(DomShape     = 'Or( DomConstrain, DomSum, DomSplit, DomInto )' )
       # Domain
       ,(HDomain = ''DOMAIN(DomBound, DomShape)'' )
       # Maybe domain
       ,(DomNoSol  = 'specfunc(`DNoSol`)' )
       ,(HDomain_mb = ''Or(HDomain, DomNoSol)'' )
       ] );

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
