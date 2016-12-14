#This module implements `Partition`---Hakaru's replacement for Maple's 
#endogenous and unwieldy `piecewise`.

#The outer data structure for a Partition is a function, PARTITION(...), (just like it
#is for piecewise.

Partition:= module()
#This module is essentially an object, but we decided, for now at least, to not
#use Maple's "option object".
local
   #The object's (internal) constructor. This just checks the argument types and
   #returns unevaluated.
   PARTITION::static:= proc(
      Pairs::set(
         record(
            #The type `anything` below should be some boolean type, but we'll 
            #need to write our own as neither Maple's 'boolean' nor
            #'boolean &under (convert, boolean_operator)' is inclusive enough. 
            cond::anything,
            val::t_Hakaru
            #Is that inclusive enough?
         )
      ),
      $ #no optional arguments, for now at least
   )::specfunc(procname);
     'procname'(_passed)
   end proc,

   ModuleLoad:= proc()
      :-`print/PARTITION`:= proc(SetOfRecords)
      local branch;
         #Don't know why `print/` is needed below. I hoped simply %piecewise(...) would
         #work.
         `print/%piecewise`(
            seq([eval(branch):-cond, eval(branch):-val][], branch= SetOfRecords)
            #I don't know why the eval's are needed above; they aren't in non-print
            #procedures.
         )
      end proc
   end proc
;
export
   #This is the exported lazy-syntax constructor.
   ModuleApply::static:= proc(Pairs::seq([anything, t_Hakaru]))
      ::specfunc(PARTITION);
   local pair, s;
      s:= {seq(Record('cond'= pair[1], 'val'= pair[2]), pair= [Pairs])};
      userinfo(3, PARTITION, s); 
      PARTITION(s)
   end proc, 

   #This is just `map` for Partitions.
   Pmap::static:= proc(
      f::anything #`appliable` not inclusive enough. 
      #Allow additional args, just like `map`
   )::specfunc(PARTITION);
   local pair,pos;
      if procname::indexed then
         pos:= op(procname);
         if not [pos]::[posint] then
            error "Expected positive integer index; received %1", [pos]
         end if
      else
         pos:= 1
      end if;
      if nargs <= pos then
         error "Expected at least %1 arguments; received %2", pos+1, nargs
      end if;
      if not args[pos+1]::specfunc(PARTITION) then
         error "Expected a Partition; received %1", args[pos+1]
      end if;         
      PARTITION(
         {seq(
            Record(
               'cond'= pair:-cond,
               'val'= f(args[2..pos], pair:-val, args[pos+2..])
            ),
            pair= op(args[pos+1])
         )}
      )
   end proc
;
   ModuleLoad()
end module: 
