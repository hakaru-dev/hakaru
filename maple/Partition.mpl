#This module implements `Partition`---Hakaru's replacement for Maple's 
#endogenous and unwieldy `piecewise`.

#The outer data structure for a Partition is a function, just like it is for 
#piecewise.

Partition:= module()
#This module is essentially an object, but we decided, for now at least, to not
#use Maple's "option object".
local
   #The object's (internal) constructor
   Partition::static:= proc(
      Pairs::set(
         record(
            #The type `anything` below should be some boolean type, but we'll 
            #need to write our own as neither Maple's 'boolean' nor
            #'boolean &under (convert, boolean_operator)' is inclusive enough. 
            cond::anything,
            val::t_Hakaru
            #Is that inclusive enough?
         )
      )
   )::specfunc('Partition');
     'procname'(_passed)
  end proc
;
export
   #This is the exported lazy-syntax constructor.
   ModuleApply::static:= proc(Pairs::seq([anything, t_Hakaru]))
      ::specfunc('Partition');
   local pair;
      Partition({seq(Record('cond'= pair[1], 'val'= pair[2]), pair= [Pairs])})
   end proc, 

   #This is just `map` for Partitions.
   Pmap::static:= proc(
      f::appliable
      #Allow additional args, just like `map`
   )::specfunc('Partition');
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
      if not args[pos+1]::specfunc('Partition') then
         error "Expected a Partition; received %1", args[pos+1]
      end if;         
      Partition(
         {seq(
            Record(
               'cond'= pair:-cond,
               'val'= f(args[2..pos], pair:-val, args[pos+2..])
            ),
            pair= args[pos+1]
         )}
      )
   end proc
;
end module: 
