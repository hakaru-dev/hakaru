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
   )::Partition;
     'procname'(_passed)
   end proc,

   ModuleLoad::static:= proc()
      :-`print/PARTITION`:= proc(SetOfRecords)
      local branch;
         `print/%piecewise`(
            seq([eval(branch):-cond, eval(branch):-val][], branch= SetOfRecords)
         )
      end proc;

      TypeTools:-AddType(Partition, specfunc(PARTITION));
      NULL
   end proc,

   ModuleUnload::static:= proc()
      TypeTools:-RemoveType(Partition);
      NULL
   end proc,

   # abstract out all argument checking for map-like functions
   map_check := proc(p)
      local pos, err;
      if p::indexed then
         pos:= op(p);
         if not [pos]::[posint] then
            err := sprintf("Expected positive integer index; received %a", [pos]);
            return err;
         end if
      else
         pos:= 1
      end if;
      if nargs-1 <= pos then
         err := sprintf("Expected at least %d arguments; received %d", pos+1, nargs-1);
         return err;
      end if;
      if not args[pos+2]::Partition then
         err := sprintf("Expected a Partition; received %a", args[pos+2]);
         return err;
      end if;
      return pos;
   end proc
;
export
   #This is the exported lazy-syntax constructor. The syntax is like piecewise except
   #that there can be no 'otherwise'.
   ModuleApply::static:= proc(Terms::seq(anything))::Partition;
   local pair, s, Pairs, k;
      if nargs::odd then
         error "Expected an even number of arguments"
      end if;   
      s:= {seq(Record('cond'= Terms[k], 'val'= Terms[k+1]), k= 1..nargs-1, 2)};
      userinfo(3, PARTITION, s); 
      PARTITION(s)
   end proc, 

   #Deconstructor that returns just the conditions as a set
   Conditions::static:= proc(P::Partition)::set;
   local p;
      {seq(p:-cond, p= op(1,P))}
   end proc,

   #Deconstructor that returns a set of [cond, val] pairs
   Pairs:= proc(P::Partition)::set([anything, t_Hakaru]);
   local p;
      {seq([p:-cond, p:-val], p= op(1,P))}
   end proc,

   #This is just `map` for Partitions.
   Pmap::static:= proc(
      f::anything #`appliable` not inclusive enough. 
      #Allow additional args, just like `map`
   )::Partition;
   local pair,pos,res;
      res := map_check(procname, args);
      if res::string then error res else pos := res; end if;
      PARTITION(
         {seq(
            Record(
               'cond'= pair:-cond,
               'val'= f(args[2..pos], pair:-val, args[pos+2..])
            ),
            pair= op(1, args[pos+1])
         )}
      )
   end proc,

   # a more complex mapping combinator which works on all 3 parts
   # not fully general, but made to work with KB
   # also, does not handle extra arguments (on purpose!)
   Amap::static:= proc(
      funcs::[anything, anything, anything], #`appliable` not inclusive enough. 
      part::Partition
   )::Partition;
   local pair,pos,f,g,h,doIt;
      (f,g,h) := op(funcs);
      #sigh, we don't have a decent 'let', need to use a local proc
      doIt := proc(pair)
        local kb0 := h(pair:-cond); 
        Record('cond' = f(pair:-cond, kb0), 
               'val' = g(pair:-val, kb0));
      end proc;
      PARTITION(map(doIt,op(1,part)));
   end proc,

   #Check whether the conditions of a Partition depend on any of a set of names.
   ConditionsDepend:= proc(P::Partition, V::{name, list(name), set(name)}, $)
   local p;
      for p in op(1,P) do if depends(p:-cond, V) then return true end if end do;
      false
   end proc
;
   ModuleLoad()
end module: 
