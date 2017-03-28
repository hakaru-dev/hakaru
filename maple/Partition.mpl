#This module implements `Partition`---Hakaru's replacement for Maple's
#endogenous and unwieldy `piecewise`.

#The outer data structure for a Partition is a function, PARTITION(...), (just like it
#is for piecewise.

Partition:= module()

option package;

#This module is essentially an object, but we decided, for now at least, to not
#use Maple's "option object".
local

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
      s:= [ seq(Record('cond'= Terms[k], 'val'= Terms[k+1]), k= 1..nargs-1, 2) ] ;
      userinfo(3, PARTITION, s);
      PARTITION(s)
   end proc,

   #Deconstructor that returns just the conditions as a set
   Conditions::static:= proc(P::Partition)::set;
   local p;
      {seq(p:-cond, p= op(1,P))}
   end proc,

   #Deconstructor that returns a set of [cond, val] pairs
   Pairs:= proc(P::Partition)::set([anything, anything]);
   local p;
      {seq([p:-cond, p:-val], p= op(1,P)) }
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
         [seq(
            Record(
               'cond'= pair:-cond,
               'val'= f(args[2..pos], pair:-val, args[pos+2..])
            ),
            pair= op(1, args[pos+1])
         )]
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

   PartitionToPW := proc(x::Partition)::specfunc(piecewise);
       # piecewise can reduce immediately to not-piecewise which makes the type
       # test fail
       'piecewise'( op( ListTools[Flatten]( [ seq([p:-cond, p:-val], p= op(1,x)) ] ) ) );
   end proc,

   # convert a piecewise to a partition, which is straightforward except:
   # - if any of the branches are unreachable, they are removed
   # - if the last clause is (implicitly) `otherwise`, that clause is filled in
   #     appropriately

   # note that if the piecewise does not cover the entire domain,
   #   then this Partition will be 'invalid' (in the sense that it also
   #   will not cover the entire domain) - the 'correct' thing to do would
   #   probably be to add a new clause whose value is 'undefined'

   # the logic of this function is already essentially implemented, by KB
   # in fact, kb_piecewise does something extremely similar to this
   PWToPartition := proc(x::specfunc(piecewise))::Partition;

       # each clause evaluated under the context so far,
       # which is the conjunction of the negations of all clauses
       # so far
       local ctx := empty, n := nops(x), cls := [], cnd_raw, cnd,i, q;

       userinfo(5, PWToPartition
               , printf("PWToPartition: found %d ops in %a \n ", n, x) );

       # handles all but the `otherwise` case if there is such a case
       for i in seq(q, q = 1 .. iquo(n, 2)) do

           userinfo(3, PWToPartition
                    , printf("PWToPartition: looking at clause %d (op %d) \n ", i, 2*i-1));

           cnd_raw := op(2*i-1,x); # the clause as given
           cnd := simplify_assuming_f( cnd_raw , ctx );

           # if this clause is unreachable, then every subsequent clause will be as well
           if kb_is_false( assert(cnd_raw, ctx) )
            or cnd :: identical(FAIL) then
               return PARTITION( cls );
           else
               ctx := assert(Not(cnd), ctx); # the context for the next clause

               userinfo(3, PWToPartition, printf("PWToPartition: ctx after %d clauses "
                                                 "is %a\n", i, ctx));

               cls := [ op(cls)
                      , Record('cond' = cnd
                              ,'val'  = op(2*i ,x)
                              )
                      ];
           end if;
       end do;

       # if there is an otherwise case, handle that.
       if n::odd and not kb_is_false(ctx) then

           cls := [ op(cls)
                  , Record('cond' = foldl(And,op(kb_to_assumptions(ctx)))
                          , 'val' = op(n,x)
                          )
                  ];
       end if;

       PARTITION( cls );

   end proc,


   # applies a function to the arg if arg::Partition,
   # and if arg::piecewise, then converts the piecewise to a partition,
   # applies the function, then converts back to piecewise
   # this mainly acts as a sanity check

   AppPartOrPw := proc(f::anything # TODO better type
                      ,x::Or(Partition,specfunc(piecewise))
                      )
       if x::Partition then
           f(x);
       else
           PartitionToPW(f(PWToPartition(x)));
       end if;
   end proc,

   #Check whether the conditions of a Partition depend on any of a set of names.
   ConditionsDepend:= proc(P::Partition, V::{name, list(name), set(name)}, $)
   local p;
      for p in op(1,P) do if depends(p:-cond, V) then return true end if end do;
      false
   end proc
;

uses Hakaru, KB;

   ModuleLoad()
end module:
