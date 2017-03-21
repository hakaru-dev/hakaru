#This module implements `Partition`---Hakaru's replacement for Maple's
#endogenous and unwieldy `piecewise`.

#The outer data structure for a Partition is a function, PARTITION(...), (just like it
#is for piecewise.


Partition:= module()

option package;

#This module is essentially an object, but we decided, for now at least, to not
#use Maple's "option object".

global Piece;

local
   diff_,

   Umap := proc(f,x,$)
       f(op(0,x))( map( p -> Piece(f(condOf(p)),f(valOf(p)))
                      , op(1,x)
                      )
                 )
   end proc,

   # could also be named
   # simplifyPartition_by_the_removal_of_particular_singular_points
   simplifyPartition_mergeSinglePts := module()
       local canSimp := c -> valOf(c) :: identical('undefined') and condOf(c) :: `=`
                                  and (lhs(condOf(c)) :: name or rhs(condOf(c)) :: name);

       local mentions_t_hi :=
                t -> bnd -> cl -> has(cl, t<bnd) or has(cl, bnd>t);

       local mentions_t_lo :=
                t -> bnd -> cl -> has(cl, bnd<t) or has(cl, t>bnd);

       local replace_with := t -> bnd -> x ->
                if mentions_t_hi(t)(bnd)(x) then
                    t <= bnd
                elif mentions_t_lo(t)(bnd)(x) then
                    t >= bnd
                else
                    x
                end if;

       local set_xor := proc(a,b,$) (a union b) intersect (a minus b) end proc;

       local tryReplacePieces :=
               proc(replPieces, otherPieces,cmp,$)
                 local rpp := replPieces, otp := otherPieces, nm, val, rp, rpv;

                 for rp in rpp do
                     rp, rpv := op(rp);

                     nm   := `if`(lhs(rp)::name, lhs(rp), rhs(rp));
                     val  := `if`(lhs(rp)::name, rhs(rp), lhs(rp));

                     otp := tryReplacePiece( nm, val, rpv, otp, cmp )
                 end do;

                 otp;

               end proc;

       local the_val := cmp -> xs ->
                evalb( foldl( proc(x,y) if cmp(x,y) then x else NULL end if; end proc, op(xs)) = NULL ) ;


       local tryReplacePiece :=
               proc(vrNm, vrVal, pc0val, pcs, cmp,$)
                 local pcs0 := pcs, pcs1, qs0, qs1, qs2, vrEq := vrNm=vrVal ;
                 pcs1 := subsindets(pcs0, relation, replace_with(vrNm)(vrVal));

                 qs0, qs1 := seq({op(qs)},qs=(pcs0,pcs1));

                 qs2 := set_xor(qs1, qs0);

                 if nops(qs2) = 2 then
                     qs2 := map(condOf, qs2);

                     if not pc0val :: identical('undefined') then
                         qs2 := { pc0val, op(qs2) };
                     end if;

                     qs2 := map(q -> subs(vrEq, q), qs2);

                     if the_val(cmp)(qs2) then
                         pcs1;
                     else
                         [ Piece(vrEq, pc0val), op(pcs0) ] ;
                     end if
                 else
                     [ Piece(vrEq, pc0val), op(pcs0) ] ;
                 end if;

               end proc;


       export ModuleApply := proc(p_,{cmp:=`=`},$)

          local p := p_, r := p, uc, oc;

          # if the partition contains case of the form `x = t', where `t' is a
          # constant (or term??) and `x' is a variable, and the value of that
          # case is `undefined', then we may be able to eliminate it (if another
          # case includes that point)
          r := op(1,r);
          uc, oc := selectremove(canSimp, r);

          # special case: if there is exactly one `undefined' case, and one
          # other case, just get rid of the `undefined' piece
          if nops(uc)=1 and nops(oc)=1 then
              p := PARTITION(oc);
          else
              p := PARTITION(tryReplacePieces(uc, oc, cmp));
          end if;

          return p;

       end proc;

   end module,

   ModuleLoad::static:= proc()
      local prev;

      :-`print/PARTITION`:= proc(SetOfRecords)
      local branch;
         `print/%piecewise`(
            seq([ condOf(eval(branch)), valOf(eval(branch))][], branch= SetOfRecords)
         )
      end proc;

      TypeTools:-AddType(Partition, specfunc(PARTITION));

      # global extensions to maple functionality

      :-`eval/PARTITION` :=
      proc(p, eqs, $)
          local q, r;
          q := Umap(x->eval(x,eqs), p);

          r := eval( PartitionToPW(q), eqs );
          if r :: specfunc('piecewise') then
              q := PWToPartition( r );
          else
              q := r;
          end if;

          q;

      end proc;

      :-`depends/PARTITION` :=
      proc(parts, nms, $)
         local dp := (x -> depends(x, nms));
         `or`(op ( map(p-> dp(condOf(p)) or dp(valOf(p)), parts) ));
      end proc;

      :-`diff/PARTITION` :=
      proc(parts, wrt, $)
          local pw  := PartitionToPW(PARTITION(parts))
              , dpw := diff(pw, wrt)
              , r   := PWToPartition(dpw)
              , r0, r1;
            ;
          r0 := simplifyPartition_mergeSinglePts(r);

          # probably a better way to do this; we really only want to simplify
          # sums and products of integrals and summations
          r1 := subsindets(r0, algebraic, `simplify`);

          userinfo(10, 'disint_trace',
                   printf("  input        : \n\t%a\n\n"
                          "  diff         : \n\t%a\n\n"
                          "  singular pts : \n\t%a\n\n"
                          "  simplified   : \n\t%a\n\n\n"
                          , parts, r, r0, r1 ));

          r1;
      end proc;

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
   end proc,

   simplifyPartitionCtx := proc(ctx, $)
       local ctxC := ctx;
       ctxC := solve({ctxC});
       if ctxC = NULL then
           ctxC := false;
       elif ctxC :: set then
           ctxC := remove(x -> x :: `=` and rhs(x)=lhs(x) and lhs(x) :: name, ctxC);
           if ctxC :: identical('{}') then
               ctxC := eval(ctx, [`And`=`and`, `Not`=`not`]);
           else
               ctxC := `and`(op(ctxC));
           end if ;

       # elif nops([ctxC])> 1 then
       #     ctxC := [ctxC];
       else
           error "simplifyPartitionCtx: don't know what to do with %1", ctxC;
       end if;

       if ctx :: identical(true) then
           error "simplifyPartitionCtx: don't know what to do with %1", ctxC;
       end if;

       ctxC;
   end proc
;
export

   condOf := proc(x::specfunc(`Piece`),$)
       op(1,x);
   end proc,

   valOf := proc(x::specfunc(`Piece`),$)
       op(2,x);
   end proc,

   #This is the exported lazy-syntax constructor. The syntax is like piecewise except
   #that there can be no 'otherwise'.
   ModuleApply::static:= proc(Terms::seq(anything))::Partition;
   local pair, s, Pairs, k;
      if nargs::odd then
         error "Expected an even number of arguments"
      end if;
      s:= [ seq(Piece( Terms[k], Terms[k+1]), k= 1..nargs-1, 2) ] ;
      userinfo(3, PARTITION, s);
      PARTITION(s)
   end proc,

   #Deconstructor that returns just the conditions as a set
   Conditions::static:= proc(P::Partition)::set;
   local p;
      {seq(condOf(p), p= op(1,P))}
   end proc,

   #Deconstructor that returns a set of [cond, val] pairs
   Pairs:= proc(P::Partition)::set([anything, anything]);
   local p;
      {seq([condOf(p), valOf(p)], p= op(1,P)) }
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
            Piece(
               condOf(pair),
               f(args[2..pos], valOf(pair), args[pos+2..])
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
        local kb0 := h(condOf(pair));
        Piece( f(condOf(pair), kb0),
               g(valOf(pair), kb0));
      end proc;
      PARTITION(map(doIt,op(1,part)));
   end proc,

   PartitionToPW := proc(x::Partition)::specfunc(piecewise);
       # piecewise can reduce immediately to not-piecewise which makes the type
       # test fail
       'piecewise'( op( ListTools[Flatten]( [ seq([condOf(p), valOf(p)], p= op(1,x)) ] ) ) );
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
       local ctx := true, n := nops(x), cls := [], cnd, ncnd, i, q
           , ctxC
         ;

       userinfo(5, PWToPartition
               , printf("PWToPartition: found %d ops in %a \n ", n, x) );

       # handles all but the `otherwise` case if there is such a case
       for i in seq(q, q = 1 .. iquo(n, 2)) do

           userinfo(3, PWToPartition
                    , printf("PWToPartition: looking at clause %d (op %d) \n ", i, 2*i-1));

           cnd := op(2*i-1,x); # the clause as given

           # if this clause is unreachable, then every subsequent clause will be as well
           if ctx :: identical(false) then
               return PARTITION( cls );
           else
               ctxC := `And`(cnd, ctx);              # the condition, along with the context (which is implicit in pw)
               ctxC := simplifyPartitionCtx(ctxC);

               if cnd :: `=` then
                   ncnd := lhs(cnd) <> rhs(cnd);
               else
                   ncnd := Not(cnd);
               end if;

               ctx  := `And`(ncnd, ctx); # the context for the next clause

               userinfo(3, PWToPartition, printf("PWToPartition: ctx after %d clauses "
                                                 "is %a\n", i, ctx));

               if ctxC :: identical(false) then # this clause is actually unreachable
                   return(PARTITION(cls));
               else
                   cls := [ op(cls)
                          , Piece(ctxC
                                 ,op(2*i ,x)
                                 )
                          ];

               end if;

           end if;
       end do;

       # if there is an otherwise case, handle that.
       if n::odd then
           ctx := simplifyPartitionCtx(ctx);
           if not ctx :: identical(false) then
               cls := [ op(cls)
                      , Piece(ctx
                             ,op(n,x)
                             )
                      ];
           end if;
       end if;

       PARTITION( cls );
   end proc,

   MbAppPartOrPw := proc(chk,f,x::Or(Partition,specfunc(piecewise)))
       local isPr := evalb(x::Partition), pr := `if`(isPr, x, PWToPartition(x));
       if chk(pr) then
           (`if`(isPr, a->a, PartitionToPW))(f(pr));
       else
           FAIL
       end if;
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
      for p in op(1,P) do if depends(condOf(p), V) then return true end if end do;
      false
   end proc
;

uses Hakaru;

   ModuleLoad()
end module:
