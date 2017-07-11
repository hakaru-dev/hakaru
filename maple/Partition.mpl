#This module implements `Partition`---Hakaru's replacement for Maple's
#endogenous and unwieldy `piecewise`.

#The outer data structure for a Partition is a function, PARTITION(...), (just like it
#is for piecewise.
Partition:= module()
  option package;

  # Constructor for Partition pieces
  global Piece;

local
  Umap := proc(f,x,$)
    f(op(0,x))( map( p -> Piece(f(condOf(p)),f(valOf(p))), piecesOf(x) )
              , `if`(nops(x)>1,map(f,[op(2..-1,x)]),[])[] )
  end proc,

  isPartitionPieceOf := proc( p, elem_t := anything )
    type(p, 'Piece(PartitionCond, elem_t)');
  end proc,

  isPartitionOf := proc( e, elem_t := anything )
    type(e, 'PARTITION(list(PartitionPiece(elem_t)))' ) or
    type(e, 'PARTITION(list(PartitionPiece(Or(elem_t,PieceRef))),list(elem_t))' );
  end proc,

  TYPES := table(
    [(PieceRef = 'And(specfunc(nonnegint,PieceRef),satisfies(x->nops(x)>0))')
    ,(PartitionCond = '{relation, boolean, `::`, specfunc({`And`,`Or`,`Not`}), `and`, `or`, `not`}')
    ,(PartitionPiece = 'isPartitionPieceOf')
    ,(Partition = 'isPartitionOf')
    ]),

  ModuleLoad::static:= proc()
    :-`print/PARTITION`:= proc()
      local SetOfRecords, branch;
      SetOfRecords := piecesOf(PARTITION(args));
      `print/%piecewise`(
        seq([ condOf(eval(branch)), valOf(eval(branch))][], branch= SetOfRecords))
    end proc;

    BindingTools:-load_types_from_table(TYPES);

    # global extensions to maple functionality
    :-`eval/PARTITION` :=
    proc(p, eqs, $)
      Umap(x->eval(x,eqs), p);
    end proc;

    # :-`depends/PARTITION` :=
    # proc(parts, nms, $)
    # local dp := (x -> depends(x, nms));
    #   # `or`(op ( map(p-> dp(condOf(p)) or dp(valOf(p)), parts) ), dp(x,);
    # end proc;

    :-`diff/PARTITION` := proc()
      local pw, wrt, dpw, r, r0, r1;
      wrt := args[-1];
      pw := PARTITION(args[1..-2]);
      pw  := PartitionToPW(pw);
      dpw := diff(pw, wrt);
      r   := PWToPartition(dpw, 'do_solve');
      r   := Pmap(simplify, r);
    end proc;

    :-`simplify/PARTITION` := Simpl;

    :-`convert/piecewise` := overload(
      [proc(p::Partition)
         option overload(callseq_only);
         PartitionToPW(Simpl:-stable_order(p));
       end proc, :-`convert/piecewise`]);

    unprotect(:-solve);
    :-`solve` := overload([
      proc(x:: Not(freeof(`PARTITION`))  )
        option overload(callseq_only); FAIL;
      end proc, :-`solve`]);
    protect(:-solve);

    VerifyTools[AddVerification](same_partition = proc(a,b,$) evalb(a=b) or SamePartition((x,y)->evalb(x=y),(x,y)->evalb(x=y),a,b) end proc);

    NULL
  end proc,

  ModuleUnload::static:= proc()
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

  extr_conjs := proc(x,$)
    if x::{specfunc(`And`), `and`} then
      map(extr_conjs, [op(x)])[];
    else
      x
    end if
  end proc;
export
  piecesOf := proc(x, $)
    local ps, rs;
    ps := op(1,x);
    if nops(x)=2 then
      rs := op(2,x);
      ps := map(mapPiece(proc(c0,v0)
                  local c,c1,v,s; c,v := c0,v0; s := (x->x);
                  if v::PieceRef then
                    c1 := is_lhs(type,c,name);
                    if c1<>FAIL then s := x->subs(c1,x) end if;
                    c, s(op(op(1,v),rs))
                  else
                    c, v
                  end if; end proc), ps );
    elif has(x,PieceRef) then
      error "found piece references (%1) but no table of pieces: %2", indets(x,PieceRef), x
    end if;
    ps;
  end proc,

  condOf := proc(x::specfunc(`Piece`),$)
    op(1,x);
  end proc,

  valOf := proc(x::specfunc(`Piece`),$)
    op(2,x);
  end proc,

  mapPiece := proc(f,$) proc(x::PartitionPiece,$) Piece(f(condOf(x), valOf(x))) end proc; end proc,
  unPiece := mapPiece(ident),
  ident := proc() args end proc,
  is_lhs := proc(test,x0)
    local x := x0;
    if test(rhs(x),_rest) then x := op(0,x)(rhs(x),lhs(x)) end if;
    if test(lhs(x),_rest) then return x
    else                       return FAIL
    end if;
  end proc,

  # This is an alternate (to PARTITION) constructor for partition, which has the
  # same call convention as piecewise, except there are no implicit cases. if
  # there is an otherwise case, its condition is the conjunction of negations of
  # the other conditions.
  ModuleApply := proc()::Partition;
    local ps, as, ops_r;
    if nargs=0 then
      error "empty partition";
    end if;
    ps := [args]; ops_r := iquo(nops(ps),2);
    if nops(ps)::odd then
      ps := [op(1..-2,ps), Not(bool_Or(seq(op(2*i-1,ps),i=1..ops_r))), op(-1,ps)];
      ops_r := ops_r+1;
    end if;
    ps := [seq(Piece(op(2*i-1,ps),op(2*i,ps)),i=1..ops_r)];
    PARTITION(ps);
  end proc,

  Pieces := proc(cs0,es0)::list(PartitionPiece);
    local es, cs;
    es := `if`(es0::{set,list},x->x,x->{x})(es0);
    cs := `if`(cs0::{set,list,specfunc(`And`),`and`},x->x,x->{x})(cs0);
    [seq(seq(Piece(c,e),c=cs),e=es)];
  end proc,

  #This is just `map` for Partitions.
  #Allow additional args, just like `map`
  Pmap::static:= proc(f)::Partition;
    local pair,pos,res;
    res := map_check(procname, args);
    if res::string then error res else pos := res; end if;
    PARTITION([seq(
      Piece(condOf(pair)
            ,f(args[2..pos], valOf(pair), args[pos+2..])
         ),pair= piecesOf(args[pos+1]))])
  end proc,

  # a more complex mapping combinator which works on all 3 parts
  # not fully general, but made to work with KB
  # also, does not handle extra arguments (on purpose!)
  Amap::static:= proc(
    funcs::[anything, anything, anything], #`appliable` not inclusive enough.
    part::Partition)::Partition;
    local pair,pos,f,g,h,doIt;
    (f,g,h) := op(funcs);
    #sigh, we don't have a decent 'let', need to use a local proc
    doIt := proc(pair)
    local kb0 := h(condOf(pair));
      Piece( f(condOf(pair), kb0),
             g(valOf(pair), kb0));
    end proc;
    PARTITION(map(doIt,piecesOf(part)));
  end proc,

  Foldr := proc( cons, nil, prt :: Partition, $ )
    foldr(proc(p, x) cons(condOf(p), valOf(p), x); end proc,nil,op(piecesOf(prt)));
  end proc,

  Case := proc(ty,f,g) proc(x) if x::ty then f(x) else g(x) end if end proc end proc,
  Foldr_mb := proc(cons,nil,prt) Case(Partition, x->Foldr(cons,nil,x), x->cons(true,x,nil)) end proc,
  PartitionToPW_mb := Case(Partition, PartitionToPW, x->x),
  PWToPartition_mb := Case(specfunc(piecewise), PWToPartition, x->x),

  PartitionToPW := module()
    export ModuleApply; local pw_cond_ctx;
    ModuleApply := proc(x::Partition, $)
      option remember,system;
      local parts := piecesOf(x);
      if nops(parts) = 1 and is(op([1,1],parts)) then return op([1,2], parts) end if;
      parts := foldl(pw_cond_ctx, [ [], {} ], op(parts) );
      parts := [seq([condOf(p), valOf(p)][], p=op(1,parts))];
      if op(-2, parts) :: identical(true) then
        parts := subsop(-2=NULL, parts);
      end if;
      piecewise(op(parts));
    end proc;

    pw_cond_ctx := proc(ctx_, p, $)
    local ps, ctx, ctxN, cond, ncond;
      ps, ctx := op(ctx_); cond := condOf(p);
      cond := {extr_conjs(cond)};
      cond := remove(x->x in ctx, cond);
      ncond := `if`(nops(cond)=1
                    , KB:-negate_rel(op(1,cond))
                    , `Not`(bool_And(op(cond))) );
      cond := bool_And(op(cond));
      ctx := ctx union { ncond };
      [ [ op(ps), Piece(cond, valOf(p)) ], ctx ]
    end proc;
  end module,

  isShape := kind ->
  module()
    option record;

    export MakeCtx := proc(p0,_rec,kb)
      local p := p0, pw, p1, wps, ws, vs, cs, w, ps;
      if kind='piecewise' then
        p := Partition:-PWToPartition(p);
      end if;
      p1 := Partition:-Simpl:-remove_false_pieces(p,kb);
      w, p1 := Partition:-Simpl:-single_nonzero_piece(p1);
      if not w :: identical(true) or p1 <> p then
        [ w, p1 ]
      else
        ps := piecesOf(p);
        wps := map((x->_rec(valOf(x),kb)), ps);
        ws, vs, cs := map2(op, 1, wps), map2(op, 2, wps), map(condOf, ps);
        if nops(vs) > 0 and
          andmap(v->op(1,vs)=v, vs) and
          ormap(a->a<>{}, ws)
        then
          [ `bool_Or`( op( zip(`bool_And`, ws, cs) ) ) , op(1,vs) ];
        else
          [ true, p0 ];
        end if;
      end if;
    end proc;
    export MapleType := `if`(kind=`PARTITION`,'Partition','specfunc(piecewise)');
  end module,

  # Checks if the given Partition is semantically valid, i.e. the conditions are
  # all disjoint. This exploits the property that if each adjacent pair of
  # conditions is pairwise disjoint, then they are all disjoint
  # (i.e. disjointness is transitive).
  IsValid := proc(p::Partition,$)
    option remember, system;
    local i, cs; cs := map(condOf, piecesOf(p));
    for i from 2 to nops(cs) do
      if not(is(bool_Not(op(i  ,cs))) assuming op(i-1,cs)) or
         not(is(bool_Not(op(i-1,cs))) assuming op(i  ,cs)) then
        return false; end if;
    end do;
    return true;
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
  PWToPartition := module()
    export ModuleApply := proc(x::specfunc(piecewise),{_kb::t_kb:=KB:-empty})
      option remember, system;
      local p;
      p := semantically_Partition(x);
      if p=FAIL then general(x,_kb,_rest);
      else           p
      end if;
    end proc;

    # A special case in which the piecewise is of the form
    # piecewise(A {<=,<} C_0, V_0, ..,
    #           A {<=,<,=} C_i, V_i, ..,
    #           A {<=,<} C_n, V_n, V_{n+1})
    # Such a piecewise is semantically a Partition, but not syntactically so.
    # Returns FAIL if the piecewise is not of this form
    local semantically_Partition := proc(x::specfunc(piecewise), $)
                                 ::{Partition,identical(FAIL)};
      local ns, cs, i, vs;
      ns := nops(x);
      if ns <= 3 then return FAIL; end if;
      cs[0] := [seq(op(2*i-1, x),i=1..iquo(ns,2))];
      if ormap(c->not(c::relation), cs[0]) then return FAIL; end if;
      if ns::odd then
        # Assuming it is semantically a Partition, construct the otherwise case
        cs[0] := [ cs[0][], KB:-negate_rel(cs[0][-1]) ];
      end if;
      # Check if the conditions are of the desired form...
      cs[1] := map(c->Domain:-Improve:-classify_relation(c,x->type(x,realcons)),
                   cs[0]);
      if has(cs[1], FAIL)
         # Relations must be in {<,<=,=}
      or ormap(c->not(op(1,c) in { B_LO, B_HI, B_EQ }), cs[1])
         # First and last conditions may not be equalities
      or (op([1,1],c)=B_EQ or op([-1,1],c)=B_EQ)
         # Value branched on must be identical in each condition
      or not(the(map2(op,4,cs[1])))
         # Must be ordered accordingly
      or (cs[1] <> sort(cs[1],key=bnd_key))
      then return FAIL end if;
      # ...they are; build the resulting conditions
      cs[2] := map(KB:-negate_rel, cs[0]);
      cs[3] := [ true  , op(1..-2, cs[2]) ];
      cs[4] := [ true$2, op(1..-3, cs[2]) ];
      cs[3] := KB:-zip_k(
        proc(x,y,z)
          # No need to take the previous negated condition; it's implied by the
          # equality
          if    x::`=`   then  x
          # Skip over the previous negated condition if it's an inequality; take
          # the one before that instead (and strenghten it, since this condition
          # also includes the negation of the equality)
          elif  y::`<>`  then  bool_And(x, table([`<=`=`<`, `<`=`<`])[op(0,z)](op(z)))
          # General case
          else                 bool_And(x,y)
          end if;
        end proc, cs[0], cs[3], cs[4] );
      # Finally build the Partition
      vs    := [seq(op(2*i, x),i=1..iquo(ns,2)), `if`(ns::odd,op(-1,x),NULL)];
      PARTITION(zip(Piece, cs[3], vs));
    end proc;
    local bnd_key := (x->[op(3,x), table([B_LO, B_EQ, B_HI] =~ [0,1,2])[op(1,x)]]);

    local general := proc(x, kb::t_kb)::Partition;
      # each clause evaluated under the context so far, which is the conjunction
      # of the negations of all clauses so far
      local ctx := true, n := nops(x), cls := [], cnd, ncnd, i, q, ctxC, cl, p;

      # Checks if the piecewise is valid when translated literally to a Partition
      # if so, that Partition can be returned directly. This is not done by
      # default because the check calls `coulditbe' many times which is
      # potentially much more expensive than just building the Partition from
      # scratch. This should only be used when the piecewise comes from a solver
      # which may or may not already return a 'partition', and when it does return
      # a 'partition', the set of conditions is typically so complicated that
      # rebuilding it produces an unwieldy monster (e.g. SemiAlgebraic in the case
      # of e.g. RoundTrip/t62).
      if 'check_valid' in {_rest} then
        p := Partition(op(x));
        if IsValid(p) then return p end if;
      end if;

      # handles all but the `otherwise` case if there is such a case
      for i in seq(q, q = 1 .. iquo(n, 2)) do
        cnd := op(2*i-1,x); # the clause as given
        # if this clause is unreachable, then every subsequent clause will be as well
        if ctx :: identical(false) then return PARTITION( cls );
        else
          ctxC := bool_And(cnd, ctx);              # the condition, along with the context (which is implicit in pw)
          ctxC := Simpl:-condition(ctxC, kb, _rest);

        if cnd :: `=` then ncnd := lhs(cnd) <> rhs(cnd);
        else               ncnd := bool_Not(cnd) end if;

          ctx  := bool_And(ncnd, ctx);             # the context for the next clause

          if ctx :: identical(false,[]) then    # this clause is actually unreachable
            return(PARTITION(cls));
          else
          cls := [ op(cls), op(Pieces(ctxC,[op(2*i,x)])) ];
          end if;
        end if;
      end do;

      # if there is an otherwise case, handle that.
      if n::odd then
        ctx := Simpl:-condition(ctx, kb, _rest);
        if not ctx :: identical(false,[]) then
          cls := [ op(cls), op(Pieces(ctx,[op(n,x)])) ];
        end if;
      end if;

      if nops(cls) = 0 then
        WARNING("PWToPartition: the piecewise %1 produced an empty partition", x);
        return 0;
      end if;
      PARTITION( cls );
    end proc;
  end module,

  # applies a function to the arg if arg::Partition,
  # and if arg::piecewise, then converts the piecewise to a partition,
  # applies the function, then converts back to piecewise
  # this mainly acts as a sanity check
  AppPartOrPw := proc(f,x::Or(Partition,specfunc(piecewise)),
                      to_opts:=[], from_opts:=[])
    if x::Partition then f(x);
    else
      PartitionToPW(f(PWToPartition(x,op(to_opts))),op(from_opts))
    end if;
  end proc,

  #Check whether the conditions of a Partition satisfy a type (or a proc return
  #truefalse)
  ConditionsSatisfy := proc(P::Partition, test, $)
    local p, ty; ty := `if`(test::type,test,satisfies(test));
    for p in piecesOf(P) do if condOf(p)::ty then return true end if end do;
    false
  end proc,

  #Check whether the conditions of a Partition depend on any of a set of names.
  ConditionsDepend:= proc(P::Partition, V::{name, list(name), set(name)}, $)
    ConditionsSatisfy(P, x->depends(x,V));
  end proc,

  # The cartesian product of two Partitions
  PProd := proc(p0::Partition,p1::Partition,{_add := `+`})::Partition;
  local ps0, ps1, cs, cs0, rs, rs0, rs1, condOrder;
    # This first part is a special case to handle the subsets of Partitions
    # whose conditions are the same - we can add those directly.
    ps0 := piecesOf(p0); cs0 := map(condOf, ps0);
    condOrder := proc(c)
      # This relies on the fact that integers (numeric types in general) are
      # 'less than' everything else. This sorts the 2nd partition with pieces in
      # common with the 1st coming before other pieces (in the order they appear
      # in the first).
      local i := ListTools:-Search(c, cs0);
      `if`(i=0, c, i);
    end proc;
    ps1 := sort(piecesOf(p1), key=condOrder@condOf);
    # Add those pieces with identical conditions directly; return the rest as a
    # pair of pieces.
    cs := zip(proc(p0,p1)
                if condOf(p0)=condOf(p1) then
                  Piece(condOf(p0),_add(valOf(p0),valOf(p1))) ;
                else [p0,p1];
                end if;
              end proc, ps0,ps1);
    # Extract the pieces already processed above; those not processed are lists
    rs, cs := selectremove(c->type(c,list),cs);
    # Unzip the list of remaining pieces
    rs0, rs1 := map(k->map(r->op(k,r),rs),[1,2])[];
    # The actual cartesian product (of whats left)
    rs := map(r0->map(r1-> Piece( bool_And(condOf(r0),condOf(r1)), _add(valOf(r0),valOf(r1)) )
                      ,rs1)[],rs0);
    PARTITION([op(cs),op(rs)]);
  end proc,

  Simpl := module()
    export ModuleApply := proc()
      local p;
      p := do_Simpl(args);
      p := subsindets[flat](p,Partition,Factor);
    end proc;

    local do_Simpl := proc(p)
      option remember, system;
      local ps, qs, qs1, mk, as; as := _rest;
      if p :: Partition then
        foldr((f,x)->f(x,as), p,
              reduce_branches,
              coalesce_equalities,
              remove_false_pieces,
              flatten,
              singular_pts);
      elif not hastype(p, Partition) then
        p;
      elif assigned(distrib_op_Partition[op(0,p)]) then
        ps := simpl_op_Partition[op(0,p)](p);
        if op(0,p)=op(0,ps) then
          mk := distrib_op_Partition[op(0,ps)];
          ps := [op(ps)];
          ps := map(x->do_Simpl(x,as), ps);
          ps, qs := selectremove(type, ps, Partition);
          if nops(ps)=0 then return p end if;
          mk(op(qs),foldr(((a,b)->
                           remove_false_pieces(Partition:-PProd(a,b,_add=mk))),
                          op(ps)));
        else
          do_Simpl(ps,as);
        end if;
      else
        subsindets(p,{Partition,indices(distrib_op_Partition,nolist)},x->do_Simpl(x,as));
      end if;
    end proc;
    local  simpl_op_Partition := table([`+`=factor,`*`=(x->x)]);
    export distrib_op_Partition := table([`+`=`+`,`*`=`*`]);

    local Factor := proc(p::Partition)
      local ps, qs, zs, tycands, v, p1;
      ps := piecesOf(p);
      qs, zs := selectremove(x->valOf(x)<>0,ps);
      # Deal with only the simple case of one non-zero piece
      if not (nops(qs)=1 and nops(zs)=1) then return p end if;
      ps := valOf(op(1,ps));
      if not(ps :: factor_op_Partition) then return p end if;
      # Deal only with simple weights
      tycands := [ specfunc(NewSLO:-applyintegrand) ];
      tycands := select(`<>`,map(t -> indets[flat](ps, t), tycands), {});
      # Expect to find exactly one 'atom' type
      if nops(tycands)<>1 then return p end if;
      tycands := op([1,1,0],tycands);

      if ps::`+` then
        v[0] := ps;
        if has(ps, exp) then
          v[0] := convert(v[0], exp);
          v[0], v[1] := selectremove(type, convert(v[0], list, `*`), `+`);
          v[0], v[1] := map(`*`@op, [v[0], v[1]])[];
          v[0] := collect(v[0], tycands);

          v[2] := convert(v[0], exp);
        else
          v[0] := factor(v[0]);
          v[0], v[1] := selectremove(type, convert(v[0], list, `*`), `+`);
          v[0], v[1] := map(`*`@op, [v[0], v[1]])[];
        end if;
      elif ps::`*` then
        v[0] := [op(ps)];
        v[0], v[1] := selectremove(has, v[0], tycands);
        v[0], v[1] := map(`*`@op, [v[0],v[1]])[];
      else error "impossible"; end if;

      p1 := v[1]*subs(ps=v[0], p);
    end proc;
    # TODO: factor for `*` is completely untested
    local factor_op_Partition := {`+`};

    export flatten := module()
      export ModuleApply;
      local unpiece, unpart, flatten_with;

      ModuleApply := proc(pr0, { _with := [ 'Partition', unpart ] } )
        local ty, un_ty, pr1, pr2;
        ty, un_ty := op(_with);

        pr1 := subsindets(pr0, ty, un_ty);
        if pr0 <> pr1 then
          ModuleApply(pr1, _with=[ Or('Partiton',`*`), unpart ]);
        else
          pr0
        end if;
      end proc;

      # like Piece, but tries to not be a Piece
      unpiece := proc(c, pr, $)
        flatten_with(proc(mk_q, ps)
                       map(q -> Piece(bool_And(condOf(q),c),mk_q(valOf(q))), ps)[]
                     end proc,
                     x->Piece(c,x),
                     pr);
      end proc;

      unpart := curry(
        flatten_with,proc(mk_q, ps)
                       PARTITION(map(q -> unpiece(condOf(q),valOf(q)), ps))
                     end proc, x->x);

      flatten_with := proc(rec, fail, pr, $)
      local ps, ws;
        if pr :: Partition then
          ps := piecesOf(pr); ws := [];
        elif pr :: `*` then
          ps, ws := selectremove(q->type(q,Partition), [op(pr)]);
          if nops(ps) = 1 then
            ps := piecesOf(op(1,ps));
          else return fail(pr) end if;
        else
          return fail(pr);
        end if;
        rec(x->`*`(op(ws),x), ps);
      end proc;
    end module;

    # Technically a no-op since Partitions have set semantics, but provides a
    # stable (hopefully) order of pieces, which will matter once the Partition
    # is returned to Haskell; the final condition will be erased (replaced by an
    # 'otherwise') and we would like 1) for that to always be the same one (in
    # case changes to Partition simplification order the pieces slightly
    # differently) and 2) for that to be the most 'complex' one.
    export stable_order := proc(e::Partition)
      # hopefully `sort' is actually a stable sort...
      PARTITION( sort(piecesOf(e),key=condition_complexity@condOf) );
    end proc;

    export single_nonzero_piece_cps := proc(k)
      local r,p; r, p := single_nonzero_piece(_rest);
      if r :: identical(true) then
        args[2]
      else
        k(r, p);
      end if;
    end proc;

    export single_nonzero_piece := proc(e, { _testzero := Testzero })
      local zs, nzs;
      if e :: Partition then
        zs, nzs := selectremove(p -> _testzero(valOf(p)), piecesOf(e));
        if nops(nzs) = 1 then
          return condOf(op(1,nzs)) , valOf(op(1,nzs))
        end if;
      end if;
      true, e
    end proc;

    export remove_false_pieces := proc(e::Partition, kb := KB:-empty)
      PARTITION(remove(p -> type(KB:-assert(condOf(p), kb), t_not_a_kb), piecesOf(e)));
    end proc;

    local `&on` := proc(f,k,$) proc(a,b,$) f(k(a),k(b)) end proc end proc;
    local condition_complexity := proc(x)
      nops(indets(x,PartitionCond)) + nops(indets(x,specfunc({exp, ln})))
    end proc;

    local try_eval := proc(x,s,$)
      try eval(x,s)
      catch "numeric exception: division by zero": FAIL; end try;
    end proc;

    # Combines pieces whose conditions are of the form `x=A' and (`x<A' or
    # `A<x') and whose values are equal under the evaluation `x=A'
    export coalesce_equalities :=
    proc(e::Partition,{ _testequal := ((a,b) -> Testzero(a-b)) })
      local ps, eqs, rest, p, pcond, pval, pbnds, cand, cands, sb;
      ps := piecesOf(e);
      eqs, rest[0] := selectremove(x->condOf(x)::`=`, ps);
      for p in eqs do
        pcond := condOf(p); pval := valOf(p);
        pbnds := {`<`(op(pcond)), `>`(op(pcond))};
        cands, rest[1] := selectremove(x-> has(condOf(x),pbnds), rest[0]);
        cands, rest[2] := selectremove((x->try_eval(x,pcond)=pval)@valOf, cands);
        if nops(cands) = 0 then
          rest[0] := [ p, op(rest[0]) ];
        elif nops(cands) <= 2 then
          cand := op(1,cands);
          sb := select(b->has(condOf(cand),b), pbnds);
          ASSERT(nops(sb)=1); # assumes that both `x<A' and `x>A' won't appear
                              # in a single condition
          sb := op(1,sb);
          rest[0] :=
          [ applyop(x->subs(sb=`<=`(op(sb)),x), 1, cand),
            `if`(nops(cands)=2, op(2,cands), NULL),
            op(rest[2]), op(rest[1]) ];
        else
          error "should be impossible (invalid Partition?): %1", cands;
        end if;
      end do;
      PARTITION(rest[0]);
    end proc;

    export reduce_branches := proc(e::Partition, kb := KB:-empty, { _testequal := ((a,b) -> Testzero(a-b)) })
      local k, ks, i, ps1, ps; ps := piecesOf(e);
      userinfo(3, :-reduce_branches, printf("Input: %a\n", ps));

      if nops(ps)=1 then return op([1,2],ps); end if;

      # Categorize(group) by equality of piece values
      ps1 := [ListTools:-Categorize(_testequal &on valOf, ps)];
      # unless there are fewer groups than original pieces ...

      ks  := map(nops, ps1); # number of pieces per group

      # build the result
      ps1 := zip((p,k)->
                 Piece(bool_Or(condition(bool_Or(map(condOf,p)[]), kb,
                         `if`(k<>1,
                              ['do_solve', 'do_kb', 'do_check'],
                              ['reduce_conjs']
                             )[])[]),
                       valOf(op(1,p)))
                 ,ps1, ks);
      userinfo(3, :-reduce_branches, printf("condition: %a\n", ps1));

      # replace the condition of each piece built from many others
      if nops(ps1) < nops(ps) and nops(ps1)>1 then
        for i in select(x->op(1,x)>1,sort(zip(`[]`,ks,[seq(1..nops(ks))]), key=(x->-op(1,x)))) do
          ps1 := piecesOf( replace_piece_cond(PARTITION(ps1), op(2,i)) );
        end do;
      end if;

      return PARTITION(ps1);
    end proc;

    # Replaces a piece (at given index) condition with the logically equivalent
    # one formed from the other pieces.
    export replace_piece_cond := proc(e::Partition, n::integer := -1, failure:=(x->x), cmp_score := [ (x->x), (x->x+1) ], $)
      local p_n, p_n1,ps,cmp; ps := piecesOf(e);
      if abs(n)>nops(ps) then
        error "index out of bound: %1", n;
      elif nops(ps)=1 then
        error "cannot replace in single piece Partition: %1", e
      end if;
      p_n := condOf(op(n, ps));                              # old condition
      p_n1 := Not(bool_Or(map(condOf,subsop(n=NULL,ps))[])); # new condition
      cmp := map(condition_complexity, [p_n1, p_n]);

      # a cheap metric for determining if the new condition is an improvement
      if `<=`(zip(apply, cmp_score, cmp)[]) then
        ps := subsop([n,1]=p_n1, ps);
        PARTITION(ps);
      else
        failure(PARTITION(ps));
      end if;
    end proc;

    # Removal of singular points from partitions
    # works with other things too!
    export singular_pts := module()
      local t_constant := (ns->x->(indets(x,And(name,Not(constant))) minus ns)={});
      local can_remove := proc(ns)
        local t1, t2;
        t1 := satisfies(t_constant(ns));
        t2 := satisfies(n->n in ns);
        'Or'(`=`(t2,{t1,t2}),`=`(t1,t2));
      end proc;

      local weakening := {`<=`=`<`, `>=`=`>`};
      local can_replace := proc(ns)
        local t := satisfies(n->n in ns);
        'And'('specfunc'(map(lhs,weakening)),
              {'anyfunc'('anything',t),'anyfunc'(t,'anything')});
      end proc;
      local do_replace := proc(c)
        table([op(weakening)])[op(0,c)](op(c));
      end proc;

      export ModuleApply := proc(sh, kb::t_kb:=KB:-empty,{_name_cands::list := [] })
        local ns, sh1; sh1 := sh;
        # todo: work with array types as well?
        ns := select(type, [op(kb)], And(KB:-t_kb_Introduce,anyfunc(anything,specfunc(`AlmostEveryReal`))));
        ns := map(curry(op,1), ns);
        ns := { op(ns), op(_name_cands) };
        if ns={} then return sh end if;

        sh1 := subsindets(sh1, can_remove(ns), _->false);
        sh1 := eval(eval(sh1, [`And`=bool_And,`Or`=bool_Or]));
        sh1 := subsindets(sh1, 'specfunc'('specfunc'(map(op,weakening)),Not), bool_Not@op);
        sh1 := subsindets(sh1, can_replace(ns), do_replace);
        subsindets[flat](sh1, Partition, pr->remove_false_pieces(pr,kb));
      end proc;
    end module; # singular_pts

    export condition := module()
      local is_extra_sol := x -> (x :: `=` and rhs(x)=lhs(x) and lhs(x) :: name);
      local postproc_for_solve := proc(ctx, ctxSlv)
                               ::{identical(false), list({boolean,relation,specfunc(boolean,And),`and`(boolean)})};
        local ctxC := ctxSlv;
        if ctxC = [] then
          ctxC := [] ;
        elif nops(ctxC)> 1 then
          ctxC := map(x -> postproc_for_solve(ctx, [x], _rest)[], ctxC);
        elif nops(ctxC) = 1 then
          ctxC := op(1,ctxC);
          if ctxC :: set then
            if ctxC :: identical('{}') then
              ctxC := NULL;
            else
              ctxC := remove(is_extra_sol, ctxC);
               # if all the solutions are 'extra', the solution is actually just
               # garbage. Maple can't really tell and doesn't just return the
               # empty set (no solutions) for these cases.
              if ctxC = {} then
                ctxC := ctx;
              else
                ctxC := bool_And(op(ctxC));
              end if;
            end if ;
            ctxC := [ctxC];
          elif ctxC :: specfunc('piecewise') then
            ctxC := PWToPartition(ctxC, _rest);
            ctxC := [ seq( map( o -> condOf(c) and o
                                , postproc_for_solve(ctx, valOf(c), _rest))[]
                           , c=piecesOf(ctxC) )] ;
          else
            ctxC := FAIL;
          end if;
        else
          ctxC := FAIL;
        end if;
        if ctxC = FAIL then
          error "don't know what to do with %1", ctxSlv;
        else
          ctxC;
        end if;
      end proc;

      # Removes each conjunct if it is true under the assumption of the others
      local do_reduce_conj := proc(x::specfunc(And), $)
        bool_And(seq(
          `if`((is(op(i,x)) assuming
                op(subsop(i=NULL,[op(x)]))),
               NULL, op(i,x)),
          i=1..nops(x)));
      end proc;

      # For some reason, solve just disregards these sorts of conditions
      # altogether, but not when they appear on their own! e.g.
      #  solve( {a<>b} )       = {a=a,a<>b}
      #  solve( {Not(a<>b)} )  = {a=a,b=b}  -- but should be {..,a=b}
      local can_solve := proc(c,$)
        local neq_nn := `<>`(name,name);
        evalb(indets(c, neq_nn) = {} or not has(c,`idx`))
      end proc;

      export ModuleApply := ProfileFn(1.0,do_condition);

      export do_condition := proc(ctx, kb::t_kb := KB:-empty)::list(PartitionCond);
        option remember, system;
        local ctxC, ctxC1, ctxC_c, ctxC1_c;
        ctxC := ctx;
        if ctx :: identical(true) then
          error "Simpl:-condition: don't know what to do with %1", ctxC;
        end if;
        if 'do_kb' in {_rest} then
          ctxC1 := KB:-kb_subtract( KB:-assert( ctxC, kb ), kb );
          if nops(ctxC1)=1 and op([1,1], ctxC1)=KB:-assert then
            ctxC1 := op([1,2], ctxC1);
            ctxC1_c, ctxC_c := map(condition_complexity, [ctxC1,ctxC])[];
            if ctxC1_c < ctxC_c then
              ctxC := ctxC1;
            end if;
          end if;
        end if;
        if condition_complexity(ctxC)=1 then
          return [ctxC];
        end if;

        ctxC := KB:-chill(ctxC);
        if 'reduce_conjs' in {_rest} then
          ctxC := subsindets(ctxC,specfunc(And),do_reduce_conj)
        elif 'do_solve' in {_rest} and _Env_HakaruSolve<>false and can_solve(ctxC) then
          ctxC1 := solve({ctxC}, 'useassumptions'=true);
          if ctxC1 = ctxC then
            # sometimes solve returns unevaluated which confuses postproc because
            # it expects the typical output of solve
            ctxC := [ctxC];
          elif ctxC1 = NULL and indets(ctx, specfunc(`exp`)) <> {} then
            ctxC := [ctxC];
          else
            ctxC1 := postproc_for_solve(ctxC, [ctxC1], _rest);
            if 'do_check' in {_rest} and condition_complexity(ctxC)>condition_complexity(ctxC1) then
              ctxC := ctxC1;
            end if;
          end if;
          if indets(ctxC, specfunc({`Or`, `or`})) <> {} then
            userinfo(10, 'Simpl:-condition',
                     printf("output: \n"
                            "  %a\n\n"
                            , ctxC ));
          end if;
        else
          ctxC1 := ctxC;
          ctxC := [seq(Domain:-simpl_relation(ctxC1, norty=t), t=['DNF','CNF'])];
          ctxC := eval(ctxC,`And`=bool_And);
          ctxC := op(1, sort(ctxC, key=condition_complexity));
          if ctxC :: specfunc(`Or`) then
            ctxC := [op(ctxC)]
          else
            ctxC := [ctxC];
          end if;
        end if;
        if 'no_split_disj' in {_rest} then
          ctxC := [ bool_Or(op(ctxC)) ];
        end if;
        ctxC := KB:-warm(ctxC);
        `if`(ctxC::list, ctxC, [ctxC]);
      end proc;
    end module; #Simpl:-condition
  end module, #Simpl

  SamePartition := proc(eqCond, eqPart, p0 :: Partition, p1 :: Partition, $)
    local ps0, ps1, pc0, the;
    ps0, ps1 := map(piecesOf,[p0,p1])[];
    if nops(ps0) <> nops(ps1) then return false end if;
    for pc0 in ps0 do
      the, ps1 :=
        selectremove(pc1 ->
          eqCond( condOf(pc1), condOf(pc0) ) and
          eqPart( valOf(pc1) , valOf(pc0)  )     ,ps1);
      if nops(the) <> 1 then
        return false;
      end if;
    end do;
    true;
  end proc
;
  uses Hakaru;
  ModuleLoad();
end module:
