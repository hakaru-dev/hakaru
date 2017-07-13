# Step 2 of 3: computer algebra

improve := proc(lo :: LO(name, anything), {_ctx :: t_kb := empty}, opts := [], $)
local r, `&context`;
  userinfo(5, improve, "input: ", print(lo &context _ctx));
  _Env_HakaruSolve := true;
  r:= LO(op(1,lo), reduce(op(2,lo), op(1,lo), _ctx, opts));
  userinfo(5, improve, "output: ", print(r));
  r
end proc;

# Walk through integrals and simplify, recursing through grammar
# h - name of the linear operator above us
# kb - domain information
reduce := proc(ee, h :: name, kb :: t_kb, opts := [], $)
  local e, elim, subintegral, w, w1, ww, x, c, kb1, with_kb1, dom_specw, dom_specb
       , body, dom_spec, ed, mkDom, vars, rr;
  e := ee;

  rr := reduce_Integrals(e, h, kb, opts);
  if rr <> FAIL then return rr end if;
  if e :: 'applyintegrand(anything, anything)' then
    applyop(reduce_scalar, 2, e, kb)
  elif can_reduce_Partition(e) then
    reduce_Partition(e,h,kb,opts,false)
  elif e :: `+` then
    map(reduce, e, h, kb, opts)
  elif e :: `*` then
    (subintegral, w) := selectremove(depends, e, h);
    if subintegral :: `*` then error "Nonlinear integral %1", e end if;
    subintegral := convert(reduce(subintegral, h, kb, opts), 'list', `*`);
    (subintegral, ww) := selectremove(depends, subintegral, h);
    w := `*`(w,op(ww));
    w1 := simplify_factor_assuming(w, kb);
    if w1 = w then
      w := subsindets[flat](w, t_pw_or_part, x->reduce_Partition(x,h,kb,opts,false));
    else w := w1; end if;
    w * `*`(op(subintegral));
  elif e :: t_case then
    subsop(2=map(proc(b :: Branch(anything, anything))
                   eval(subsop(2='reduce'(op(2,b),x,c,opts),b),
                        {x=h, c=kb})
                 end proc,
                 op(2,e)),
           e);
  elif e :: 'Context(anything, anything)' then
    kb1 := assert(op(1,e), kb);
    # A contradictory `Context' implies anything, so produce 'anything'
    # In particular, 42 :: t_Hakaru = false, so a term under a false
    # assumption should never be inspected in any way.
    if kb1 :: t_not_a_kb then
        return 42
    end if;
    applyop(reduce, 2, e, h, kb1, opts);
  elif e :: 'toLO:-integrate(anything, Integrand(name, anything), list)' then
    x := gensym(op([2,1],e));
    # If we had HType information for op(1,e),
    # then we could use it to tell kb about x.
    subsop(2=Integrand(x, reduce(subs(op([2,1],e)=x, op([2,2],e)), h, kb, opts)), e)
  else
    simplify_assuming(e, kb)
  end if;
end proc;

reduce_scalar := proc(e, kb :: t_kb, $)
  foldr(((f,x)->f(x,kb)), e
        ,simplify_assuming
        ,Partition:-Simpl
        ,(x->subsindets(x, t_pw, PWToPartition))
       );
end proc;

# Returns true for expressions for which we could conceivably
# do a Partition simplification.
can_reduce_Partition := proc(e,inside := false)
  local ps;
  if   type(e,Or(Partition,t_pw)) and
       not(has(e, {erf,csgn}))    # probably output of elim_intsum
  then true
  elif type(e,{indices(Partition:-Simpl:-distrib_op_Partition,nolist)}) then
    if not(inside) then
      # in this case, we hope to apply PProd and then maybe do some cleanup; this
      # is only possible if the expression has at least two sub-Partitions.
      ps := select(x->can_reduce_Partition(x,true), convert(e,list));
      ps := map(Partition:-PWToPartition_mb, indets[flat](ps, t_pw_or_part));
      if nops(ps) < 2 then return false; end if;

      # We also only do this simplification if the Partitions have the same piece values
      the(ps, curry(SamePartition,((a,b)->true),`=`)) or
      # or the same conditions
      the(ps, curry(SamePartition,(`=`,(a,b)->true)))
    else
      ormap(x->can_reduce_Partition(x,true),convert(e,list))
    end if;
  else false
  end if;
end proc;

# Same as reduce, but for Partitions; and contains an additional flag which,
# when true, checks `can_reduce_Partition' (when the check is false, there is a
# great chance this function will throw an error!)
reduce_Partition := proc(ee,h::name,kb::t_kb,opts::list,do_check::truefalse, $)
  local e := ee;
  if do_check and not(can_reduce_Partition(e)) then return e end if;
  # big hammer: simplify knows about bound variables, amongst many
  # other things
  Testzero := x -> evalb(simplify(x) = 0);

  e := subsindets(e, t_pw, PWToPartition);
  e := Partition:-Simpl(e, kb);

  # This is necessary because subsequent calls to kb_Partition do not work on
  # nested Partitions; but Simpl calls flatten, which should gives us a
  # Partition on the top level.
  e := (`if`(e::Partition,do_reduce_Partition,reduce))(e, h, kb, opts);
  if ee::t_pw and e :: Partition then
    e := Partition:-PartitionToPW(e);
  end if;
  e;
end proc;

do_reduce_Partition := proc(ee,h::name,kb::t_kb,opts::list,$)
  local e := ee;
  e := kb_Partition(e, kb, simplify_assuming,
                    ((rhs, kb) -> %reduce(rhs, h, kb, opts)));
  e := eval(e, %reduce=reduce);
  e := Partition:-Simpl(e, kb);
end proc;

# "Integrals" refers to any types of "integrals" understood by domain (Int,
# Sum currently)
reduce_Integrals := module()
  export ModuleApply;
  local
  # The callbacks passed by reduce_Integrals to Domain:-Reduce
    reduce_Integrals_body, reduce_Integrals_into, reduce_Integrals_apply,
    reduce_Integrals_sum, reduce_Integrals_constrain
  # tries to evaluate a RootOf
  , try_eval_Root
  # tries to evaluate Int/Sum/Ints/Sums
  , elim_intsum
  , distrib_over_sum;

  reduce_Integrals_body := proc(h,opts,x,kb1) reduce(x,h,kb1,opts) end proc;
  reduce_Integrals_into := proc(h,opts,kind,e,vn,vt,kb,ows,$)
    local rr;
    rr := distrib_over_sum(
            x->elim_intsum(Domain:-Apply:-do_mk(kind,x,vn,vt,kb),
                           h,kb,opts),e);
    rr := subsindets(rr, specfunc(RootOf), x->try_eval_Root(x,a->a));
    ows * rr;
  end proc;
  reduce_Integrals_sum := proc()
    subsindets(`+`(args),
               And(`+`,satisfies(x->has(x,applyintegrand))),
               e->collect(e, `applyintegrand`, 'distributed'));
  end proc;
  reduce_Integrals_apply := proc(f,e,$)
    local r; r := e;
    r := `if`(can_reduce_Partition(r),
              Partition:-Simpl(subsindets(r,t_pw,x->PWToPartition(x,'check_valid'))),
              r);
    r := distrib_over_sum(f,r);
  end proc;
  reduce_Integrals_constrain := proc(do_c, x,$)
    local ws, b;
    b, ws := selectremove(has, convert(x, 'list', `*`), NewSLO:-applyintegrand);
    b, ws := map(`*`@op, [b, ws])[];
    ws * do_c(b);
  end proc;
  distrib_over_sum := proc(f,e,$) `+`(op(map(f,convert(e, 'list',`+`)))) end proc;

  ModuleApply := proc(expr, h, kb, opts, $)
    local rr;
    rr := Domain:-Reduce(expr, kb
      ,curry(reduce_Integrals_into,h,opts)
      ,curry(reduce_Integrals_body,h,opts)
      ,reduce_Integrals_sum
      ,reduce_Integrals_constrain
      ,reduce_Integrals_apply
      ,(_->:-DOM_FAIL), opts);
    rr := Partition:-Simpl(rr, kb);
    if has(rr, :-DOM_FAIL) then
      return FAIL;
    elif has(rr, FAIL) then
      error "Something strange happened in reduce_Integral(%a, %a, %a, %a)\n%a"
           , expr, kb, kb, opts, rr;
    end if;
    rr
  end proc;

  try_eval_Root := proc(e0::specfunc(`RootOf`),on_fail := (_->FAIL), $)
    local ix,e := e0;
    try
      if nops(e)=2 or nops(e)=3
      and op(-1,e) :: `=`(identical(index),{specindex(real),nonnegint}) then
        ix := op([2,-1],e);
        if ix :: specindex(real) then ix := op(ix); end if;
        e := op(0,e)(op(1,e));
      else
        ix := NULL;
      end if;
      e := convert(e, 'radical', ix);
      if e :: specfunc(RootOf) then return on_fail(e) end if;
      return e;
    catch: return on_fail(e0); end try;
  end proc;

  # Try to find an eliminate (by evaluation, or simplification) integrals which
  # are free of `applyintegrand`s.
  elim_intsum := module ()
    export ModuleApply := proc(inert0, h :: name, kb :: t_kb, opts, $)
       local ex, e, inert := inert0;
       ex := extract_elim(inert, h, kb);
       e[0] := apply_elim(h, kb, ex);
       e[1] := check_elim(inert, e[0]);
       if e[1] = FAIL then inert
       else
         e[2] := reduce(e[1],h,kb,opts);
         if has(e[2], {csgn}) then
           WARNING("Throwing away an eliminated result result containing csgn (this "
                   "could be a bug!):\n%1\n(while running %2)", e[2], ex);
           inert;
         else e[2] end if;
       end if
    end proc;

    local known_tys := table([Int=int_assuming,Sum=sum_assuming,Ints=ints,Sums=sums]);
    # Returns FAIL if we probably can't eliminate this intsum, or
    # the work to be done as a list:
    #  [ intsum body, intsum function, primary var, other var args ]
    local extract_elim := proc(e, h::name, kb::t_kb,$)
      local t, intapps, var, f, e_k, e_args, vs, blo, bhi,
            case_var, cond_case_var;
      vs := {op(KB:-kb_to_variables(kb))};
      t := 'applyintegrand'('identical'(h), 'anything');
      intapps := indets(op(1,e), t);
      if intapps = {} then
        return FAIL;
      end if;
      e_k := op(0,e); e_args := op([2..-1],e);
      if Domain:-Has:-Bound(e) and assigned(known_tys[e_k]) then
        var := Domain:-ExtBound[e_k]:-ExtractVar(e_args);
        ASSERT(var::DomBoundVar);
        blo, bhi := Domain:-ExtBound[e_k]:-SplitRange
                    (Domain:-ExtBound[e_k]:-ExtractRange(e_args));
        if ormap(b->op(1,b) in map((q-> (q,-q)), vs) and op(2,b)::SymbolicInfinity
                ,[[blo,bhi],[bhi,blo]]) then
          return FAIL end if; # This is something that `disint` wants to see unevaluated
        if var :: list then var := op(1,var) end if;
        case_var := c->hastype(c, 'idx'(list,name));
        cond_case_var := p->Partition:-ConditionsSatisfy(p,case_var);

        # independant of `h' - this is a weight
        if not depends(intapps, var)
        # A sum whose bounds are literals and which contains a
        # `case(idx(<literal array>, ...)) ...', or
        # `idx(<literal array>, ...' inside a `Ret'
        or (e_k in {Sum,Sums} and andmap(b->b::And(realcons,integer),[blo,bhi])
            and (hastype(op(1,e),
                           {And(Partition, satisfies(cond_case_var)),
                            And(t_pw, satisfies(cond_case_var@PWToPartition))})
                 or hastype(intapps, satisfies(case_var))))
        then f := known_tys[e_k];
        else return FAIL;
        end if;
      else
        error "extract_elim was passed something which is not an intsum: %1", e;
      end if;
      [ op(1,e), f, var, [e_args] ];
    end proc;

    local apply_elim := proc(h::name,kb::t_kb,todo::{list,identical(FAIL)})
      local body, f, var, rrest;
      if todo = FAIL then return FAIL; end if;
      body, f, var, rrest := op(todo);
      banish(body, h, kb, infinity, var,
             proc (kb1,g,$) do_elim_intsum(kb1, f, g, op(rrest)) end proc);
    end proc;

    local check_elim := proc(e, elim,$)
      if has(elim, {MeijerG, undefined, FAIL}) or e = elim or elim :: SymbolicInfinity then
        return FAIL;
      end if;
      return elim;
    end proc;

    local do_elim_intsum := proc(kb, f, ee, v::{name,name=anything})
      local w, e, x, g, t, r;
      w, e := op(Domain:-Extract:-Shape(ee));
      w := Domain:-Shape:-toConstraints(w);
      e := piecewise_And(w, e, 0);
      e := f(e,v,_rest,kb);
      x := `if`(v::name, v, lhs(v));
      g := '{sum, sum_assuming, sums}';
      if f in g then
        t := {'identical'(x),
              'identical'(x) = 'Not(range(Not({SymbolicInfinity, undefined})))'};
      else
        g := '{int, int_assuming, ints}';
        t := {'identical'(x),
              'identical'(x) = 'anything'};
        if not f in g then g := {f} end if;
      end if;
      for r in indets(e, 'specfunc'(g)) do
        if 1<nops(r) and op(2,r)::t then return FAIL end if
      end do;
      e
    end proc;
  end module; # elim
end module; # reduce_Integrals

int_assuming := proc(e, v::name=anything, kb::t_kb, $)
  simplify_factor_assuming(int(e, v), kb);
end proc;

# Should this do the same thing as `int_assuming'? i.e.
# should it pass `sum(e,v)' instead of `'sum'(e,v)' and
# get rid of the extra logic to evaluate the sum afterwards?
# Is calling `simplify_factor_assuming' here even correct?
sum_assuming := proc(e, v::name=anything, kb::t_kb)
  local r;
  r := simplify_factor_assuming('sum'(e, v), kb);
  if r::specfunc(`sum`) then sum(op(r)) else r; end if;
end proc;

# Int( .., var=var_ty ) == var &X var_ty
isBound_IntSum := kind -> module()
  option record;
  export MakeKB := (`if`(kind=Sum,KB:-genSummation,KB:-genLebesgue));
  export ExtractVar := (e->op(1,e));
  export ExtractRange := (e->op(2,e));
  export MakeRange := `..`;
  export SplitRange := (e->op(e));
  export Constrain := `if`(kind=Sum,`<=`,`<`);
  export DoMk := ((e,v,t)->kind(e,v=t));
  export Min := `min`; export Max := `max`;
  export VarType := 'name';
  export RangeType := 'range';
  export MapleType := 'And'('specfunc'(kind), 'anyfunc(anything,name=range)');
  export BoundType := `if`(kind=Sum,'integer','real');
  export RecogBound := `if`(kind=Sum,
            (proc(k,b)
               if   k = `<=` then (x->subsop(2=b,x))
               elif k = `>=` then (x->subsop(1=b,x))
               elif k = `<`  then (x->subsop(2=(b-1),x))
               elif k = `>`  then (x->subsop(1=b+1,x))
               end if;
             end proc),
            (proc(k,b)
               if   k in {`<=`,`<`} then (x->subsop(2=b,x))
               elif k in {`>=`,`>`} then (x->subsop(1=b,x))
               end if;
             end proc));
end module;

# Ints( .., var::name, var_ty::range, dims::list(name=range) ) ==
#        [ var   , map(lhs,dims) ] :: list(name)  &X
#        [ var_ty, map(rhs,dims) ] :: list(range)
isBound_IntsSums := kind -> module()
  option record;
  export MakeKB := proc(vars, lo, hi, kb, $)
    local var, dims, ty, rngs, x, kb1;
    var  := op(1, vars);
    rngs := zip(`..`,lo,hi);
    ty   := op(1, rngs);
    dims := subsop(1=NULL,zip(`=`,vars,rngs));
   x, kb1 := genType(var,
                      mk_HArray(`if`(kind=Ints,
                                     HReal(open_bounds(ty)),
                                     HInt(closed_bounds(ty))),
                                dims),kb);
    if nops(dims) > 0 then
      kb1 := assert(size(x)=op([-1,2,2],dims)-op([-1,2,1],dims)+1, kb1);
    end if;
    x, kb1;
  end proc;
  export ExtractVar   := ((v,t,d)->[v,map(lhs,d)[]]);
  export ExtractRange := ((v,t,d)->[t,map(rhs,d)[]]);
  export MakeRange    := ((a,b)->zip(`..`,a,b));
  export SplitRange   := (rs->(map(x->op(1,x),rs), map(x->op(2,x),rs)));
  export Constrain    := ((a,b)->zip(`if`(kind=Ints, `<`, `<=`),a,b)[]);
  export DoMk         := ((e,v,t)->kind( e,op(1,v),op(1,t), subsop(1=NULL,zip(`=`,v,t)) ));
  export Min          := ((a,b)->zip(`min`,a,b));
  export Max          := ((a,b)->zip(`max`,a,b));
  export VarType      := 'And(list(name),satisfies(x->x<>[]))';
  export RangeType    := 'And(list(range),satisfies(x->x<>[]))';
  export MapleType    := 'And'('specfunc'(kind),'anyfunc'('anything', 'name', 'range', 'list(name=range)'));
  export BoundType    := TopProp;
  export RecogBound   := (_->NULL);
end module;
