constraints_about_vars := module()
  uses SolveTools[Inequality];
  export SimplName  := "Make constraints abouts vars";
  export SimplOrder := 6;

    export ModuleApply := proc(vs0 :: DomBound, sh :: DomShape, $)
        local vs := vs0, ctx;
        vs  := {op(Domain:-Bound:-varsOf(vs))};
        ctx := Domain:-Bound:-toConstraints(vs0, 'bound_types');
        subsindets(sh, DomConstrain
                  ,x->do_simpl_constraints(vs0, vs, ctx, x));
    end proc;

    local do_simpl_constraints := proc(vs0, vars, ctx_vs, x, $)
        local ctx1, ctx, ss, td, rest, d, in_vs;
        ss, ctx := selectremove(q->depends(q,indets(vars,And(name,Not(constant)) )), x);
        in_vs := q-> not(lhs(q) in vars) and not(rhs(q) in vars);
        td, rest := selectremove(type, ss, And(relation,satisfies(in_vs)));
        ctx1 := { op(ctx), op(ctx_vs), op(rest) };
        d := map(x->try_make_about(vs0, vars,ctx1,x), td);
        DConstrain(op(d), op(ctx), op(rest));
    end proc;

    local try_make_about := proc(dbnd, vars, ctx1, q0, $)
        local vars_q, q_s, q := q0;
        vars_q := indets(q, name) intersect vars;
        if nops(vars_q)=0 then return q end if;

        vars_q := op(1,vars_q);
        q := KB:-try_improve_exp(q, vars_q, ctx1);

        try
          q_s := LinearUnivariate(q, vars_q) assuming (op(ctx1));
          if q_s :: set(relation) and nops(q_s)=1 then
            op(1,q_s)
          else
            q
          end if;
        catch "when calling '%2'. Received: 'inequality must be linear in %1'":
          q_s := 'solve({q},[op(vars_q)], 'useassumptions'=true) assuming (op(ctx1))';
          q_s := eval(q_s);
          if q_s::list then
            if nops(q_s)=0 then return q end if;
            q_s := map(s->remove(c->c in ctx1 or `and`(c::relation,lhs(c)::name,lhs(c)=rhs(c)), s), q_s);
            q_s := remove(x->x=[],q_s);
            if nops(q_s)=0 then return q end if;
            op(op(1,q_s)); # pick the first solution arbitrarily!
          else
            q
          end if;
        end try;
    end proc;
end module;

# Pushes constraints down, or pulls them up, when there are such constraints.
local do_ctx_dir := dir -> proc(vs :: DomBound, sh :: DomShape, $)
    local ctx := `if`(nops(vs)=2,op(2,vs),{});
    ctx := remove(x->x::`::`,ctx);
    if ctx <> {} then
        dir(ctx)(sh);
    else
        sh;
    end if;
end proc;

push_ctx_down := module()
  export ModuleApply := do_ctx_dir(ctx->sh->subsindets(sh, DomConstrain, x->if nops(x)<>0 then DConstrain(op(x), op(ctx)) else DConstrain() end if));
  export SimplName  := "Push context down";
  export SimplOrder := 1;
end module;

pull_ctx_out := module()
  export ModuleApply :=
    do_ctx_dir(ctx->sh->subsindets(sh, DomConstrain
              ,x->remove(c->c in ctx or (is(c) assuming op(ctx)), x)));
  export SimplName  := "Pull context out";
  export SimplOrder := 20;
end module;

# Turns constraints(relations) into bounds
classify_DConstrains := module()
  export SimplName  := "Classify constraints";
  export SimplOrder := 8;

  export ModuleApply := proc(dbnds::DomBound,dsh::DomShape,$)
    subsindets(dsh, DomConstrain, x->classify_Rels([op(x)], dbnds));
  end proc;

  # Split relations into those we can incorporate
  # into bounds and others; this process also includes
  # some intermediate computations about the new bound:
  #  [ DInto(var), orig, upd_bound, bound_kind, numVars ]
  #    var         :=   variable to be modified
  #    orig        :=   the original relation
  #    upd_bound   :=   how to modify (a function)
  #    bound_kind  :=   {LO/HI}
  #    numVars     :=   how many variables are mentioned by the bound
  local classify_Rel := proc(r0,dbnd,$)
    local ret, vars, mk_k, bnd_k, i, var_k, q, r := r0;
    ret := [ DConstrain, r0 ];
    vars := {Domain:-Bound:-varsOf(dbnd)[]};
    if r :: {`<=`,`<`} then
      if rhs(r) in vars then
        r := op(0,r)(rhs(r),lhs(r));
        mk_k := flip_rel[op(0,r)]; bnd_k := B_LO;
      elif lhs(r) in vars then
        mk_k := op(0,r);           bnd_k := B_HI;
      else
        return ret;
      end if;

      i := Domain:-Bound:-varIx_mb(dbnd, lhs(r));
      if i >= 0 then
        var_k := op([1,i,3], dbnd);
        q := Domain:-ExtBound[var_k]:-RecogBound(mk_k,rhs(r));
        if q <> NULL then
          ret := [ DInto(lhs(r)), r0, q, bnd_k, countVs(vars minus {lhs(r)},r0) ];
        end if;
      end if;
    end if;
    ret;
  end proc;

  # Classifies a set of relations as potential bounds. The process
  # is as follows:
  #  - Classify each relation individually (see classify_Rel)
  #  - "Categorize" by the classification
  #  - Split relations which will be DConstrains, and those where we found
  #      more than one LO/HI bound or more than 2 bounds total.
  #  - Sort the relations which are to become bounds by the number of variables
  #      mentioned in the bound
  #  - Rebuild the continuations producing each new bound (see make_DInto)
  #  - Rebuild the leftover relations as a DConstrain.
  #  - Squash together ("foldr (.) id fs z") the continuations and leftover relations.
  local classify_Rels := proc(rs0,dbnd,$)
    local cs1, cs2, cs, rs := rs0;
    rs := map(r->classify_Rel(r,dbnd), rs);
    rs := [ListTools[Categorize]( ((a,b) -> op(1,a)=op(1,b) ), rs )];
    cs1, rs := selectremove(x->op([1,1],x)=DConstrain, rs);
    rs, cs2 := selectremove(x->nops(x)=1 or (nops(x)=2 and op([1,4],x)<>op([2,4],x)), rs);
    rs := sort(rs, key=solOrder);
    rs := map(r->make_DInto(r,dbnd),rs);
    cs := DConstrain(map(c->map(q->op(2,q),c)[], [op(cs1),op(cs2)])[]);
    foldr((f,g)->f@g,x->x,op(rs))(cs);
  end proc;

  # Rebuild a classified (by classify_Rel) relation; this
  # takes a list of such classifications, all of whose variable should
  # be identical, and for which the different bound kinds are all distinct.
  # None of this is checked!
  # (since there are 2 bound kinds, this list is at most length 2)
  local make_DInto := proc(r::list([specfunc(DInto),anything,anything,identical(B_LO,B_HI),nonnegint]), dbnd, $)
    local var_nm, var_ty;
    var_nm := op([1,1,1], r);
    var_ty := Domain:-Bound:-get(dbnd, var_nm)[1];
    var_ty := foldr( ((q,x)->op(3,q)(x)), var_ty, op(r) );
    (ctx -> DInto(var_nm, var_ty, ctx))
  end proc;
  local flip_rel := table([`=`=`=`,`<>`=`<>`,`<=`=`>=`,`<`=`>`,`>=`=`<=`,`>`=`<`]);
  local countVs := ((vs,c)-> nops(indets(c, DomBoundVar) intersect {op(vs)} ));
  local solOrder := (x->`+`(map(z->op(5,z),x)[]));
end module;

# todo; this should actually solve for a variable, then substitute
# that variable in. In most cases, it would probably be enough to
# leave that as it is; it would simplify later.
singular_pts := module()
  export SimplName  := "Single_pts";
  export SimplOrder := 14;

  local can_remove := ((x,vs_ty) -> nops(x) = 1 and op(1,x) :: `=` and ormap(s->s(op(1,x))::vs_ty,[lhs,rhs]));

  export ModuleApply := proc(bnds_ :: DomBound, sh_ :: DomShape, $)
    local bnds := bnds_, sh := sh_, vs, todo, sh1, vs_ty;
    vs := applyop(bl -> select(b->op(3,b)=`Int`, bl), 1, bnds);
    vs := Domain:-Bound:-varsOf(vs);
    vs_ty := 'satisfies(x->x in {op(vs)})';
    todo := indets(sh, specfunc(`DConstrain`));
    todo := select(x->can_remove(x,vs_ty), todo);
    subs([seq(t=DSum(),t=todo)], sh);
  end proc;
end module;
