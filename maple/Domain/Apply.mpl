# Apply a domain to an expression.
# Apply will perform certain 'simplifications' to make sure the
# domain application is well-formed. e.g.,
#   DOMAIN( DBound( [x,y], [xt,yt] ), DConstrain(..) )
#      is the same as
#   DOMAIN(        ..               , DInto(x,xt,DInto(y,yt,DConstrain(..))) )
# basically, when we see an 'unbound' variable in the 'RHS' , we should bind
# it with the default 'DInto'.
export Apply := module ()
       export ModuleApply :=
         proc(dom :: HDomain_mb, kb0 :: t_kb
             ,f_into := "default"
             ,f_body := "default", $)
           local vs, sh, ctx;
           if dom :: DomNoSol then
               error "cannot apply %1", dom;
           end if;
           vs, sh := op(dom);
           vs := Domain:-Bound:-withVarsIxs(vs);
           ctx := [ kb0,
              `if`(f_into="default",`do_mk`,f_into),
              `if`(f_body="default",`do_body`,f_body) ];
           (e->do_apply({}, e, vs, sh, ctx));
       end proc;

       export Shape := proc(dsh :: DomShape, e, $) ModuleApply( DOMAIN( [], dsh ), e ) end proc;
       export Bound := proc(dbn :: DomBound, e, $) ModuleApply( DOMAIN( dbn, DConstrain() ), e ) end proc;

       # main loop of the apply function
       # done_  := variables already integrated
       # e      := expr
       # vs     := domain bounds
       # sh     := domain shape
       # ctx[0] := KB (context for f_into/f_body)
       # f_into := how to make a DomInto
       # f_body := how to make the expression body
       local do_apply := proc(done__, e, vs, sh_, ctx, $)
           local sh := sh_, done_ := done__
               , r, cond, cond_outer, vn, vt, shv, vars, deps, ctx1, rn;
           # If the solution is a constraint, and the constraint is true,
           # then just produce the expression. If it isn't necessarily true
           # (i.e. trivial) then produce a Partition with the constraint as a
           # guard.
           if sh :: DomConstrain then
               vars := Domain:-Bound:-varsOf(vs,"set") minus done_;
               cond, cond_outer := select_cond_outer(sh, vars);
               # if there are still integrals which have not been applied, apply
               # them now
               do_constrain(cond_outer)(do_mks(e, (r,kb1) -> do_constrain(cond)(op(3,ctx)(r, kb1)), vars, vs, ctx))
           # if the solution is a sum of solutions, produce the algebraic sum
           # of each summand of the solution applied to the expression.
           elif sh :: DomSum then
               `+`(seq(do_apply(done_, e, vs, s, ctx), s=sh))
           # if the solution is a split solution, just make `do_apply' over
           # the values of the Partition (the subsolutions)
           elif sh :: DomSplit then
               Partition:-Amap(
                 [ (c,_)->c
                 , (p,c)->do_apply(done_, e, vs, p, applyop(kb->KB:-assert(c,kb),1,ctx))
                 , c->c ], op(1, sh) );
           # performs the 'make' on the expression after recursively
           # applying the solution
           elif sh :: DomInto then
               # deconstruction
               vn, vt, shv := op(sh);
               # extract bounds which have not been applied upon which this
               # bound depends. Those are applied after this one, so are not
               # in 'scope' in the recursive call
               vars := Domain:-Bound:-varsOf(vs,"set");
               deps := (indets(vt, DomBoundVar) intersect vars) minus done_ ;
               deps := `union`(deps, {vn});
               done_ := `union`(done_, deps) ;

               shv, cond_outer := select_cond_outer(shv, done_);

               # build this integral, and the other this one depended on, then
               # recursively apply
               do_constrain(cond_outer)(
                 do_mks(e, (r,kb1) -> do_apply(done_, r, vs, shv, subsop(1=kb1,ctx)),
                      deps, Domain:-Bound:-upd(vs, vn, vt), ctx));
           else
               error "don't know how to apply %1", sh
           end if;
       end proc;

       export do_mk := proc(mk, e, vn, ty_, _kb)
           Domain:-ExtBound[mk]:-DoMk(e, vn, ty_);
       end proc;

       export do_body := proc(e, _kb) e end proc;

       local do_constrain := proc(cond0::{list,set,DomConstrain},$)
         local mk_cond, cond := cond0;
         if nops(cond)=0 then
           mk_cond := x->x;
         else
           cond := bool_And(op(cond));
           mk_cond := x->PARTITION([Piece(cond,x), Piece(Not(cond),0)]);
         end if;
         mk_cond;
       end proc;

       # A very cute way of pulling constraints out over other constructors
       # which relies on the fact that constraints are required to be innermost;
       # i.e. DomShape is a sum of products; i.e. this could also be called
       # 'factoring'.
       local select_cond_outer := proc(sh::DomShape, vars0::set({name,list(name)}), $)
         local csd, cs0, cs, ots, sh1, ins, vars := vars0;
         vars := map(v->`if`(v::list,v,[v])[],vars);
         csd := [op(indets(sh, And(DomConstrain,Not(satisfies(x->has(x,vars))))))];
         cs0 := map(x->{op(x)},csd);
         if cs0=[] then return sh, {}; end if;
         cs := map(x->[selectremove(z->andmap(c->z in c,cs0),x)], cs0);
         ots := op([1,1],cs); ins := map(curry(op,2), cs);
         sh1 := subs(zip(`=`, csd, map(DConstrain@op,ins)), sh);
         userinfo(3, Domain, printf("select_cond_outer(%a, %a) = %a, %a\n", sh, vars, sh1, ots));
         sh1, ots;
       end proc;

       # Move into an integral by augmenting the KB with the variables bound by
       # that integral.
       local into_mk := proc(dbnd::DomBound, vn, vt, ctx, $)
           local kb, v_i, v_k, vn_, kb1, rn;
           kb := op(1,ctx); if kb :: t_not_a_kb then return KB:-NotAKB() end if;

           v_i := Domain:-Bound:-varIx(dbnd, vn);
           v_k := op([1,v_i,3], dbnd);
           vn_, kb1 := Domain:-ExtBound[v_k]:-MakeKB(vn, Domain:-ExtBound[v_k]:-SplitRange(vt), kb);

           rn := `if`(evalb(vn=vn_), [], [vn=vn_]);
           subsop(1=kb1, ctx), rn;
       end proc;

       local do_mks := proc(e, kont, todo::({list,set})(DomBoundVar), dbnd :: DomBound, ctx, $)
           local vs, v_td, i, vt, kb0, v_mk, _, ctx1, rn, r := e;

           if todo :: set then
             vs := select(v->v in todo,Domain:-Bound:-varsOf(dbnd));
             vs := ListTools[Reverse](vs);
           else
             vs := todo;
           end if;

           if nops(vs)=0 then
             return kont(r,op(1,ctx));
           end if;

           v_td := op(1,vs);
           vs   := subsop(1=NULL,vs);
           i    := Domain:-Bound:-varIx(dbnd, v_td);
           _,vt,v_mk := op(op([1,i], dbnd));

           ctx1, rn := into_mk(dbnd, v_td, vt, ctx);
           if rn <> [] then
             r := subs(rn,r);
           end if;

           r := do_mks(r, kont, vs, dbnd, ctx1);
           op(2,ctx)(v_mk, r, v_td, vt, op(1,ctx));
       end proc;
end module;
