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
               , r, cond, vn, vt, shv, vars, deps, ctx1, rn;
           # If the solution is a constraint, and the constraint is true,
           # then just produce the expression. If it isn't necessarily true
           # (i.e. trivial) then produce a Partition with the constraint as a
           # guard.
           if sh :: DomConstrain then
               r := op(3,ctx)(e, op(1,ctx));
               cond := remove(is, sh);
               if cond = DConstrain() then
                   r := r;
               else
                   cond := bool_And(op(sh));
                   r := PARTITION([Piece(cond,r), Piece(Not(cond),0)]);
               end if;
               # if there are still integrals which have not been applied, apply
               # them now
               do_mks(r, {op(Domain:-Bound:-varsOf(vs))} minus done_, vs, ctx);
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
               vars := {op(Domain:-Bound:-varsOf(vs))};
               deps := (indets(vt, DomBoundVar) intersect vars) minus done_ ;
               done_ := `union`(done_, deps, {vn}) ;
               # recursively apply
               ctx1, rn := into_mk(vs, vn, vt, ctx);
               r := `if`(rn<>[],%subs(rn,e),e);
               r := do_apply(done_, r, vs, shv, ctx1);
               # build this integral, and the other this one depended on
               deps := `union`(deps, {vn});
               do_mks(r, deps, Domain:-Bound:-upd(vs, vn, vt), ctx);
           else
               error "don't know how to apply %1", sh
           end if;
       end proc;

       local do_mk := proc(mk, e, vn, ty_, kb, $)
           Domain:-ExtBound[mk]:-DoMk(e, vn, ty_);
       end proc;

       local do_body := proc(e, kb, $) e end proc;

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

       local do_mks := proc(e, todo::set(DomBoundVar), dbnd :: DomBound, ctx, $)
           local v_td, i, vt, v_mk, _, r := e;
           for v_td in todo do
             i := Domain:-Bound:-varIx(dbnd, v_td);
             _, vt, v_mk := op(op([1,i], dbnd));
             r := op(2,ctx)(v_mk, r, v_td, vt, op(1,ctx));
           end do;
           r;
       end proc;
end module;
