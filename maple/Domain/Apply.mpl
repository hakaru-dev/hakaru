# Apply a domain to an expression.
# Apply will perform certain 'simplifications' to make sure the
# domain application is well-formed. e.g.,
#   DOMAIN( DBound( [x,y], [xt,yt] ), DConstrain(..) )
#      is the same as
#   DOMAIN(        ..               , DInto(x,xt,DInto(y,yt,DConstrain(..))) )
# basically, when we see an 'unbound' variable in the 'RHS' , we should bind
# it with the default 'DInto'.
export Apply := module ()
       export ModuleApply := proc(dom :: HDomain_mb, $)
           local vs, sh, `expression body`;
           if dom :: DomNoSol then
               error "cannot apply %1", dom;
           end if;
           vs, sh := op(dom);
           vs := Domain:-Bound:-withVarsIxs(vs);
           unapply(do_apply({}, `expression body`, vs, sh), `expression body`);
       end proc;

       export Shape := proc(dsh :: DomShape, e, $) ModuleApply( DOMAIN( [], dsh ), e ) end proc;
       export Bound := proc(dbn :: DomBound, e, $) ModuleApply( DOMAIN( dbn, DConstrain() ), e ) end proc;

       # main loop of the apply function
       # e     := expr
       # vs    := variables
       # vs_ty := domain bounds (as a kb)
       # sh    := domain shape
       local do_apply := proc(done__, e, vs, sh_, $)
           local sh := sh_, done_ := done__
               , cond, r, vs_td, v_td, vn_td, vt_td, vt_mk, vn, vt, shv, vars, deps
               , e1, v, vvn, vvt, vmk,  with_kb1 ;
           # If the solution is a constraint, and the constraint is true,
           # then just produce the expression. If it isn't necessarily true
           # (i.e. trivial) then produce a Partition with the constraint as a
           # guard.
           if sh :: DomConstrain then
               cond := remove(is, sh);
               if cond = DConstrain() then
                   r := e;
               else
                   cond := bool_And(op(sh));
                   r := PARTITION([Piece(cond,e), Piece(Not(cond),0)]);
               end if;
               # if there are still integrals which have not been applied, apply
               # them now
               do_mks(r, vs_td, {op(Domain:-Bound:-varsOf(vs_td))} minus done_);
           # if the solution is a sum of solutions, produce the algebraic sum
           # of each summand of the solution applied to the expression.
           elif sh :: DomSum then
               `+`(seq(do_apply(done_, e, vs, s), s=sh))
           # if the solution is a split solution, just make `do_apply' over
           # the values of the Partition (the subsolutions)
           elif sh :: DomSplit then
               sh := op(1, sh);
               Partition:-Pmap(p-> do_apply(done_, e, vs, p), sh);
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
               e1 := do_apply(done_, e, vs, shv);
               # build this integral, and the other this one depended on
               vs := Domain:-Bound:-upd(vs, vn, vt);
               do_mks(e1, deps, vs);
           else
               error "don't know how to apply %1", sh
           end if;
       end proc;

       local do_mk := proc(e, vn, ty_, mk, $)
           Domain:-ExtBound[mk]:-DoMk(e, vn, ty_);
       end proc;

       local do_mks := proc(e, todo::set(DomBoundVar), dbnd :: DomBound, $)
           local v_td, i, vt, v_mk, _, r := e;
           for v_td in todo do
             i := varIx(dbnd, v_td);
             _, vt, v_mk := op([1,i], dbnd)[];
             r := do_mk(r, v_td, vt, v_mk);
           end do;
           r;
       end proc;
end module;
