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
               cond := `and`(op(sh));
               if is(cond) then
                   r := e
               else
                   r := PARTITION([Piece(cond,e), Piece(Not(cond),e)]);
               end if;
               # if there are still integrals which have not been applied,
               # apply them now
               vs_td := select(x -> not(op(1, x) in done_), op(1, vs));
               for v_td in vs_td do
                   vn_td, vt_td, vt_mk := op(v_td);
                   r := do_mk(r, vn_td, vt_td, vt_mk);
               end do;
               r;
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
               deps := (indets(vt, name) intersect vars) minus done_ ;
               done_ := `union`(done_, deps, {vn}) ;
               # recursively apply
               e1 := do_apply(done_, e, vs, shv);
               # build this integral, and the other this one depended on
               for v in op(1,vs) do
                   vvn, vvt, vmk := op(v);
                   if vvn in deps then
                       e1 := do_mk(e1, vvn, vvt, vmk);
                   elif vvn = vn then
                       e1 := do_mk(e1, vvn,  vt, vmk);
                   end if;
               end do;
               e1;
           else
               error "don't know how to apply %1", sh
           end if;
       end proc;

       local do_mk := proc(e, vn, ty_, mk, $)
           mk(e, Domain:-ExtBound[mk]:-MakeEqn(vn, ty_));
       end proc;
end module;
