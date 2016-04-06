# Teach Maple (through depends and eval) about our new binding forms.
# forall bind from 1st arg to 2nd arg.
# Ints,Sums,ints,sums bind from 2nd arg to 1st arg, and also from each element
#   of the 4th arg to the other elements on the left and to the 3rd arg.

`depends/forall` := proc(bvar, pred, x)
  depends(pred, x minus convert(bvar, 'set'))
end proc:

`depends/Ints` := proc(body, bvar, rng, loops, x)
  local xx, i;
  if depends(body, x minus {bvar}) then return true end if;
  xx := x; # don't remove bvar from xx!
  for i from nops(loops) to 1 by -1 do
    if depends(op([i,2],loops), xx) then return true end if;
    xx := xx minus {op([i,1],loops)};
  end do;
  depends(rng, xx)
end proc:
`depends/Sums` := `depends/Ints`:
`depends/ints` := `depends/Ints`:
`depends/sums` := `depends/Ints`:

`eval/forall` := proc(e, eqs)
  local bvar, pred;
  bvar, pred := op(e);
  eval(op(0,e), eqs)(BindingTools:-generic_evalat(bvar, pred, eqs))
end proc:

`eval/Ints` := proc(e, eqs)
  local body, bvar, rng, loops, n, i;
  body, bvar, rng, loops := op(e);
  bvar, body := BindingTools:-generic_evalat(bvar, body, eqs);
  eval(op(0,e), eqs)(body, bvar, BindingTools:-generic_evalatstar(rng, loops, eqs))
end proc:
`eval/Sums` := `eval/Ints`:
`eval/ints` := `eval/Ints`:
`eval/sums` := `eval/Ints`:

`eval/Int` := proc(e, eqs)
  local body, bound, bvar;
  body, bound := op(1..2, e);
  if bound :: name then
    bound, body := BindingTools:-generic_evalat(bound, body, eqs);
  elif bound :: `=` then
    bvar := lhs(bound);
    bvar, body := BindingTools:-generic_evalat(bvar, body, eqs);
    bound := bvar = eval(rhs(bound), eqs);
  else
    body, bound := BindingTools:-generic_evalatstar(body, bound, eqs);
  end if;
  eval(op(0,e), eqs)(body, bound, op(eval([op(3..-1,e)], eqs)))
end proc:
`eval/Sum` := `eval/Int`:
`eval/int` := `eval/Int`:
`eval/sum` := `eval/Int`:

#############################################################################

Loop := module ()
  option package;
  local wrap, statement_info, Stmt, t_binder;
  export
     # These first few are smart constructors (for themselves):
         ints, sums, unproducts, unproduct;
  # these names are not assigned (and should not be).  But they are
  # used as global names, so document that here.
  global Ints, Sums;
  uses KB;

  t_binder:= 'Stmt(identical(product,Product,sum,Sum), [], [name=range])';

  ints := proc(e::anything, x::name, r::range, l::list(name=range))
    local w0, pp;
    w0, pp := unproducts(e, x, l);
    if depends(w0, x) then
      'procname(_passed)'
    else
      w0 * foldl(product, int(pp,x=r), op(l))
    end if
  end proc;

  sums := proc(e::anything, x::name, r::range, l::list(name=range))
    local w0, pp;
    w0, pp := unproducts(e, x, l);
    if depends(w0, x) then
      'procname(_passed)'
    else
      w0 * foldl(product, sum(pp,x=r), op(l))
    end if
  end proc;

  unproducts := proc(w, x::name, loops::list(name=range))
    local w0, pp, j, w1, xx;
    w0 := 1;
    pp := w;
    for j from nops(loops) to 1 by -1 do
      w1, pp := op(unproduct(pp, x, op(j,loops), [], `*`));
      w0 := w0 * foldl(product, w1, op(j+1..-1, loops));
    end do;
    w0, pp
  end proc;

  # Find [w1,pp] so that
  #   foldl(wrap,w,op(heap)) = w1*product(eval(pp,var=idx(var,lhs(loop))),loop)
  # making w1 depend on var as little as possible.
  # The flag "mode" should be `+` if "heap" contains an entry of the form
  # {Stmt(exp,[],[]), Stmt(`^`,[anything],[])}, or `*` otherwise.
  unproduct := proc(w, var::name, loop::(name=range),
                    heap::list(Stmt(anything,list,list)),
                    mode::identical(`*`,`+`))
    local ind, x, s, r, narrow, wide, eq, as, res, dummy;
    if not depends(w, var) then
      return [foldr(wrap, w, op(heap)), 1]
    end if;
    ind := map2(op, 2, indets(w, Hakaru:-idx(identical(var), anything)));
    if nops(ind) = 1 then
      ind := op(ind);
      x := indets(ind, name) intersect
           {op(map2(op, [3,1,1], select(type, heap, t_binder)))};
      wide := rhs(loop);
      wide := And(lhs(wide) <= lhs(loop), lhs(loop) <= rhs(wide));
      if nops(x) = 1 then
        x := op(x);
        ind := ind - x;
        if not depends(ind, x) then
          for r from 1 to nops(heap) do
            if op(r,heap)::t_binder and op([r,3,1,1],heap)=x then break end if
          end do;
          s := op(r,heap);
          # We want to change the product/sum over x to a product over
          # lhs(loop), so we want to set lhs(loop)=x+ind, and we need to
          # extend the range x=op([3,1,2],s) to match lhs(loop)=rhs(loop).
          narrow := map(`+`, op([3,1,2],s), ind);
          narrow := And(lhs(narrow) <= lhs(loop), lhs(loop) <= rhs(narrow));
          eq := x = lhs(loop) - ind;
          as := eval(map(statement_info, subsop(r=NULL, heap)), eq);
          as := foldr(assert, empty, op(as)); # not ideal usage of KB...
          if true #= simplify_assuming(wide,
             #assert(And(lhs(loop)::integer, narrow), as))
             # TODO: The array bounds check above is disabled (i.e., we run the
             # risk of indexing into an array out of bounds) until we improve
             # simplify_assumption to handle <> better:
             # > KB:-simplify_assuming(0<=i, KB:-assert(And(i::integer, -1<=i, -1<>i), KB:-empty))
             # 0 <= i
             # > KB:-simplify_assuming(0<=i, KB:-assert(And(i::integer, -1<=i, -1<i), KB:-empty))
             # true
             then
            res := eval(foldr(wrap, w, op(r+1..-1, heap)), eq);
            res := simplify_assuming(piecewise(narrow, res,
              `if`(op(1,s) in {product,Product}, 1, 0)),
              assert(And(lhs(loop)::integer, wide), as));
            res := foldr(wrap, res, op(1..r-1, heap));
            res := subs(Hakaru:-idx(var,lhs(loop))=dummy, res);
            if not depends(res, var) then
              return [1, subs(dummy=var, res)]
            end if
          end if
        end if
      elif nops(x) = 0 then
        # Use piecewise to force lhs(loop)=ind
        as := map(statement_info, heap);
        as := foldr(assert, empty, op(as)); # not ideal usage of KB...
        if true = simplify_assuming(eval(wide, lhs(loop)=ind), as) then
          res := foldr(wrap, w, op(heap));
          res := piecewise(lhs(loop)=ind, res, 1);
          res := subs(Hakaru:-idx(var,ind)=dummy, res);
          if not depends(res, var) then
            return [1, subs(dummy=var, res)]
          end if
        end if
      end if
    end if;
    if w :: mode then
      res := map(unproduct, [op(w)], var, loop, heap, mode);
      return [`*`(op(map2(op,1,res))), `*`(op(map2(op,2,res)))]
    end if;
    if w :: 'specfunc(piecewise)' then
      res := [seq(`if`(r::even or r=nops(w),
                       unproduct(op(r,w), var, loop,
                         [op(heap), Stmt(piecewise,
                           [seq(`if`(s::even, mode(), op(s,w)), s=1..r-1)],
                           `if`(r::even, [mode()], []))],
                         mode),
                       NULL),
              r=1..nops(w))];
      return [`*`(op(map2(op,1,res))), `*`(op(map2(op,2,res)))]
    end if;
    if mode = `*` then
      if w :: (anything^freeof(var)) then
        return unproduct(op(1,w), var, loop,
                         [op(heap), Stmt(`^`, [], [op(2,w)])], `*`)
      elif w :: exp(anything) then
        return unproduct(op(1,w), var, loop,
                         [op(heap), Stmt(exp, [], [])], `+`)
      elif w :: (freeof(var)^anything) then
        return unproduct(op(2,w), var, loop,
                         [op(heap), Stmt(`^`, [op(1,w)], [])], `+`)
      end if
    end if;
    if mode = `+` and w :: `*` then
      s, r := selectremove(depends, w, var);
      if s :: `*` then
        # Nonlinear %1 (time to reread kiselyov-lifted?)
      else
        return unproduct(s, var, loop,
                         [op(heap), Stmt(`*`, [], [r])], `+`)
      end if
    end if;
    if w :: And(specfunc(`if`(mode = `*`, {product, Product}, {sum, Sum})),
                anyfunc(anything, name=freeof(var))) then
      x := op([2,1],w);
      if depends([_passed], x) then x := gensym(x) end if;
      return unproduct(eval(op(1,w), op([2,1],w)=x), var, loop,
                       [op(heap), Stmt(op(0,w), [], [x=op([2,2],w)])], mode)
    end if;
    return [foldr(wrap, w, op(heap)), 1]
  end proc;

  wrap := proc(stmt :: Stmt(anything,list,list), w)
    local arrrgs;
    arrrgs := op(op(2,stmt)), w, op(op(3,stmt)); # in case op(1,stmt)=piecewise
    op(1,stmt)(arrrgs);
  end proc;

  statement_info := proc(stmt)
    local var, bnds, i;
    if stmt :: t_binder then
      var, bnds := op(op([3,1], stmt));
      var :: integer, lhs(bnds) <= var, var <= rhs(bnds)
    elif stmt :: Stmt(identical(piecewise), list, list) then
      seq(`if`(i::odd, `if`(i=nops(op(2,stmt)),
                            op([2,i],stmt),
                            Not(op([2,i],stmt))),
               NULL),
          i=1..nops(op(2,stmt)))
    else
      NULL
    end if
  end proc;

end module; # NewSLO
