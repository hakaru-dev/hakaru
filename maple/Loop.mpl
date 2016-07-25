# Teach Maple (through depends and eval) about our new binding forms.
# forall bind from 1st arg to 2nd arg.
# Ints,Sums,ints,sums bind from 2nd arg to 1st arg, and also from each element
#   of the 4th arg to the other elements on the left and to the 3rd arg.

`depends/forall` := proc(bvar, pred, x, $)
  depends(pred, x minus convert(bvar, 'set'))
end proc:

`depends/Ints` := proc(body, bvar, rng, loops, x, y, $)
  local xx, i;
  if nargs = 5 then
    xx := x; # y is ununsed and x lists the variables to look for
  else
    xx := y; # x is some KB and y lists the variables to look for
    if depends(x, y) then return true end if;
  end if;
  # don't remove bvar from xx!
  if depends(body, xx minus {bvar}) then return true end if;
  for i from nops(loops) to 1 by -1 do
    if depends(op([i,2],loops), xx) then return true end if;
    xx := xx minus {op([i,1],loops)};
  end do;
  depends(rng, xx)
end proc:
`depends/Sums` := eval(`depends/Ints`):
`depends/ints` := eval(`depends/Ints`):
`depends/sums` := eval(`depends/Ints`):

`eval/forall` := proc(e, eqs, $)
  local bvar, pred;
  bvar, pred := op(e);
  eval(op(0,e), eqs)(BindingTools:-generic_evalat(bvar, pred, eqs))
end proc:

`eval/Ints` := proc(e, eqs, $)
  local body, bvar, rng, loops, n, i;
  body, bvar, rng, loops := op(1..4, e);
  bvar, body := BindingTools:-generic_evalat(bvar, body, eqs);
  eval(op(0,e), eqs)(body, bvar,
                     BindingTools:-generic_evalatstar(rng, loops, eqs),
                     op(5..-1,e))
end proc:
`eval/Sums` := eval(`eval/Ints`):
`eval/ints` := eval(`eval/Ints`):
`eval/sums` := eval(`eval/Ints`):

`eval/Int` := proc(e, eqs, $)
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
`eval/Sum`     := eval(`eval/Int`):
`eval/Product` := eval(`eval/Int`):
`eval/int`     := eval(`eval/Int`):
`eval/sum`     := eval(`eval/Int`):
`eval/product` := eval(`eval/Int`):

#############################################################################

Loop := module ()
  option package;
  local intssums, enter_piecewise, wrap,
        Binder, Stmt, t_binder, t_stmt, t_exp,
        ModuleLoad;
  export
     # These first few are smart constructors (for themselves):
         ints, sums,
     # while these are "proper functions"
         mk_HArray, genLoop, unproducts, unproduct,
         peel, split, graft, rebase_lower, rebase_upper;
  # these names are not assigned (and should not be).  But they are
  # used as global names, so document that here.
  global Ints, Sums, csgn;
  uses Hakaru, KB;

  t_binder := 'Binder(identical(product, Product, sum, Sum), t_kb)';
  t_stmt   := 'Stmt(anything, list, list)';
  t_exp    := '{Stmt(identical(exp), [], []),
                Stmt(identical(`^`), [anything], [])}';

  ints := proc() intssums('ints', 'int', _passed) end proc;
  sums := proc() intssums('sums', 'sum', _passed) end proc;

  intssums := proc(makes::name, make::name,
                   ee::anything, xx::name, rr::range, ll::list(name=range),
                   kb::t_kb:=empty, $)
    local t, x, e, r, l, kb1, w0, pp;
    t := `if`(make=int, HReal(open_bounds(rr)), HInt(closed_bounds(rr)));
    x, kb1 := genType(xx, mk_HArray(t, ll), kb);
    e := eval(ee, xx=x);
    if nops(ll) > 0 then
      kb1 := assert(size(x)=op([-1,2,2],ll)-op([-1,2,1],ll)+1, kb1);
    end if;
    e := simplify_assuming(e, kb1);
    r, l, kb1 := genLoop(rr, ll, kb, 'Integrand'(x,e));
    w0, pp := unproducts(e, x, l, kb1);
    if depends(w0, x) then
      'makes'(e, x, rr, ll)
    else
      w0 * foldl(''product'', 'make'(pp,x=r), op(l))
    end if
  end proc;

  mk_HArray := proc(t::t_type, loops::list(name=range), $)
    local res, i;
    res := t;
    for i in loops do res := HArray(res) end do;
    res
  end proc;

  genLoop := proc(e, loops::list(name=range), kb::t_kb)
    local kb1, rng, ind, do_subst, i;
    kb1 := kb;
    rng := table();
    ind := table();
    do_subst := e -> foldl(((e,eq) -> eval(e, op([lhs(eq),1],loops)=rhs(eq))),
                           e, entries(ind, 'pairs'));
    for i from nops(loops) to 1 by -1 do
      rng[i] := do_subst(op([i,2],loops));
      ind[i], kb1 := genType(op([i,1],loops), HInt(closed_bounds(rng[i])),
                               kb1, _rest);
    end do;
    do_subst(e), zip(`=`, [entries(ind, 'nolist')],
                          [entries(rng, 'nolist')]), kb1
  end proc;

  unproducts := proc(w, x::name, loops::list(name=range), kb::t_kb, $)
    local w0, pp, j, w1, w2, loop;
    w0 := 1;
    pp := w;
    for j from nops(loops) to 1 by -1 do
      w1, pp := op(unproduct(pp, x, op(j,loops), [], `*`, kb, kb));
      # separate out each of the factors in w1, as they might have different
      # variable dependencies, which can be exploited by other routines
      w2 := convert(w1, 'list', '`*`');
      for loop in [op(j+1..-1, loops)] do
        w2 := map((w -> product(eval(w, x=idx(x,lhs(loop))), loop)), w2);
      end do;
      w0 := w0 * `*`(op(w2));
      # w0 := w0 * foldl(product, w1, op(j+1..-1, loops));
    end do;
    # Rewrite ... * piecewise(i<=kk-1, xs^2, 1)
    #      to ... * xs ^ (2*piecewise(i<=kk-1, 1))
    # because the latter is easier to integrate and recognize with respect to xs
    pp := maptype(`*`,
      proc (p)
        local n, s, r;
        if p :: 'And(specfunc(piecewise), anyfunc(freeof(x), anything, 1))' then
          n := indets(op(1,p),name);
          if op(2,p) :: {'exp(anything)', '`^`'('freeof'(n),'anything')} then
            s, r := selectremove(depends, convert(op([2,-1],p),'list','`*`'), n);
            subsop(-1 = `*`(piecewise(op(1,p), `*`(op(s))), op(r)), op(2,p))
          else
            s, r := selectremove(depends, convert(op(2,p),'list','`*`'), n);
            `*`(op(r)) ^ piecewise(op(1,p), 1)
              * `if`(nops(s) > 0, piecewise(op(1,p), `*`(op(s)), 1), 1)
          end if
        else
          p
        end if
      end proc,
      pp);
    w0, pp
  end proc;

  # Find [w1,pp] so that
  #   wrap(heap,w,mode,kb1,kb0)
  #   = w1*product(eval(pp,var=idx(var,lhs(loop))),loop)
  # making w1 depend on var as little as possible.
  # The flag "mode" should be `+` if "heap" contains an entry of the form
  # t_exp, or `*` otherwise.
  unproduct := proc(w, var::name, loop::(name=range),
                    heap::list, mode::identical(`*`,`+`),
                    kb1::t_kb, kb0::t_kb, $)
    local ind, res, dummy, kb, kbThen, i, w1, pp, s, r, x;
    if not depends(w, var) then
      return [wrap(heap, w, mode, kb1, kb0), 1]
    end if;
    ind := map2(op, 2, indets(w, idx(identical(var), anything)));
    if nops(ind) = 1 then
      ind := op(ind);
      # Make sure ind contains no bound variables before lifting it!
      # So, check that "extract using indets" and "rename using eval" commute.
      s := indets(ind, 'name');
      s := map(proc(x,$) local y; `if`(depends(ind,x), x=y, NULL) end proc, s);
      if indets(eval(w, s), idx(identical(var), anything))
                = {idx(var, eval(ind, s))} then
        kb  := assert(lhs(loop)=ind, kb1); # BUG! bijectivity assumed!
        res := subs(idx(var,ind) = idx(var,lhs(loop)), w);
        res := wrap(heap, res, mode, kb, kb0);
        res := subs(idx(var,lhs(loop))=dummy, res);
        if not depends(res, var) then
          return [1, subs(dummy=var, res)]
        end if
      end if
    end if;
    if w :: mode then
      res := map(unproduct, `if`(mode=`*`, list_of_mul(w,kb1), [op(w)]),
                 var, loop, heap, mode, kb1, kb0);
      return [`*`(op(map2(op,1,res))), `*`(op(map2(op,2,res)))]
    end if;
    if w :: 'specfunc(piecewise)' then
      kb := kb1;
      for i from 1 to nops(w) do
        if i :: even then
          kbThen := assert(    op(i-1,w) , kb);
          kb     := assert(Not(op(i-1,w)), kb);
          w1[i], pp[i] := op(unproduct(op(i,w),var,loop,heap,mode,kbThen,kb0))
        elif i = nops(w) then
          w1[i], pp[i] := op(unproduct(op(i,w),var,loop,heap,mode,kb    ,kb0))
        end if
      end do;
      return [`*`(entries(w1,'nolist')), `*`(entries(pp,'nolist'))]
    end if;
    if mode = `*` then
      if w :: (anything^freeof(var)) then
        return unproduct(op(1,w), var, loop,
                         [op(heap), Stmt(`^`, [], [op(2,w)])], `*`, kb1, kb0)
      elif w :: exp(anything) then
        return unproduct(op(1,w), var, loop,
                         [op(heap), Stmt(exp, [], [])], `+`, kb1, kb0)
      elif w :: (freeof(var)^anything) then
        return unproduct(op(2,w), var, loop,
                         [op(heap), Stmt(`^`, [op(1,w)], [])], `+`, kb1, kb0)
      end if
    end if;
    if mode = `+` and w :: `*` then
      s, r := selectremove(depends, w, var);
      if s :: `*` then
        # Nonlinear %1 (time to reread kiselyov-lifted?)
      else
        return unproduct(s, var, loop,
                         [op(heap), Stmt(`*`, [], [r])], `+`, kb1, kb0)
      end if
    end if;
    if w :: And(specfunc(`if`(mode = `*`, {product, Product}, {sum, Sum})),
                anyfunc(anything, name=range(freeof(var)))) then
      x, kb := genType(op([2,1],w),
                       HInt(Bound(`>=`,op([2,2,1],w)),
                            Bound(`<=`,op([2,2,2],w))),
                       kb1,
                       w, var, loop, heap);
      return unproduct(eval(op(1,w), op([2,1],w)=x), var, loop,
                       [op(heap), Binder(op(0,w), kb1)], mode, kb, kb0)
    end if;
    if mode = `*` and w :: '{`+`, specfunc({sum, Sum})}' then
      # Maybe this w is one of those big sums involving products that are
      # always equal to 1, left behind by the density of Categorical
      w1 := graft(split(peel(lift_piecewise(w))));
      w1 := combine(rebase_upper(w1));
      w1 := combine(rebase_lower(w1));
      return [wrap(heap, w1, mode, kb1, kb0), 1]
    end if;
    return [wrap(heap, w, mode, kb1, kb0), 1]
  end proc;

  enter_piecewise := proc(ee, kb0::t_kb, mode::identical(`*`,`+`), $)
    local e, kb, mo;
    e  := ee;
    kb := kb0;
    mo := mode();
    while e :: 'specfunc(piecewise)' and nops(e) = 3 do
      if op(3,e) = mo then
        kb := assert(op(1,e), kb);
        e := op(2,e);
      elif op(2,e) = mo then
        kb := assert(Not(op(1,e)), kb);
        e := op(3,e);
      else
        break;
      end if;
    end do;
    e, kb
  end proc;

  wrap := proc(heap::list, e1, mode1::identical(`*`,`+`),
               kb1::t_kb, kb0::t_kb, $)
    local e, kb, mode, i, entry, rest, var, new_rng, make,
       dom_spec, w, arrrgs;
    e    := e1;
    kb   := kb1;
    mode := mode1;
    for i from nops(heap) to 1 by -1 do
      entry := op(i,heap);
      if entry :: t_binder then
        if not (op(1,entry) in `if`(mode=`+`, {sum,Sum},
                                              {product,Product})) then
          print("Warning: heap mode inconsistency", heap, mode1)
        end if;
        e := simplify_assuming(e, op(2,entry));
        e, kb := enter_piecewise(e, kb, mode);
        rest := kb_subtract(kb, op(2,entry));
        new_rng, rest := selectremove(type, rest,
          {[identical(genType), name, specfunc(HInt)],
           [identical(genLet), name, anything]});
        if not (new_rng :: [list]) then
          error "kb_subtract should return exactly one gen*"
        end if;
        new_rng := op(new_rng);
        var     := op(2,new_rng);
        if op(1,new_rng) = genType then
          make    := op(1,entry);
          new_rng := range_of_HInt(op(3,new_rng));
        else # op(1,new_rng) = genLet
          make    := eval;
          new_rng := op(3,new_rng);
        end if;
        dom_spec, rest := selectremove(depends,
          map(proc(a::[identical(assert),anything],$) op(2,a) end proc, rest),
          var);
        (e, w) := selectremove(depends, convert(e, 'list', `*`), var);
        w := `*`(op(w));
        if mode = `*` and not (w = 1) then
          w := w ^ `if`(make=eval,eval,sum)
                       (piecewise_And(dom_spec, 1, 0), var=new_rng);
        end if;
        e := w * make(piecewise_And(dom_spec, `*`(op(e)), mode()), var=new_rng);
        kb := foldr(assert, op(2,entry), op(rest));
      elif entry :: t_stmt then
        # We evaluate arrrgs first, in case op(1,stmt) is an operation (such as
        # piecewise) that looks ahead at how many arguments it is passed before
        # they are evaluated.
        arrrgs := op(op(2,entry)), e, op(op(3,entry));
        e      := op(1,entry)(arrrgs);
        if entry :: t_exp then
          if mode <> `+` then
            print("Warning: heap mode inconsistency?", heap, mode1)
          end if;
          mode := `*`;
        end if
      else error "Malformed heap entry %1", entry end if
    end do;
    if mode <> `*` then
      print("Warning: heap mode inconsistency??", heap, mode1)
    end if;
    e, kb := enter_piecewise(e, kb, mode);
    rest := kb_subtract(kb, kb0);
    rest := map(proc(a::[identical(assert),anything],$) op(2,a) end proc, rest);
    piecewise_And(rest,e,mode())
  end proc;

  # Rewrite product(piecewise(i+42=lo+42,th,el),i=lo..hi)
  # to eval(th,i=lo)*product(el,i=lo+1..hi)
  peel := proc(ee, $)
    subsindets(ee, 'And(specfunc({sum,Sum,product,Product}),
                        anyfunc(specfunc(piecewise), name=range))',
    proc(e, $)
      local body, x, r, line, test, make, here, rest, res;
      body := op(1,e);
      if not (1<nops(body) and op(1,body)::{`=`,`<`,`<=`}) then return e end if;
      x, r := op(op(2,e));
      line := op([1,1],body) - op([1,2],body);
      if 1 = degree(line, x) then
        if op(1,body) :: `=`  then
          test := proc (y,z,$)
            if Testzero(eval(line, x=y)) then true
            else FAIL end if
          end proc;
        elif op(1,body) :: `<` then
          test := proc (y,z,$)
            local l;
            l := [eval(line, x=y), eval(line, x=z)];
            if   l :: [negative, nonnegative] then true
            elif l :: [nonnegative, negative] then false
            else FAIL end if
          end proc;
        elif op(1,body) :: `<=` then
          test := proc (y,z,$)
            local l;
            l := [eval(line, x=y), eval(line, x=z)];
            if   l :: [nonpositive, positive] then true
            elif l :: [positive, nonpositive] then false
            else FAIL end if
          end proc;
        end if;
        if op(0,e) in {sum,Sum} then
          make := `+`;
        elif op(0,e) in {product,Product} then
          make := `*`;
        end if;
        here := op(2,body);
        if nops(body)=2 then
          rest := 0;
        elif nops(body)=3 then
          rest := op(3,body);
        elif {op([1,0],body) , op([3,0],body)} = {`<`, `<=`}
          and op([1,1],body) = op([3,2],body)
          and op([1,2],body) = op([3,1],body) then
          rest := op(4,body);
        else
          rest := subsop(1=NULL,2=NULL,body);
        end if;
        res := test(lhs(r), lhs(r)+1);
        if res <> FAIL then
          return make(eval(`if`(res, here, rest), x=lhs(r)),
                      subsop(1 = `if`(res, rest, here), [2,2,1]=lhs(r)+1, e));
        end if;
        res := test(rhs(r), rhs(r)-1);
        if res <> FAIL then
          return make(eval(`if`(res, here, rest), x=rhs(r)),
                      subsop(1 = `if`(res, rest, here), [2,2,2]=rhs(r)-1, e));
        end if;
      end if;
      e
    end proc);
  end proc:

  # Expand sum(a*(b-c),q) to sum(a*b,q)-sum(a*c,q)
  split := proc(ee, $)
    subsindets(ee, 'And(specfunc({sum,Sum}),
                        anyfunc(And(`*`,Not(`*`(Not(`+`)))),name=anything))',
    proc(e, $)
      local terms, x;
      terms := convert(expand(op(1,e), op(indets(op(1,e), function))),
                       'list', `+`);
      x := op([2,1],e);
      `+`(op(map(proc(term, $)
        local s, r;
        s, r := selectremove(depends, convert(term, 'list', `*`), x);
        `*`(op(r), subsop(1=`*`(op(s)),e))
      end proc, terms)))
    end proc)
  end proc:

  # Simplify f(lo-1)*product(f(i),i=lo..hi) to product(f(i),i=lo-1..hi)
  graft := proc(ee, $)
    subsindets(ee, 'Or(And(`*`,Not(`*`(Not(specfunc({product,Product}))))),
                       And(`+`,Not(`+`(Not(specfunc({sum    ,Sum    }))))))',
    proc(e, $)
      local produce, factors, i, j;
      produce := `if`(e::`*`, '{product,Product}',
                              '{sum    ,Sum    }');
      factors := sort(convert(e,'list'),
                      key = (factor -> -numboccur(factor,produce)));
      for i from nops(factors) to 2 by -1 do
        for j from i-1 to 1 by -1 do
          if op(j,factors) :: 'And'('specfunc'(produce),
                                    'anyfunc(anything,name=range)') then
            if Testzero(op(i,factors) - eval(op([j,1],factors),
                 op([j,2,1],factors)=op([j,2,2,1],factors)-1)) then
              factors := subsop(i=NULL,applyop(`-`,[j,2,2,1],factors,1))
            elif Testzero(op(i,factors) - eval(op([j,1],factors),
                   op([j,2,1],factors)=op([j,2,2,2],factors)+1)) then
              factors := subsop(i=NULL,applyop(`+`,[j,2,2,2],factors,1))
            end if
          end if
        end do
      end do;
      op(0,e)(op(factors))
    end proc)
  end proc:

  # Normalize sum(f(i),i=2..hi) to sum(f(i+2),i=0..hi-2)
  rebase_lower := proc(ee, $)
    subsindets(ee, 'And(specfunc({sum,Sum,product,Product}),
                        anyfunc(anything,
                          name=Not({0,SymbolicInfinity,undefined})..anything))',
    proc(e, $)
      subsop([2,2,1]=0,
             applyop(`-`,
                     [2,2,2],
                     applyop(eval, 1, e, op([2,1],e)=op([2,1],e)+op([2,2,1],e)),
                     op([2,2,1],e)))
    end proc)
  end proc:

  # Normalize sum(f(i),i=lo..2) to sum(f(i+2),i=lo-2..0)
  rebase_upper := proc(ee, $)
    subsindets(ee, 'And(specfunc({sum,Sum,product,Product}),
                        anyfunc(anything,
                          name=anything..Not({0,SymbolicInfinity,undefined})))',
    proc(e, $)
      subsop([2,2,2]=0,
             applyop(`-`,
                     [2,2,1],
                     applyop(eval, 1, e, op([2,1],e)=op([2,1],e)+op([2,2,2],e)),
                     op([2,2,2],e)))
    end proc)
  end proc:

  ModuleLoad := proc($)
    # Override csgn to work a little bit harder on piecewise and sum
    # (to get rid of csgn(1/2+1/2*sum(piecewise(...,1,0),...))
    #  produced by int on a Gaussian mixture model)
    unprotect(csgn);
    csgn := overload([
      # Handle if the csgn of a piecewise doesn't depend on which branch
      proc(a :: specfunc(piecewise), $)
        option overload;
        local r, i;
        r := {seq(`if`(i::even or i=nops(a), csgn(op(i,a)), NULL),
                  i=1..nops(a))};
        if nops(r)=1 then return op(r) end if;
        if not assigned(_Envsignum0) then
          r := r minus {0};
          if nops(r)=1 then return op(r) end if;
        end if;
        error "invalid input: cannot csgn %1", a;
      end proc,
      # Handle if the csgn of a sum doesn't depend on the bound variable
      proc(a :: And(specfunc({sum, Sum}), anyfunc(anything, name=range)), $)
        option overload;
        local r;
        r := csgn(op(1,a));
        if not depends(r,op([2,1],a)) then
          return signum(op([2,2,2],a)+1-op([2,2,1],a)) * r
        end if;
        error "invalid input: cannot csgn %1", a;
      end proc,
      csgn]);
    protect(csgn);
  end proc;

  ModuleLoad();

end module; # Loop
