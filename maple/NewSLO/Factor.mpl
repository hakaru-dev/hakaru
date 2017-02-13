
  # Like simplify_assuming, but does a lot of hack-y things
  simplify_factor_assuming := module ()

    export ModuleApply;
    local graft_pw, GAMMAratio, wrap, hack_Beta,
          bounds_are_simple, eval_piecewise, eval_factor;

$include "NewSLO/Beta.mpl"

    # Rewrite piecewise(i<=j-1,1,0) + piecewise(i=j,1,0) + ...
    #      to piecewise(i<=j,1,0) + ...
    # and rewrite piecewise(And(i<=j-1,a<b),1) + piecewise(And(a<b,i=j),1) + ...
    #          to piecewise(And(i<=j,a<b),1) + ...
    graft_pw := proc(ee, $)
      subsindets(ee, 'And(`+`, Not(`+`(Not(specfunc(piecewise)))))', proc(e, $)
        local terms, j, i, jcond, icond, conds;
        terms := sort(convert(e,'list'),
                      key = proc(term, $) local rel; -add(numboccur(term,rel), rel in indets(term,`<=`)) end proc);
        for i from nops(terms) to 2 by -1 do
          if not (op(i,terms) :: 'And(specfunc(piecewise), Or(anyfunc(anything,1), anyfunc(anything,1,0)))') then next end if;
          icond := op([i,1],terms);
          icond := `if`(icond :: 'specfunc(And)', {op(icond)}, {icond});
          for j from i-1 to 1 by -1 do
            if not (op(j,terms) :: 'And(specfunc(piecewise), Or(anyfunc(anything,1), anyfunc(anything,1,0)))') then next end if;
            jcond := op([j,1],terms);
            jcond := `if`(jcond :: 'specfunc(And)', {op(jcond)}, {jcond});
            conds := jcond intersect icond;
            jcond := jcond minus conds;
            icond := icond minus conds;
            if not (nops(jcond) = 1 and nops(icond) = 1) then next end if;
            jcond := op(jcond);
            icond := op(icond);
            if not (jcond :: `<=` and icond :: `=`) then next end if;
            if not Testzero(`-`(op(jcond)) - `-`(op(icond)) - 1) then next end if; # Unsound HACK: assuming integers, so jcond<=-1 is equivalent to jcond<0
            terms := subsop(i=NULL, [j,1]=maptype('specfunc(And)', (c -> `if`(c=jcond, subsop(0=`<=`,icond), c)), op([j,1],terms)), terms);
            break
          end do
        end do;
        `+`(op(terms))
      end proc)
    end proc;

    # GAMMAratio(s, r) = GAMMA(s+r) / GAMMA(r)
    GAMMAratio := proc(s, r, $)
      local var;
      if s :: t_piecewiselike then
        map_piecewiselike(GAMMAratio,
          `if`(s :: 'specfunc(piecewise)' and nops(s) :: even, 'piecewise'(op(s), 0), s),
          r)
      elif s :: 'numeric' then
        product(var+r, var=0..s-1)
      else
        var := 'j';
        if has(r, var) then var := gensym(var) end if;
        Product(var+r, var=0..s-1) # inert so as to not become GAMMA
      end if
    end proc;

    wrap := proc(e, loops :: list([identical(product,Product,sum,Sum),
                                   name=range]), $)
      local res, loop;
      res := e;
      for loop in loops do
        res := op(1,loop)(res, op(2,loop));
      end do;
      res
    end proc;

    bounds_are_simple := proc(bounds :: range, $)
      local bound, term, i;
      if `-`(op(bounds)) :: integer then return true end if;
      for bound in bounds do
        for term in convert(bound, 'list', `+`) do
          if term :: `*` then term := remove(type, term, integer) end if;
          if term :: 'specfunc(piecewise)' then
            for i from 2 by 2 to nops(term)-1 do
              if not(op(i,term) :: integer) then return false end if
            end do;
            if not(op(-1,term) :: integer) then return false end if
          elif not(term :: integer) then return false end if
        end do
      end do;
      true
    end proc;

    # eval_piecewise has the same calling convention as eval_factor.
    # It simplifies piecewise expressions.
    eval_piecewise := proc(e :: specfunc(piecewise),
                           kb :: t_kb, mode :: identical(`*`,`+`),
                           loops :: list([identical(product,Product,sum,Sum),
                                          name=range]),
                           $)
      local default, kbs, pieces, i, cond, inds, res, x, b, a;
      default := 0; # the catch-all "else" result
      kbs[1] := kb;
      for i from 1 by 2 to nops(e) do
        if i = nops(e) then
          default := op(i,e);
          pieces[i] := default;
        else
          # Simplify piecewise conditions using KB
          cond := op(i,e);
          # cond := eval_factor(cond, kbs[i], `+`, []);
          kbs[i+1] := assert(cond, kbs[i]);
          cond := map(proc(cond::[identical(assert),anything], $)
                        op(2,cond)
                      end proc,
                      kb_subtract(kbs[i+1], kbs[i]));
          if nops(cond) = 0 then
            default := op(i+1,e);
            pieces[i] := default;
            break;
          else
            cond := `if`(nops(cond)=1, op(1,cond), And(op(cond)));
            # TODO: Extend KB interface to optimize for
            #       entails(kb,cond) := nops(kb_subtract(assert(cond,kb),kb))=0
            kbs[i+2] := assert(Not(cond), kbs[i]);
            if nops(kb_subtract(kbs[i+2], kbs[i])) > 0 then
              pieces[i] := cond;
              pieces[i+1] := op(i+1,e);
            else
              # This condition is false in context, so delete this piece
              # by not putting anything inside "pieces"
            end if
          end if
        end if
      end do;
      # Combine duplicate branches at end
      inds := [indices(pieces, 'nolist', 'indexorder')];
      for i in ListTools:-Reverse(select(type, inds, 'even')) do
        if Testzero(pieces[i]-default) then
          pieces[i  ] := evaln(pieces[i  ]);
          pieces[i-1] := evaln(pieces[i-1]);
        else
          break;
        end if
      end do;
      # Special processing for when the pieces are few
      res := [entries(pieces, 'nolist', 'indexorder')];
      if nops(res) <= 1 then
        return eval_factor(default, kb, mode, loops);
      end if;
      if nops(res) <= 3 and op(1,res) :: `=` and Testzero(default - mode()) then
        # Reduce product(piecewise(i=3,f(i),1),i=1..10) to f(3)
        for i from 1 to nops(loops) do
          x := op([i,2,1],loops);
          if depends(op(1,res), x) then
            if ispoly(`-`(op(op(1,res))), 'linear', x, 'b', 'a') then
              b := Normalizer(-b/a);
              if nops(kb_subtract(assert(And(b :: integer,
                                             op([i,2,2,1],loops) <= b,
                                             b <= op([i,2,2,2],loops)),
                                         kb), kb)) = 0 then
                return eval_factor(eval(op(2,res), x=b),
                                   assert(x=b, kb), # TODO: why not just use kb?
                                   mode,
                                   eval(subsop(i=NULL, loops), x=b));
              end if;
            end if;
            break;
          end if;
        end do;
      end if;
      # Recursively process pieces
      inds := [indices(pieces, 'nolist', 'indexorder')];
      for i in inds do
        if i::even or i=op(-1,inds) then
          pieces[i] := eval_factor(pieces[i], kbs[i], mode, []);
        end if;
      end do;
      res := piecewise(entries(pieces, 'nolist', 'indexorder'));
      for i in loops do res := op(1,i)(res, op(2,i)) end do;
      return res;
    end proc;

    # eval_factor is a simplifier.  It maintains the following invariants:
    #   eval_factor(e, kb, mode, []) = e
    #   eval_factor(e, kb, `*` , [...,[product,i=lo..hi]])
    #     = product(eval_factor(e, kb, `*`, [...]), i=lo..hi)
    #   eval_factor(e, kb, `+` , [...,[sum    ,i=lo..hi]])
    #     = sum    (eval_factor(e, kb, `+`, [...]), i=lo..hi)
    # It recursively traverses e while "remembering" the loops traversed,
    # as ``context'' information, to help with transformations.
    eval_factor := proc(e, kb :: t_kb, mode :: identical(`*`,`+`), loops, $)
      local o, body, x, bounds, res, go, y, kb1, i, j, k, s, r;
      if not (loops :: 'list'([`if`(mode=`*`, 'identical(product,Product)',
                                              'identical(sum    ,Sum    )'),
                               'name=range'])) then
        error "invalid input: mode=%1, loops=%2", mode, loops;
      end if;
      if e :: mode then
        # Transform product(a*b,...) to product(a,...)*product(b,...)
        # (where e=a*b and loops=[[product,...]])
        return map(eval_factor, e, kb, mode, loops);
      end if;
      if e = mode () then
        return e;
      end if;
      if e :: And(specfunc(`if`(mode=`*`, '{product,Product}', '{sum,Sum}')),
                    'anyfunc(anything, name=range)') then
        o := op(0,e);
        body, bounds := op(e);
        x, bounds := op(bounds);
        bounds := map(eval_factor, bounds, kb, `+`, []);
        if bounds_are_simple(bounds) then
          # Expand {product,sum} to {mul,add}
          if o=Product then o:=product elif o=Sum then o:=sum end if;
          bounds := lift_piecewise(bounds,
                      'And(range, Not(range(Not(specfunc(piecewise)))))');
          res := `if`(bounds :: 'specfunc(piecewise)', map_piecewiselike, apply)
                     ((b -> o(go(x), x=b)), bounds);
          # Work around this bug:
          # > product(Sum(f(j),j=0..n-1),j=0..0)
          # Sum(f(0),0=0..n-1)
          res := eval(res, go = (i -> eval(body, x=i)));
          return eval_factor(res, kb, mode, loops);
        end if;
        y, kb1 := genType(x, HInt(closed_bounds(bounds)), kb);
        return eval_factor(subs(x=y,body), kb1, mode, [[o,y=bounds],op(loops)]);
      end if;
      if e :: 'specfunc(piecewise)' then
        return eval_piecewise(e, kb, mode, loops);
      end if;
      if e :: `*` then
        # If we're here, then mode=`+` (else "e :: mode" above would be true)
        s, r := selectremove(depends, e, map2(op,[2,1],loops));
        # Transform sum(a*b(i),i=...) to a*sum(b(i),i=...)
        if r <> 1 then
          return eval_factor(s, kb, `+`, loops)
               * maptype(`*`, eval_factor, r, kb, `+`, []);
        end if;
      end if;
      if mode = `*` then
        if e :: '`^`' then
          # Transform product(a(i)^b,i=...) to product(a(i),i=...)^b
          i := map2(op,[2,1],loops);
          if not depends(op(2,e), i) then
            return eval_factor(op(1,e), kb, `*`, loops)
                 ^ eval_factor(op(2,e), kb, `+`, []);
          end if;
        end if;
        if e :: 'exp(anything)' or e :: '`^`' and not depends(op(1,e), i) then
          # Transform product(a^((b(i)+c(i))^2),i=...)
          #        to a^   sum(b(i)^2   ,i=...)
          #         * a^(2*sum(b(i)*c(i),i=...))
          #         * a^   sum(c(i)^2   ,i=...)
          return mul(subsop(-1=i,e),
                     i in convert(eval_factor(expand(op(-1,e)), kb, `+`,
                                              map2(subsop,1=sum,loops)),
                                  'list', `+`));
        end if;
        # Rewrite ... * idx([p,1-p],i)
        #      to ... * p^idx([1,0],i) * (1-p)^idx([0,1],i)
        # because the latter is easier to integrate and recognize with respect to p
        if e :: 'idx(list, anything)' and not depends(op(1,e), i) then
          return mul(op([1,j],e)
                     ^ eval_factor(idx([seq(`if`(k=j,1,0), k=1..nops(op(1,e)))],
                                       op(2,e)),
                                   kb, `+`, map2(subsop,1=sum,loops)),
                     j=1..nops(op(1,e)));
        end if;
      end if;
      if mode = `*` and e :: 'specfunc(Beta)' then
        res := hack_Beta(e, kb, loops);
        if res <> FAIL then return res end if;
      end if;
      if nops(loops) > 0 then
        # Emit outermost loop as last resort
        return op([-1,1],loops)(eval_factor(e, kb, mode, loops[1..-2]),
                                op([-1,2],loops));
      end if;
      # In the remainder of this function, assume loops=[] and recur in
      if e :: '{specfunc({GAMMA, Beta, exp, And, Or, Not}), relation, logical}' then
        return map(eval_factor, e, kb, `+`, []);
      end if;
      if e :: `^` then
        return eval_factor(op(1,e), kb, mode, [])
             ^ eval_factor(op(2,e), kb, `+` , []);
      end if;
      if e :: `+` then
        return map(eval_factor, e, kb, mode, []);
      end if;
      return e;
    end proc;

    ModuleApply := proc(e, kb::t_kb, $)
      simplify_assuming(eval_factor(convert(e, 'Beta'), kb, `*`, []), kb);
    end proc;
  end module; # simplify_factor_assuming
