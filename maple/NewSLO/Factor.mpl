
  # Like simplify_assuming, but does a lot of hack-y things
  simplify_factor_assuming := module ()

    export ModuleApply;
    local graft_pw, GAMMAratio, wrap,
          hack_Beta_pw, hack_Beta, hackier_Beta,
          eval_piecewise, bounds_are_simple, eval_loop, eval_factor;

$include "NewSLO/Beta.mpl"
$include "NewSLO/Piecewise.mpl"

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

    eval_loop := proc(e :: And(specfunc({product,Product,sum,Sum}),
                               anyfunc(anything, name=range)),
                      kb :: t_kb,
                      mode :: identical(`*`,`+`),
                      loops, $)
      local o, body, x, bounds, res, go, y, kb1,
            extra, cond, b, a, bodyNe, bodyEq, bodyDiff;
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
      extra := mode();
      for cond in select(depends, indets(body, '{`=`,`<>`}'), x) do
        try
          if not ispoly(`-`(op(cond)), 'linear', x, 'b', 'a') then next end if;
          b := Normalizer(-b/a);
          bodyNe := eval(body, {subsop(0=`=` , cond) = false,
                                subsop(0=`<>`, cond) = true});
          if length(body) <= length(bodyNe) then next end if;
          if mode = `*` and
             not kb_entails(kb, 0 <> eval(bodyNe, x=b)) then next end if;
          bodyEq := eval(body, {subsop(0=`=` , cond) = true,
                                subsop(0=`<>`, cond) = false});
          bodyDiff :=
            piecewise(And(b :: integer, lhs(bounds) <= b, b <= rhs(bounds)),
                      eval(`if`(mode=`*`,`/`,`-`)(bodyEq, bodyNe), x=b),
                      mode());
          if has(bodyDiff, '{undefined, infinity, FAIL}') then next end if;
          bodyDiff := eval_factor(bodyDiff, kb, mode, loops);
          userinfo(3, procname, "Kronecker expansion succeeded on pivot %1: %2",
                   cond, bodyDiff);
          extra := mode(extra, bodyDiff);
          body  := bodyNe;
        catch:
          userinfo(3, procname, "Kronecker expansion failed on pivot %1: %2",
                   cond, lastexception);
        end try;
      end do;
      y, kb1 := genType(x, HInt(closed_bounds(bounds)), kb);
      mode(extra,
           eval_factor(subs(x=y,body), kb1, mode, [[o,y=bounds],op(loops)]));
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
      local res, i, j, k, s, r;
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
        return eval_loop(e, kb, mode, loops);
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
        i := map2(op,[2,1],loops);
        if e :: '`^`' then
          # Transform product(a(i)^b,i=...) to product(a(i),i=...)^b
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
          return mul(subsop(-1=j,'e'),
                     j in convert(eval_factor(expand(op(-1,e)), kb, `+`,
                                              map2(subsop,1=sum,loops)),
                                  'list', `+`));
        end if;
        if e :: 'idx(list, anything)' and not depends(op(1,e), i) then
          if has(op(1,e), piecewise) then
            # Simplify the `idx' without chilling (by moving it into the
            # function argument to kb_assuming_mb) and recurse. This shouldn't
            # really be needed, but sometimes on expressions of the form
            # produced by the subsequent case are simplified incorrectly by the
            # later call to `simplify_assuming' in `simplify_factor_assuming'.
            res := kb_assuming_mb(
              simplify@(x->idx(x,op(2,e))), op(1,e), kb, _->e);
            if res<>e then
              return eval_factor(res, kb, `*`, loops);
            end if;
          end if;

          # Rewrite ... * idx([p,1-p],i)
          #      to ... * p^idx([1,0],i) * (1-p)^idx([0,1],i)
          # because the latter is easier to integrate and recognize with respect to p
          return mul(op([1,j],e)
                   ^ eval_factor(idx([seq(`if`(k=j,1,0), k=1..nops(op(1,e)))],
                                      op(2,e)),
                                  kb, `+`, map2(subsop,1=sum,loops)),
                   j=1..nops(op(1,e)));
        end if;
      end if;

      # Try not to use hack_beta for now...

      if mode = `*` and e :: 'specfunc(Beta)' then
        res := hack_Beta(e, kb, loops);
        if res <> FAIL then
          userinfo(3, 'hack_Beta',
                   printf("Beta hack was applied to %a, %a, %a\n"
                          "\tto produce %a\n", e, kb, loops, res));
          return res
        end if;
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
      simplify_assuming(eval_factor(convert(Partition:-PartitionToPW_mb(e), 'Beta'), kb, `*`, []), kb);
    end proc;
  end module; # simplify_factor_assuming
