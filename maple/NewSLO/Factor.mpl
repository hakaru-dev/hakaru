
  # Like simplify_assuming, but does a lot of hack-y things
  simplify_factor_assuming := module ()

    export ModuleApply;
    local graft_pw, GAMMAratio, wrap, hack_Beta,
          bounds_are_simple, eval_piecewise, eval_factor;

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

      # Try not to use hack_beta for now...

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
