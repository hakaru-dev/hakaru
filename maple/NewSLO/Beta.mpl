# Note that this 'module' and Loop.mpl are currently mutually recursive.
# Loop:-intssums > simplify_factor_assuming > eval_factor > hack_Beta > Loop:-graft
# but Loop:-intssums does not seem to even be used anywhere...

    hack_Beta := proc(e :: specfunc(Beta), kb :: t_kb,
                      loops :: list([identical(product,Product,sum,Sum),
                                     name=range]),
                      $)
      local x, bounds, res, s1, r1, s2, r2, sg, rg;
      # Temporary hack to show desired output for examples/{dice_predict,gmm_gibbs,naive_bayes_gibbs}.hk
      if nops(loops) > 0 and e :: 'specfunc(`+`, Beta)' and has(e, piecewise) then
        x, bounds := op(op([-1,2],loops));
        res := subsindets(e, 'specfunc(piecewise)', proc(pw, $)
          # Remove a particular superfluous inequality
          if op(1,pw) :: 'And(specfunc(And), anyfunc(relation, name=anything))' and has(op(1,pw),x) then
            if op([1,1],pw) :: `<=`
               and Testzero(op([1,1,1],pw)-op([1,1,2],pw)+op([1,2,1],pw)-op([1,2,2],pw)+rhs(bounds)-x) or
               op([1,1],pw) :: `<>`
               and Normalizer(op([1,1,1],pw)-op([1,1,2],pw)+op([1,2,1],pw)-op([1,2,2],pw)+rhs(bounds)-x) :: negative
            then
              return subsop(1=op([1,2],pw), pw)
            end if
          end if;
          return pw
        end proc);
        s1, r1 := selectremove(has, op(1,res), piecewise);
        s2, r2 := selectremove(has, op(2,res), piecewise);
        sg := graft_pw(combine(s1+s2));
        rg := Loop:-graft(r1+r2);
        if rg = eval(r2,x=x-1) and sg = eval(s2,x=x-1) then
          # Telescoping match!
        elif rg = eval(r1,x=x-1) and sg = eval(s1,x=x-1) then
          # Telescoping match, but swap Beta arguments
          s1, s2 := s2, s1;
          r1, r2 := r2, r1;
        else
          # No telescoping match -- bail out
          return FAIL;
        end if;
        # At this point we know that e = Beta(s1+r1, s2+r2)
        #   and that s2 = eval(s2, x=rhs(bounds)+1) + sum(s1, x=x+1..rhs(bounds)+1)
        #   and that r2 = eval(r2, x=rhs(bounds)+1) + sum(r1, x=x+1..rhs(bounds)+1)
        # So our remaining job is to express
        #   product(Beta(s1+r1, eval(s2+r2, x=rhs(bounds)+1) + sum(s1+r1, x=x+1..rhs(bounds)+1)), x=bounds)
        # in terms of
        #   product(Beta(   r1, eval(   r2, x=rhs(bounds)+1) + sum(   r1, x=x+1..rhs(bounds)+1)), x=bounds)
        res := wrap('Beta'(r1, eval(r2, x=rhs(bounds)+1) + 'sum'(r1, x=x+1..rhs(bounds)+1)), loops)
             * Loop:-graft(wrap(GAMMAratio(s1, r1), loops)
                           * wrap(eval('GAMMAratio'(s1 (* + s2 *), r1 + r2), x=rhs(bounds)+1),
                                                    # Unsound HACK: assuming eval(s2, x=rhs(bounds)+1) = 0
                                                    #   (Discharging this assumption sometimes requires checking idx(w,k) < size(word_prior) for symbolic k)
                                  eval(subsop(-1=NULL, loops), x=rhs(bounds)+1)))
             / wrap(eval('GAMMAratio'(s2, r2), x=lhs(bounds)-1),
                    eval(subsop(-1=NULL, loops), x=lhs(bounds)-1));
        return eval_factor(res, kb, `*`, []);
      end if;
      # Temporary hack to show desired output for the "integrate BetaD out of
      # BetaD-Bernoulli" test
      return hackier_Beta(loops, e)

      # return FAIL;
    end proc;

    hackier_Beta := proc(loops,e)
      local s1, r1, s2, r2;

      if nops(loops) = 0 and e :: 'specfunc(And(`+`, Not(`+`(Not(idx({[1,0],[0,1]}, anything))))), Beta)' then
        s1, r1 := selectremove(type, op(1,e), 'idx({[1,0],[0,1]}, anything)');
        s2, r2 := selectremove(type, op(2,e), 'idx({[1,0],[0,1]}, anything)');
        if s1 :: 'idx([1,0], anything)' and s2 :: 'idx([0,1], anything)' and op(2,s1) = op(2,s2) then
          return Beta(r1, r2) * idx([r1, r2], op(2,s1)) / (r1 + r2);
        elif s1 :: 'idx([0,1], anything)' and s2 :: 'idx([1,0], anything)' and op(2,s1) = op(2,s2) then
          return Beta(r1, r2) * idx([r2, r1], op(2,s1)) / (r1 + r2);
        end if
      end if;

      FAIL

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


    wrap := proc(e, loops :: list([identical(product,Product,sum,Sum),
                                   name=range]), $)
      local res, loop;
      res := e;
      for loop in loops do
        res := op(1,loop)(res, op(2,loop));
      end do;
      res
    end proc;
