
  banish := proc(g, h :: name, kb :: t_kb, levels :: extended_numeric,
                 x :: name, make, $)
    # banish(g, h, kb, levels, x, make), where the integrand h and the
    # integration variable x take scope over the integral g patently linear
    # in h, should be equivalent to make(kb, g), where the integration operator
    # make binds x in g, except
    #   - integration over x is performed innermost rather than outermost;
    #   - if levels < infinity then levels controls how deeply to banish g;
    #   - make is invoked with the KB in the first argument extended.
    local subintegral, w, y, kb1, lo, hi, m, loops, xx, less;
    if g = 0 then
      0
    elif levels <= 0 then
      make(kb, g)
    elif not depends(g, x) then
      make(kb, 1) * g
    elif g :: `+` then
      map(banish, _passed)
    elif g :: `*` then
      (subintegral, w) := selectremove(depends, g, h);
      if subintegral :: `*` then error "Nonlinear integral %1", g end if;
      banish(subintegral, h, kb, levels, x, banish_weight(make, w));
    elif g :: 'And'('specfunc({Int,int,Sum,sum})',
                    'anyfunc'('anything','name'='range'('freeof'(h)))) then
      lo, hi      := op(op([2,2],g));
      m           := make;
      if depends(lo, x) then
        m  := banish_guard(eval(m), lo<y);
        lo := -infinity;
      end if;
      if depends(hi, x) then
        m  := banish_guard(eval(m), y<hi);
        hi := infinity;
      end if;
      y, kb1 := `if`(op(0,g) in '{Int,int}',
        genLebesgue(op([2,1],g), lo, hi, kb, make),
        genType(op([2,1],g), HInt(closed_bounds(lo..hi)), kb, make));
      subintegral := subs(op([2,1],g)=y, op(1,g));
      op(0,g)(banish(subintegral, h, kb1, levels-1, x, m), y=lo..hi)
    elif g :: 'And'('specfunc({Ints,ints,Sums,sums})',
                    'anyfunc'('anything', 'name', 'range'('freeof'(h)),
                              'list(name=range)')) then
      lo, hi      := op(op(3,g));
      loops       := op(4,g);
      xx          := map(lhs, loops);
      m           := make;
      less        := `if`(op(0,g) in '{Ints,ints}', `<`, `<=`);
      if depends(lo, x) then
        m  := banish_guard(m, forall(xx, less(lo, mk_idx(y,loops))));
        lo := -infinity;
      end if;
      if depends(hi, x) then
        m  := banish_guard(m, forall(xx, less(mk_idx(y,loops), hi)));
        hi := infinity;
      end if;
      y, kb1 := genType(op(2,g),
                        mk_HArray(`if`(op(0,g) in '{Ints,ints}',
                                       HReal(open_bounds(lo..hi)),
                                       HInt(closed_bounds(lo..hi))),
                                  op(4,g)),
                        kb);
      if nops(op(4,g)) > 0 then
        kb1 := assert(size(y)=op([4,-1,2,2],g)-op([4,-1,2,1],g)+1, kb1);
      end if;
      subintegral := subs(op(2,g)=y, op(1,g));
      op(0,g)(banish(subintegral, h, kb1, levels-1, x, m), y, lo..hi, op(4,g));
    elif g :: t_pw then
      foldr_piecewise(
        proc(cond, th, el, $) proc(make, kb, $)
          if depends(cond, x) then
            banish(th, h, kb, levels-1, x, banish_guard(make, cond))
              + el(banish_guard(make, Not(cond)), kb)
          else
            piecewise_if(cond,
              banish(th, h, assert(cond, kb), levels-1, x, make),
              el(make, assert(Not(cond), kb)))
          end if
        end proc end proc,
        proc(make, kb, $) 0 end proc,
        g)(make, kb)
    elif g :: t_case then
      map_piecewiselike(banish, _passed)
    elif g :: 'integrate(freeof(x), Integrand(name, anything), list)' then
      y           := gensym(op([2,1],g));
      subintegral := subs(op([2,1],g)=y, op([2,2],g));
      subsop(2=Integrand(y, banish(subintegral, h, kb, levels-1, x, make)), g)
    else
      make(kb, g)
    end if
  end proc;

  banish_guard := proc(make, cond, $)
    if cond :: 'And(specfunc(Not), anyfunc(anything))' then
      # Work around simplify/piecewise bug:
      #   > simplify(piecewise(Not(i=0), 1, 0))
      #   a
      # (due to PiecewiseTools:-ImportImplementation:-UseSolve calling
      # solve(Not(i=0), {i}, 'AllSolutions', 'SolveOverReals'))
      proc(kb,g,$) make(kb, piecewise(op(1,cond),0,g)) end proc
    else
      proc(kb,g,$) make(kb, piecewise(cond,g,0)) end proc
    end if
  end proc;

  banish_weight := proc(make, w, $)
    proc(kb,g,$) make(kb, w*g) end proc
  end proc;
