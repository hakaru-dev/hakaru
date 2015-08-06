NewSLO := module ()
  option package;
  local t_pw, gensym, density, get_de, recognize_density, Diffop, WeightedM;
  export Integrand, applyintegrand,
         LO, Ret, Bind, Msum, Weight, Lebesgue, Gaussian,
         HakaruToLO, integrate, LOToHakaru, unintegrate;

# FIXME Need eval/LO and eval/Integrand and eval/Bind to teach eval about our
# binders.  Both LO and Integrand bind from 1st arg to 2nd arg, whereas Bind
# binds from 2nd arg to 3rd arg.

  t_pw := 'specfunc(piecewise)';

# An integrand h is either an Integrand (our own binding construct for a
# measurable function to be integrated) or something that can be applied
# (probably proc, which should be applied immediately, or a generated symbol).

# TODO evalapply/Integrand instead of applyintegrand?
# TODO evalapply/{Ret,Bind,...} instead of integrate?!

  applyintegrand := proc(h, x)
    if h :: 'Integrand(name, anything)' then
      eval(op(2,h), op(1,h) = x)
    elif h :: procedure then
      h(x)
    else
      'applyintegrand'(h, x)
    end if
  end proc;

# Step 1 of 3: from Hakaru to Maple LO (linear operator)

  HakaruToLO := proc(m)
    local h;
    h := gensym('hh');
    LO(h, integrate(m, h))
  end proc;

  integrate := proc(m, h)
    local x, n, i;
    if m :: 'Ret(anything)' then
      applyintegrand(h, op(1,m))
    elif m :: 'Bind(anything, name, anything)' then
      integrate(op(1,m), z -> integrate(eval(op(3,m), op(2,m) = z), h))
    elif m :: 'Msum(list)' then
      `+`(op(map(integrate, op(1,m), h)))
    elif m :: 'Weight(anything, anything)' then
      op(1,m) * integrate(op(2,m), h)
    elif m :: 'Lebesgue()' then
      x := gensym('xl');
      Int(applyintegrand(h, x),
          x=-infinity..infinity)
    elif m :: 'Gaussian(anything, anything)' then
      x := gensym('xg');
      Int(density[NormalD](op(1,m),op(2,m))(x) * applyintegrand(h, x),
          x=-infinity..infinity)
    elif m :: 'LO(name, anything)' then
      eval(op(2,m), op(1,m) = h)
    elif m :: t_pw then
      n := nops(m);
      piecewise(seq(`if`(i::even or i=n, integrate(op(i,m), h), op(i,m)),
                    i=1..n))
    elif h :: procedure then
      x := gensym('xa');
      'integrate'(m, Integrand(x, h(x)))
    else
      'integrate'(m, h)
    end if
  end proc;

# Step 2 of 3: algebra (currently nothing)

# Step 3 of 3: from Maple LO (linear operator) back to Hakaru

  Bind := proc(m, x, n)
    if n = 'Ret'(x) then
      m # monad law: right identity
    elif m :: 'Ret(anything)' then
      eval(n, x = op(1,m)) # monad law: left identity
    else
      'Bind'(m, x, n)
    end if;
  end proc;

  Weight := proc(p, m)
    if p = 1 or m = Msum([]) then
      m
    elif m :: 'Weight(anything, anything)' then
      'Weight'(p * op(1,m), op(2,m))
    else
      'Weight'(p, m)
    end if;
  end proc;

  LOToHakaru := proc(lo :: LO(name, anything))
    local h;
    h := gensym('hl');
    unintegrate(h, eval(op(2,lo), op(1,lo) = h), [])
  end proc;

  unintegrate := proc(h :: name, integral, context :: list)
    local x, m,
          recognition, de, Dx, f, diffop, init,
          subintegral, weight,
          n, i, else_context, update_context;
    if integral = 0 then
      Msum([])
    elif integral :: `+` then
      Msum(map2(unintegrate, h, convert(integral, 'list'), context))
    elif integral :: 'applyintegrand(anything, anything)'
         and op(1,integral) = h then
      Ret(op(2,integral))
    elif integral :: 'integrate(anything, anything)' then
      x := gensym('xu');
      # TODO is there any way to enrich context in this case?
      Bind(op(1,integral), x,
           unintegrate(h, applyintegrand(op(2,integral), x), context))
    elif integral :: 'Or(Int(anything, name=-infinity..infinity),
                         int(anything, name=-infinity..infinity))' then
      x := gensym('xu');
      # TODO: enrich context with x (measure class lebesgue)
      m := unintegrate(h, eval(op(1,integral), op([2,1],integral) = x),
                       [op(context), x::real]);
      recognition := NULL;
      if m :: 'Weight(anything, anything)' then
        de := get_de(op(1,m), x, Dx, f);
        if de :: 'Diffop(anything, anything)' then
          (diffop, init) := op(de);
          recognition := recognize_density(diffop, init, Dx, x)
            assuming op(context), x::real
        end if
      end if;
      if recognition :: 'WeightedM(anything, NormalD(anything, anything))' then
        Weight(op(1,recognition),
               Bind(Gaussian(op(op(2,recognition))), x, op(2,m)))
      else
        Bind(Lebesgue(), x, m)
      end if
    elif integral :: `*` then
      (subintegral, weight) := selectremove(has, integral, h);
      if subintegral :: `*` then
        error "Nonlinear integral %1", integral
      end if;
      Weight(weight, unintegrate(h, subintegral, context))
    elif integral :: t_pw then
      n := nops(integral);
      else_context := context;
      update_context := proc(c)
        local then_context;
        then_context := [op(else_context), c];
        else_context := [op(else_context), not c]; # Mutation!
        then_context
      end proc;
      piecewise(seq(piecewise(i::even,
                              unintegrate(h, op(i,integral),
                                          update_context(op(i-1,integral))),
                              i=n,
                              unintegrate(h, op(i,integral), context),
                              op(i,integral)),
                    i=1..n))
    else
      # Failure: return residual LO
      LO(h, integral)
    end if
  end proc;

  get_de := proc(dens, var, Dx, f)
    local de, init, diffop;
    try
      de := gfun[holexprtodiffeq](dens, f(var));
      if not (de = NULL) and not (de :: set) then
        de := gfun[diffeqtohomdiffeq](de, f(var));
      end if;
      if de::set then
        init, de := selectremove(type, de, `=`);
        if nops(de)=1 then
          de := de[1];
          diffop := DEtools[de2diffop](de, f(var), [Dx, var]);
          return Diffop(diffop, init)
        end if;
      elif not (de = NULL) then # no initial condition returned
        diffop := DEtools[de2diffop](de, f(var), [Dx, var]);
        return Diffop(diffop, {}); # should be {f(0)=0} ?
      end if;
    catch: # do nothing
    end try;
    Nothing
  end proc;

  # density recognizer for reals
  recognize_density := proc(diffop, init, Dx, var)
    local a0, a1, scale, at0, mu, sigma, ii;
    if degree(diffop, Dx) = 1 then
      a0 := coeff(diffop, Dx, 0);
      a1 := coeff(diffop, Dx, 1);
      if degree(a0, var) = 1 and degree(a1, var) = 0 and nops(init) = 1 then
        ii := rhs(init[1]);
        scale := coeff(a0, var, 1);
        mu := -coeff(a0, var, 0)/scale;
        sigma := sqrt(coeff(a1, var, 0)/scale);
        at0 := simplify(eval(ii/density[NormalD](mu, sigma)(0)));
        return WeightedM(at0, NormalD(mu,sigma));
      end if;
    end if;
    NULL;
  end proc;

  density[NormalD] := proc(mu, sigma) proc(x)
    1/sigma/sqrt(2)/sqrt(Pi)*exp(-(x-mu)^2/2/sigma^2)
  end proc end proc;
  density[BetaD] := proc(a, b) proc(x)
    x^(a-1)*(1-x)^(b-1)/Beta(a,b)
  end proc end proc;
  # Hakaru uses the alternate definition of gamma, so the args are backwards
  density[GammaD] := proc(theta,k) proc(x)
    x^(theta-1)/k^(theta-1)*exp(-x/k)/k/GAMMA(theta);
  end proc end proc;

  gensym := module()
    export ModuleApply;
    local gs_counter;
    gs_counter := 0;
    ModuleApply := proc(x::name)
      gs_counter := gs_counter + 1;
      x || gs_counter;
    end proc;
  end module; # gensym

end module; # NewSLO
