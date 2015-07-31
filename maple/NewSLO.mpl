NewSLO := module ()
  option package;
  local t_pw, t_LO, gensym, density, get_de, recognize_density, WeightM, WeightedM;
  export ret, bind, mzero, mplus, weight, lebesgue, gaussian, LO, applyLO, intLO, Ret, Bind, Mzero, Mplus, Weight, Lebesgue, Gaussian, unexpect;

  t_pw := 'specfunc(anything, piecewise)';
  t_LO := 'LO(name, anything)';

# Step 1 of 3: expect (shallow embedding from Hakaru to Maple LO (linear operator))

  ret := proc(x)
    local h;
    h := gensym('hr');
    LO(h, h(x))
  end proc;

  bind := proc(m,x,n)
    local h;
    h := gensym('hb');
    LO(h, applyLO(m, z -> applyLO(eval(n,x=z), h)))
  end proc;

  mzero := proc()
    local h;
    h := gensym('hmz');
    LO(h, 0)
  end proc;

  mplus := proc(m1,m2)
    local h;
    h := gensym('hmp');
    LO(h, applyLO(m1,h) + applyLO(m2,h))
  end proc;

  weight := proc(p,m)
    local h;
    h := gensym('hw');
    LO(h, p * applyLO(m,h))
  end proc;

  lebesgue := proc()
    local h, x;
    h := gensym('hl');
    x := gensym('xl');
    LO(h, Int(h(x), x=-infinity..infinity))
  end proc;

  gaussian := proc(mean, stdev)
    local h, x;
    h := gensym('hg');
    x := gensym('xg');
    LO(h, Int(density[NormalD](mean,stdev)(x) * h(x), x=-infinity..infinity))
  end proc;

  applyLO := proc(lo, hproc)
    local x;
    if lo::t_LO then
      eval(op(2,lo), op(1,lo) = hproc)
    elif lo::t_pw then
      # FIXME ... applyLO(loPrime, hproc) ...
    else
      x := gensym('xa');
      'intLO'(lo, x, hproc(x))
    end if;
  end proc;

  intLO := proc(lo, x, body)
    applyLO(lo, unapply(body, x))
  end proc;

  # FIXME Need eval/LO and eval/intLO to teach eval about our binders:
  # - 'LO' binds from 1st arg to 2nd arg
  # - 'intLO' binds from 2nd arg to 3rd arg

# Step 2 of 3: algebra (currently nothing)

# Step 3 of 3: unexpect

  Weight := proc(p, m)
    if p = 1 or m = Mzero then
      m
    elif m :: 'Weight(anything, anything)' then
      'Weight'(p * op(1,m), op(2,m))
    else
      'Weight'(p, m)
    end if;
  end proc;

  unexpect := proc(lo, context)
    local body, h, x, subbody, weight, result, de, res, Dx, f, diffop, init;

    if lo :: t_LO then
      h := op(1,lo);
      body := op(2,lo);
      if body=0 then
        Mzero
      elif body::`+` then
        foldr(Mplus, Mzero,
              op(map((subbody -> unexpect(LO(h, subbody), context)),
                  convert(body,'list'))))
      elif body::function and op(0,body)=h then
        Ret(op(1,body))
      elif body::'intLO(anything, name, anything)' then
        x := gensym('xu');
        # TODO is there any way to enrich context in this case?
        subbody := op(3,body);
        if subbody::function and op(0,subbody)=h and op(1,subbody)=op(2,body) then
          op(1,body) # optimize using right-identity monad-law
        else
          Bind(op(1,body), x,
               unexpect(LO(h, eval(subbody, op(2,body)=x)),
                        context))
        end if;
      elif body::'Int(anything, name=-infinity..infinity)' then
        x := gensym('xu');
        # TODO: enrich context with x (measure class lebesgue)
        result := unexpect(LO(h, eval(op(1,body), op([2,1],body)=x)),
                           [op(context), x::real]);
        res := NULL;
        if result :: Weight(anything, anything) then
          de := get_de(op(1,result),x,Dx,f);
          if de::specfunc(anything, 'Diffop') then
            (diffop, init) := op(de);
            res := recognize_density(diffop, init, Dx, x) assuming op(context), x::real;
          end if;
        end if;
        if res :: WeightedM(anything, NormalD(anything, anything)) then
          Weight(op(1,res), Bind(Gaussian(op(op(2,res))), x, op(2,result)))
        else
          Bind(Lebesgue(), x, result)
        end if;
      elif body::`*` then
        (subbody, weight) := selectremove(has, body, h);
        if subbody::`*` then
          error "Nonlinear body %1", body;
        end if;
        Weight(weight, unexpect(LO(h, subbody), context))
      else
        error "unexpect failure on LO: %1", args;
      end if;
    elif lo :: t_pw then
      # FIXME
      error "pw case in unexpect not implemented yet";
    else
      error "unexpect failure: %1", args;
    end if;
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
