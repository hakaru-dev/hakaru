# Teach Maple (through depends and eval) about our new binding forms.
# Integrand and LO bind from 1st arg to 2nd arg.

`depends/Integrand` := proc(v, e, x) depends(e, x minus {v}) end proc:
`depends/LO`        := proc(v, e, x) depends(e, x minus {v}) end proc:

`eval/Integrand` := proc(e, eqs)
  local v, ee;
  v, ee := op(e);
  eval(op(0,e), eqs)(BindingTools:-generic_evalat(v, ee, eqs))
end proc:

`eval/LO` := proc(e, eqs)
  local v, ee;
  v, ee := op(e);
  eval(op(0,e), eqs)(BindingTools:-generic_evalat(v, ee, eqs))
end proc:

#############################################################################

NewSLO := module ()
  option package;
  local
        t_sum, t_product,
        integrate_known,
        recognize_continuous, recognize_discrete, get_de, get_se,
        recognize_de, mysolve, Shiftop, Diffop, Recognized,
        factorize, termize, bind, weight,
        reduce_IntSum, reduce_IntsSums, get_indicators,
        elim_intsum, do_elim_intsum, int_assuming, sum_assuming,
        banish, banish_guard, banish_weight,
        reduce_pw, nub_piecewise, piecewise_if,
        get_var_pos, get_int_pos,
        mk_sym, mk_ary, mk_idx, innermostIntSum, ChangeVarInt,
        ModuleLoad;
  export
     # These first few are smart constructors (for themselves):
         integrate, applyintegrand,
     # while these are "proper functions"
         RoundTrip, Simplify, SimplifyKB, TestSimplify, TestHakaru, Efficient,
         toLO, fromLO, unintegrate, unweight, improve, reduce,
         density, bounds,

     # Like simplify_assuming, but also applies `hack_Beta` and `eval_factor`
     # which helps some things simplify.
     simplify_factor_assuming,

         ReparamDetermined, determined, reparam, disint;
  # these names are not assigned (and should not be).  But they are
  # used as global names, so document that here.
  global LO, Integrand, Indicator, SumIE, ProductIE;
  uses Hakaru, KB, Loop, Partition;

  t_sum     := 'specfunc({sum    ,Sum    })';
  t_product := 'specfunc({product,Product})';

$include "NewSLO/Interface.mpl"
$include "NewSLO/To.mpl"
$include "NewSLO/From.mpl"
$include "NewSLO/Banish.mpl"
$include "NewSLO/Improve.mpl"
$include "NewSLO/Disint.mpl"
$include "NewSLO/Reparam.mpl"
$include "NewSLO/Factor.mpl"

# An integrand h is either an Integrand (our own binding construct for a
# measurable function to be integrated) or something that can be applied
# (probably proc, which should be applied immediately, or a generated symbol).

  applyintegrand := proc(h, x, $)
    local var, body, dummy;
    if h :: 'Integrand(name, anything)' then
      var, body := op(h);
      if x :: {boolean, specfunc({And,Or,Not})} then
        body := eval(body, var=dummy);
        var  := dummy;
        body := subs((var=true)=var, body);
      end if;
      eval(body, var=x)
    elif h :: appliable then
      h(x)
    else
      'procname(_passed)'
    end if
  end proc;

  mysolve := proc(constraints)
    # This wrapper around "solve" works around the problem that Maple sometimes
    # thinks there is no solution to a set of constraints because it doesn't
    # recognize the solution to each constraint is the same.  For example--
    # This fails     : solve({c*2^(-1/2-alpha) = sqrt(2)/2, c*4^(-alpha) = 2^(-alpha)}, {c}) assuming alpha>0;
    # This also fails: solve(simplify({c*2^(-1/2-alpha) = sqrt(2)/2, c*4^(-alpha) = 2^(-alpha)}), {c}) assuming alpha>0;
    # But this works : map(solve, {c*2^(-1/2-alpha) = sqrt(2)/2, c*4^(-alpha) = 2^(-alpha)}, {c}) assuming alpha>0;
    # And the difference of the two solutions returned simplifies to zero.

    local result;
    if nops(constraints) = 0 then return NULL end if;
    result := solve(constraints, _rest);
    if result <> NULL or not (constraints :: {set,list}) then
      return result
    end if;
    result := mysolve(subsop(1=NULL,constraints), _rest);
    if result <> NULL
       and op(1,constraints) :: 'anything=anything'
       and simplify(eval(op([1,1],constraints) - op([1,2],constraints),
                         result)) <> 0 then
      return NULL
    end if;
    result
  end proc;

  ###
  # smart constructors for our language

  bind := proc(m, x, n, $)
    if n = 'Ret'(x) then
      m # monad law: right identity
    elif m :: 'Ret(anything)' then
      eval(n, x = op(1,m)) # monad law: left identity
    else
      'Bind(_passed)'
    end if;
  end proc;

  weight := proc(p, m, $)
    #Trying to make the below into an ASSERT statement results in a kernel
    #crash, even though the condition is caught, the message printed, and
    #the error generated.
    if kernelopts(assertlevel) > 0 then
         if not p::
              (complexcons &implies ((numeric &implies {0,1}) &under csgn))
         then
              userinfo(
                   1, SLO,
                   proc()
                   uses LL= ListTools:-LengthSplit;
                   local
                        S:= Matrix([LL(debugopts(callstack)[2..], 3)]),
                        rts:= interface(rtablesize= infinity)
                   ;
                        print(S);
                        interface(rtablesize= rts);
                        NULL
                   end proc()
              );
              error "Negative weight %1 not allowed", p
         end if
    end if;
    if p = 1 then
      m
    elif p = 0 then
      Msum()
    elif m :: 'Weight(anything, anything)' then
      weight(p * op(1,m), op(2,m))
    else
      'Weight(_passed)'
    end if;
  end proc;

  density[Lebesgue] := proc(lo,hi,$) proc(x,$) 1 end proc end proc;
  density[Uniform] := proc(a,b,$) proc(x,$)
    1/(b-a)
  end proc end proc;
  density[Gaussian] := proc(mu, sigma, $) proc(x,$)
    1/sigma/sqrt(2)/sqrt(Pi)*exp(-(x-mu)^2/2/sigma^2)
  end proc end proc;
  density[Cauchy] := proc(loc, scale, $) proc(x,$)
    1/Pi/scale/(1+((x-loc)/scale)^2)
  end proc end proc;
  density[StudentT] := proc(nu, loc, scale, $) proc(x,$)
    GAMMA((nu+1)/2) / GAMMA(nu/2) / sqrt(Pi*nu) / scale
    * (1 + ((x-loc)/scale)^2/nu)^(-(nu+1)/2)
  end proc end proc;
  density[BetaD] := proc(a, b, $) proc(x,$)
    x^(a-1)*(1-x)^(b-1)/Beta(a,b)
  end proc end proc;
  # Hakaru uses the alternate definition of gamma, so the args are backwards
  density[GammaD] := proc(shape, scale, $) proc(x,$)
    x^(shape-1)/scale^shape*exp(-x/scale)/GAMMA(shape);
  end proc end proc;
  density[InverseGammaD]:= proc(shape, scale, $)
       proc(x,$) scale^shape/GAMMA(shape)/x^(shape+1)/exp(scale/x) end proc
  end proc;
  density[Counting] := proc(lo, hi, $) proc(k,$)
    1
  end proc end proc;
  density[Categorical] := proc(a, $) proc(k,$)
    idx(a,k)
  end proc end proc;
  density[Binomial]:= proc(n,p,$)
       proc(k,$) p^k*(1-p)^(n-k)*GAMMA(n+1)/GAMMA(k+1)/GAMMA(n-k+1) end proc
  end proc;
  density[NegativeBinomial] := proc(r, p, $) proc(k,$)
    p^k * (1-p)^r * GAMMA(r+k) / GAMMA(k+1) / GAMMA(r)
  end proc end proc;
  density[PoissonD] := proc(lambda, $) proc(k,$)
    lambda^k/exp(lambda)/k!
  end proc end proc;
  density[ChiSquared] := proc(k, $) proc(x,$)
    x^((1/2)*k-1)*exp(-(1/2)*x)/(2^((1/2)*k)*GAMMA((1/2)*k))
  end proc end proc:

  bounds[Lebesgue] := `..`;
  bounds[Uniform] := proc(a, b, $) a .. b end proc;
  bounds[Gaussian] := proc(mu, sigma, $) -infinity .. infinity end proc;
  bounds[Cauchy] := proc(loc, scale, $) -infinity .. infinity end proc;
  bounds[StudentT] := proc(nu, loc, scale, $) -infinity .. infinity end proc;
  bounds[BetaD] := proc(a, b, $) 0 .. 1 end proc;
  bounds[GammaD] := proc(shape, scale, $) 0 .. infinity end proc;
  bounds[InverseGammaD]:= proc(shape, scale, $) 0..infinity end proc;
  bounds[Counting] := proc(lo, hi, $) lo..hi-1 end proc;
  bounds[Categorical] := proc(a, $) 0 .. size(a)-1 end proc;
  bounds[Binomial]:= proc(n,p,$) 0..n end proc;
  bounds[NegativeBinomial] := proc(r, p, $) 0 .. infinity end proc;
  bounds[PoissonD] := proc(lambda, $) 0 .. infinity end proc;
  bounds[ChiSquared] := proc(k, $) 0 .. infinity end proc;

  mk_sym := proc(var :: name, h, $)
    local x;
    x := var;
    if h :: 'Integrand(name, anything)' then
      x := op(1,h);
    elif h :: 'procedure' then
      x := op(1, [op(1,h), x]);
    end if;
    gensym(x)
  end proc;

  mk_ary := proc(e, loops :: list(name = range), $)
    foldl((res, i) -> ary(op([2,2],i) - op([2,1],i) + 1,
                          op(1,i),
                          eval(res, op(1,i) = op(1,i) + op([2,1],i))),
          e, op(loops));
  end proc;

  mk_idx := proc(e, loops :: list(name = range), $)
    foldr((i, res) -> idx(res, op(1,i) - op([2,1],i)),
          e, op(loops));
  end proc;

  ModuleLoad := proc($)
    local prev;
    Hakaru; # Make sure the Hakaru module is loaded for the types t_type and t_Hakaru.
    KB;     # Make sure the KB module is loaded, for the type t_kb
    prev := kernelopts(opaquemodules=false);
    try
      PiecewiseTools:-InertFunctions := PiecewiseTools:-InertFunctions
        union '{# Do not lift piecewise over a binder
                Integrand,LO,lam,Branch,Bind,ary,Plate,
                forall,Ints,Sums,ints,sums,`..`}';
    catch:
         userinfo(
              1, NewSLO,
              "Redefinition of PiecewiseTools:-InertFunctions failed.",
              StringTools:-FormatMessage(lastexception[2..-1])
         )
    finally
      kernelopts(opaquemodules=prev);
    end try
  end proc; #ModuleLoad

  ModuleLoad();

end module; # NewSLO
