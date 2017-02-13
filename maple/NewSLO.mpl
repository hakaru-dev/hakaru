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
         ReparamDetermined, determined, reparam, disint;
  # these names are not assigned (and should not be).  But they are
  # used as global names, so document that here.
  global LO, Integrand, Indicator, SumIE, ProductIE;
  uses Hakaru, KB, Loop;

  t_sum     := 'specfunc({sum    ,Sum    })';
  t_product := 'specfunc({product,Product})';

$include "NewSLO\Interface.mpl"
$include "NewSLO\To.mpl"
$include "NewSLO\From.mpl"

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

(*------------------- cut code -------------------------------
  #This code should not currently be used, it is just a snapshot in time.
  #New version defined below.
  Reparam := proc(e::Int(anything,name=range), h::name)
    local body, var, inds, xx, inv, new_e;

    # TODO improve the checks.
    if not has(body, {Int,int}) and hastype(e,'specfunc(applyintegrand)') then
      inds := indets(body, 'applyintegrand'('identical'(h), 'dependent'(var)));
      if nops(inds)=1 and op(2,inds[1]) :: algebraic and
         not hastype(body, t_pw) then
        xx := gensym('xx');
        inv := solve({op(2,inds[1])=xx}, {var});
        try
          new_e := IntegrationTools[Change](e, inv, xx);
          if not has(new_e,{'limit'}) then e := new_e end if;
        catch:
          # this will simply not change e
        end try;
      end if;
    end if;

    e;
  end proc;
-------------- end cut code ---------------------------------- *)

  ReparamDetermined := proc(lo :: LO(name, anything))
    local h;
    h := op(1,lo);
    LO(h,
       evalindets(op(2,lo),
                  'And'('specfunc({Int,int})',
                        'anyfunc'(anything, 'name=anything')),
                  g -> `if`(determined(op(1,g),h), Reparam(g,h), g)))
  end proc;

  determined := proc(e, h :: name)
    local i;
    for i in indets(e, 'specfunc({Int,int})') do
      if hastype(IntegrationTools:-GetIntegrand(i),
           'applyintegrand'('identical'(h),
             'dependent'(IntegrationTools:-GetVariable(i)))) then
        return false
      end if
    end do;
    return true
  end proc;

  #Beginning of Carl's code devoted to disintegration and the reparametrization (aka change
  #of variables) of integrals and sums.

  #Finds the innermost Ints or Sums in an expression, that is, those which
  #don't contain further Ints or Sums
  innermostIntSum:= proc(e::anything, $)::set(specfunc({Int,Sum}));
       select(IS-> nops(indets(IS, specfunc({Int,Sum}))) = 1, indets(e, specfunc({Int,Sum})))
  end proc;

  #my substitute for IntegrationTools:-Change
  ChangeVarInt:= proc(J::specfunc(Int), target::algebraic, $)
  local
       newJ, #What J will become.
       x::name:= op([2,1], J),
       u::name:= gensym('u'),  #new variable of integration
       s,                      #What x will become
       F                       #Boolean: flip integral?
  ;
       s:= {solve({u = target}, {x})};
       if nops(s) = 0 then
            userinfo(1, reparam, "Can't solve substitution target.");
            return e
       end if;
       if nops(s) > 1 then
            userinfo(1, reparam, "Case of multi-branched substitution not handled.");
            return e
       end if;
       s:= s[];

       newJ:= Int(
            eval(implicitdiff(u = target, x, u)*op(1,J), s),
            u=
                 limit(target, x= op([2,2,1], J), right).. #lower limit
                 limit(target, x= op([2,2,2], J), left),   #upper limit
            op(3.., J) #optional Int args (unlikely to be used)
       );

       #If lower limit > upper limit, then flip limits of integration.
       F:= is(op([2,2,1], newJ) > op([2,2,2], newJ));
       if F::truefalse then
            if F then
                 userinfo(2, reparam, "Switching limits:", op([2,2], newJ));
                 newJ:= IntegrationTools:-Flip(newJ)
            end if
       else #If inequality can't be decided, then don't reverse.
            userinfo(1, reparam, "Can't order new limits:", op([2,2], newJ))
       end if;

       newJ
  end proc;

  #main procedure for int/sum reparamterizations
  reparam:= proc(e::LO(symbol, algebraic), {ctx::list:= []}, $)
  local
       J:= innermostIntSum(e),   #the integral or sum
       newJ, #What J will become
       #possible subs target(s)
       oldarg::{algebraic, set(algebraic)}:= map2(op, 2, indets(e, specfunc(applyintegrand)))
  ;
       if nops(J) = 0 then
            userinfo(2, procname, "No sum or integral found.");
            return e
       end if;
       if nops(J) > 1 then
            userinfo(1, reparam, "Case of multiple innermost Int or Sums not yet handled.");
            return 'procname'(e)
       end if;
       J:= J[];
       if J::specfunc(Sum) then
            userinfo(1, reparam, "Sums not yet handled.");
            return 'procname'(e)
       end if;

       if nops(oldarg) <> 1 then
            userinfo(1, thisproc, "More than 1 reparam possible:", oldarg);
            return 'procname'(e)
       end if;
       oldarg:= oldarg[];   #Extract the reparam target.

       #If the target is simply a name, return input unchanged.
       if oldarg::symbol then
            userinfo(2, procname, "No need for a reparameterization.");
            return e
       end if;

       (*#************ This isn't currently used. **********************************
       #Check the invertibility of the change of vars.

       #The ability of `solve` to select a branch is very limited. For example,
               solve({y=x^2, x > 0}, {x})
       #returns
               sqrt(y), -sqrt(y).
       #This needs to be dealt with. First idea: Use `is` to filter
       #solutions. This is implemented below.

       #The next command is redundantly performed in the local inits. I put it here also
       #because I anticipate some future situations where that's no longer valid.

       #Save current vars for comparison with vars after `solve`.
       Ns:= indets(oldarg, symbol);
       #The usage of `explicit` in the next line is undocumented.
       S:= {solve({'y'=oldarg, a <= x, x <= b}, {x}, allsolutions, explicit)};
       S:= map(s->`if`(s::specfunc(piecewise), s[], s), S);
       #Use `is` to filter solutions under the assumptions.
       assume(a <= x, x <= b);
       S:= select(s-> ver(rhs,lhs)(eval(s, y= oldarg)[]), S);
       if  nops(S) <> 1  or  indets(S, symbol) <> Ns union {y}  or  hastype(S, RootOf)  then
            WARNING("Reparam target is not invertible (upto `solve` and `is`).");
            userinfo(1, procname, "Target:", subs(x= ':-x', oldarg), "S:", subs(x= ':-x', S), "domain:", ':-x'= a..b);
            return 'procname'(e)
       end if;
       *******************************************************************************)

       #Make the change of vars.
       newJ:= simplify_assuming('ChangeVarInt(J, oldarg)', foldr(assert, empty, ctx[]));

       if newJ = 0 then
            WARNING("Integral is 0, likely due to improper handling of an infinity issue.");
            userinfo(
                 1, procname, "u subs:",
                 print(
                      #Reformat the ChangeVarInt command for readability.
                      subs(
                           x= ':-x',
                           'ChangeVarInt'(
                                subsindets(
                                     J,
                                     specfunc(applyintegrand),
                                     f-> ':-h'(op(2,f))
                                )
                           ),
                           oldarg
                      )
                 )
            )
       end if;

       subs(J= newJ, e)
  end proc;

  #Disintegration *
  #---------------*
  #Abbreviations:
  #     wrt = "with respect to".
  #     wrt var = "a variable wrt which disintegration is performed". There may be
  #          more than one of these, in which case they are passed (in the 2nd arg)
  #          as Pairs, possibly nested.
  #     wrt-var type: Each wrt var may be continuous (Lebesgue), discrete (Counting),
  #          point evaluation (Dirac), and there may be other types added later.
  disint:= module()
  local
       #Dispatch table for wrt-var types. For each, there is a "cond constructor",
       #a "disintegrator", and a "disintegrator_arg_extractor". The cond constructor
       #builds the associated relation in the master piecewise; the disintegrator
       #does the differentiation or whatever operator is analogous to differentiation
       #for that type after the measure has been `improve`d; and the
       #disintegrator_arg_extractor builds the 2nd arg to the disintegrator from
       #the t_disint_var passed in the 2nd arg of disint.
       #
       #APIs:
       #     Indices:
       #          Must be the op(0, ...) of the expression passed with the
       #          wrt var.
       #     cond_constructor: (algebraic,name)-> boolean (most likely, a relation)
       #     disintegrator: (algebraic, {name, name=anything})-> algebraic
       #     disintegrator_arg_extractor:
       #          (`&M`(name, t_wrt_var_type))-> {name, name= anything}
       Wrt_var_types::static:= table([
            Lebesgue= Record(
                 cond_constructor= `<=`,
                 disintegrator= diff,
                 disintegrator_arg_extractor= (A-> op(1,A))
            ),
            Counting= Record(
                 cond_constructor= `<=`,
                 disintegrator= LREtools[delta],
                 disintegrator_arg_extractor= (A-> op(1,A))
            ),
            #Ret is aka Dirac.
            Ret= Record(
                 cond_constructor= `=`,
                 #If it wasn't necessary to clean out the superfluous `Indicator`s,
                 #then this disintegrator could simply be `eval`, which would
                 #have a great symmetry, the 3 disintegrators being diff, delta,
                 #and eval.
                 disintegrator= ((e::algebraic, pt::{name=anything})->
                      eval(
                           eval(e, pt),
                           #Remove any Indicator made superfluous by the above eval:
                           Indicator= (r-> `if`(r::`=` and r, 1, 'Indicator'(r)))
                      )
                 ),
                 disintegrator_arg_extractor= (A-> op(1,A)= op([2,1], A))
                 #E.g., (x &M Ret(3)) --> (x= 3).
            )
       ]),

       #types for disint wrt vars (2nd arg to disint)
       t_wrt_var_type,
       t_disint_var, #Curiosity: giving this a type `type` causes a kernel crash
                     #during update-archive.
       t_disint_var_pair,
       ModuleLoad::static:= proc($) #Needed to declare types.
            TypeTools:-AddType(
                 t_wrt_var_type,
                 satisfies(t-> assigned(Wrt_var_types[op(0,t)]))
            );
            TypeTools:-AddType(t_disint_var, {name, name &M t_wrt_var_type});
            TypeTools:-AddType(     #Caution: recursive type: Make sure base cases
                 t_disint_var_pair, #are on left (a la McCarthy rule).
                 'Pair'(Or(t_disint_var, t_disint_var_pair) $ 2)
            )
       end proc,
       #end of types for disint

       DV::table,  #wrt vars, with their types and conditions
       p::symbol,  #"pair"--abstract representation
       #`path` is layers of fst(...) and snd(...) built by traversing tree
       #(Weird Maple syntax note: Module prefixes seem to be required for
       #assertion type checking. Failure to include them causes kernel crash
       #during execution.)
       path::{specfunc({Hakaru:-fst, Hakaru:-snd}), symbol},

       #Parses the 2nd arg---the wrt vars.
       # works by side-effect: accumulates "paths" to variables in T
       # via the module variable DV.
       traverse_var_tree::static:= proc(
            T::{t_disint_var, t_disint_var_pair}, $
       )::identical(NULL);
       local
            v::name, #the wrt var
            M::NewSLO:-disint:-t_wrt_var_type,
            pp #iterator over [fst, snd]---the deconstructors of Pair
       ;
            if T::t_disint_var then
                 #Add a default wrt-var type if none appears.
                 (v,M):= op(`if`(T::name, T &M 'Lebesgue'((-1,1)*~infinity), T));
                 DV[v]:= Record(
                      'wrt_var_type'= M,
                      'path'= path,
                      'disintegrator_arg'=
                           Wrt_var_types[op(0,M)]:-disintegrator_arg_extractor(
                                v &M M
                           )
                 );
                 path:= op(path) #Peel off outer layer: fst or snd.
            else #T::Pair(..., ...)---deconstruct recursively.
                 for pp in [fst, snd] do path:= pp(path); thisproc(pp(T)) end do
            end if;
            NULL
       end proc, #disint:-traverse_var_tree

       ModuleApply::static:= proc(
            m::t_Hakaru,
            #var &M wrt-var type, or Pairs thereof
            A::{t_disint_var, t_disint_var_pair},
            {ctx::t_kb_atoms:= []}, #context: parameter assumptions, "knowledge"
            $
       )::t_Hakaru;
       local
            mc,  #final integral to be passed to improve @ toLO; then result
                 #of each disintegration step
            kb:= foldr(assert, empty, ctx[]),
            V, #wrt vars
            v::name #iterator over V
       ;
            #Init module variables.
            DV:= table();
            p:= gensym('p');
            path:= fst(p);

            traverse_var_tree(A); # collect information about A in DV
            userinfo(3, Disint, "DV:", eval(DV));
            V:= indices(DV, 'nolist');
            mc:= Bind(
                 m, p,
                 #The piecewise condition is a conjunction of conditions, each
                 #condition formed from a (var,path) pair from DV.
                 piecewise(
                      And(seq(
                           Wrt_var_types[op(0, DV[v]:-wrt_var_type)]:-
                                cond_constructor(DV[v]:-path, v),
                           v= V
                      )),
                      Ret(snd(p)),
                      Msum()
                 )
            );
            mc:= improve(toLO(mc), _ctx= kb);
            #Does the order of application of the disintegrators matter?
            #Theoretically, I think not, it's just like differentiation. As far
            #as Maple's ability to do the computation, maybe it matters.
            for v in V do
                 mc:= applyop(
                      Wrt_var_types[op(0, DV[v]:-wrt_var_type)]:-disintegrator,
                      2, mc, DV[v]:-disintegrator_arg
                )
            end do;
            fromLO(mc, _ctx= kb)
       end proc #disint:-ModuleApply
  ;
       ModuleLoad()
  end module; #disint
  ###################### end of Carl's code ######################

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
