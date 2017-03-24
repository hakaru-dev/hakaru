
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
  export ModuleApply;
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
              disintegrator_arg_extractor= (A-> op(1,A)),
              disintegrator_type_extractor= (ll-> kb-> KB:-genLebesgue(op(1,ll), op(op(2,ll)), kb))
         ),
         Counting= Record(
              cond_constructor= `<=`,
              disintegrator= LREtools[delta],
              disintegrator_arg_extractor= (A-> op(1,A)),
              disintegrator_type_extractor= (ll-> kb-> KB:-genSummation(op(1,ll), op(op(2,ll)), kb))
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
              disintegrator_arg_extractor= (A-> op(1,A)= op([2,1], A)),
              #E.g., (x &M Ret(3)) --> (x= 3).

              disintegrator_type_extractor=(ll -> kb -> (op(1,ll), kb))
              # disintegrator_type_extractor= (ll-> kb-> KB:-genLet(op(1,ll), op([2,1],ll), kb))
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
         pp, #iterator over [fst, snd]---the deconstructors of Pair
         vM, vK
    ;
         if T::t_disint_var then
              #Add a default wrt-var type if none appears.
              (v,M):= op(`if`(T::name, T &M 'Lebesgue'((-1,1)*~infinity), T));
              vK   := op(0,M);
              vM   := v &M M;
              DV[v]:= Record(
                   'wrt_var_type'= M,
                   'path'= path,
                   'disintegrator_arg'=
                        Wrt_var_types[vK]:-disintegrator_arg_extractor(vM),
                   'disintegrator_mktype'=
                        Wrt_var_types[vK]:-disintegrator_type_extractor(vM)
              );
              path:= op(path) #Peel off outer layer: fst or snd.
         else #T::Pair(..., ...)---deconstruct recursively.
              for pp in [fst, snd] do path:= pp(path); thisproc(pp(T)) end do
         end if;
         NULL
    end proc #disint:-traverse_var_tree
  ;
   ModuleApply := proc(
    m::t_Hakaru,
    #var &M wrt-var type, or Pairs thereof
    A::{t_disint_var, t_disint_var_pair},
    {ctx::t_kb_atoms:= []}, #context: parameter assumptions, "knowledge"
    $
   )::t_Hakaru;
   local
    mc,  #final integral to be passed to improve @ toLO; then result
         #of each disintegration step
    kb0 := build_kb(ctx,"disint"),
    kb,
    kbs_vars := table(), var_rn,
    V, #wrt vars
    v::name #iterator over V
   ;

    #Init module variables.
    DV:= table();
    p:= gensym('p');
    path:= fst(p);

    traverse_var_tree(A); # collect information about A in DV
    userinfo(3, Disint, "DV:", eval(DV));
    V:= [indices(DV, 'nolist')];


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


    kb := kb0;
    for v in ListTools[Reverse](V) do
        var_rn[v], kb := DV[v]:-disintegrator_mktype(kb);
        kbs_vars[v] := kb;

        mc, DV[v]:-disintegrator_arg :=
          op( subs( v=var_rn[v]
                  , [mc,DV[v]:-disintegrator_arg]
                  ));

    end do;

    userinfo(3, Disint, "Disint defn:", eval(mc), kb);
    userinfo(3, Disint, "Disint path:", path);

    mc:= improve(toLO(mc), _ctx= kb);

    userinfo(3, Disint, "Disint improved:", eval(mc));

    #Does the order of application of the disintegrators matter?
    #Theoretically, I think not, it's just like differentiation. As far
    #as Maple's ability to do the computation, maybe it matters.
    for v in V do
         mc:= applyop(
    	  Wrt_var_types[op(0, DV[v]:-wrt_var_type)]:-disintegrator,
    	  2, mc, DV[v]:-disintegrator_arg
        );

         # simplify integrals which do not mention the LO var (i.e. integrals in
         # weights). this is a hack, we should do this inside of `improve'* in
         # the correct place.  It is required to see the correct output for
         # d7_normalFB1.

         # * Or, some other simplifier, which does only specific things - note
         # the simplification we hope to see here (in d7) can only be done after
         # the application of the `diff'. So just chucking it into `improve'
         # might not be the correct thing to do. Calling `improve' at all might
         # be wrong since we roundtrip through pulling off domains and replacing
         # them (this is sort of expensive..), although we may also want such
         # simplifications here - the application of the `diff' might give a new
         # domain problem that can be improved significanly.
         mc :=
          kb_assuming_mb( _mc ->
            subsindets( _mc, And(specfunc(`Int`),freeof(op(1, _mc))), x-> simplify( int(op(x)) ) )
                        )(mc, kbs_vars[v], x->x);

         # all of the below achieve the same as the above, but in a different
         # way.
         # mc :=  subs( `int`=`Int`, improve( eval(mc, `Int`=`int`), _ctx=kb ) );
         # mc := subs( `int`=`Int`, improve( eval(mc, `Int`=`int`) , _ctx=kb) );
         # mc := kb_assuming_mb(x-> subs(`int`=`Int`,simplify(eval(x, `Int`=`int`))) )(mc, kb, x->x);

        userinfo(3, Disint, "Disint diff:", eval(mc));


        mc, DV[v]:-disintegrator_arg :=
          op( subs( var_rn[v]=v
                  , [mc,DV[v]:-disintegrator_arg]
                  ));
    end do;

    mc := fromLO(mc, _ctx= kb0);

    userinfo(3, Disint, "Disint hakaru:", eval(mc));

    mc

   end proc; #disint:-ModuleApply
   ModuleLoad();
  end module; #disint
  ###################### end of Carl's code ######################
