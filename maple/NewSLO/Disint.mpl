
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
