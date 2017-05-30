
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
  export ModuleApply, `do`;
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
              disintegrator_type_extractor= [ (ll-> kb-> KB:-genLebesgue(op(1,ll), op(op(2,ll)), kb)), AlmostEveryReal ]
         ),
         Counting= Record(
              cond_constructor= `<=`,
              disintegrator= LREtools[delta],
              disintegrator_arg_extractor= (A-> op(1,A)),
              disintegrator_type_extractor= [ (ll-> kb-> KB:-genSummation(op(1,ll), op(op(2,ll)), kb)), HInt ]
         ),
         #Ret is aka Dirac.
         Ret= Record(
              cond_constructor= `=`,
              disintegrator='eval',
              disintegrator_arg_extractor= (A-> op(1,A)= op([2,1], A)),
              #E.g., (x &M Ret(3)) --> (x= 3).

              disintegrator_type_extractor= [ (ll -> kb -> (op(1,ll), kb)) ]
              # disintegrator_type_extractor= (ll-> kb-> KB:-genLet(op(1,ll), op([2,1],ll), kb))
         )
    ]),

    #types for disint wrt vars (2nd arg to disint)
    t_wrt_var_type,
    t_disint_var, #Curiosity: giving this a type `type` causes a kernel crash
                  #during update-archive.
    t_disint_var_pair,

    TYPES := table(
         [(t_wrt_var_type=
              'satisfies(t-> assigned(Wrt_var_types[op(0,t)]))')
         ,(t_disint_var = '{name, name &M t_wrt_var_type}')
         ,(     #Caution: recursive type: Make sure base cases
           t_disint_var_pair = #are on left (a la McCarthy rule).
              ''Pair'(Or(t_disint_var, t_disint_var_pair) $ 2)')
         ]),

    ModuleLoad::static:= proc($) #Needed to declare types.
      BindingTools:-load_types_from_table(TYPES);
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
         vM, vK, mks, mk_ty, mk_ctx
    ;
         if T::t_disint_var then
              #Add a default wrt-var type if none appears.
              (v,M):= op(`if`(T::name, T &M 'Lebesgue'((-1,1)*~infinity), T));
              vK   := op(0,M);
              vM   := v &M M;
              mks := Wrt_var_types[vK]:-disintegrator_type_extractor;
              mk_ty := op(1,mks);
              if nops(mks)=2 then mk_ctx := ((e)->lam(v,op(2,mks)(),e));
              else                mk_ctx := ((e)->e);
              end if;
              DV[v]:= Record(
                   'wrt_var_type'= M,
                   'path'= path,
                   'disintegrator_arg'=
                        Wrt_var_types[vK]:-disintegrator_arg_extractor(vM),
                   'disintegrator_mktype'=mk_ty(vM),
                   'disintegrator_mkctx' =mk_ctx
              );
              path:= op(path) #Peel off outer layer: fst or snd.
         else #T::Pair(..., ...)---deconstruct recursively.
              for pp in [fst, snd] do path:= pp(path); thisproc(pp(T)) end do
         end if;
         NULL
    end proc, #disint:-traverse_var_tree

    subs_disint_data := proc(sub_vars, expr, $)
        local V:= [indices(DV, 'nolist')], v
            , vars := [indices(sub_vars, 'nolist')]
            , eqns := [seq(v=sub_vars[v], v=vars)]
            , sb := (x->subs(eqns,x));

        for v in V do
            DV[v]:-disintegrator_arg := sb(DV[v]:-disintegrator_arg);
        end do;

        sb(expr);
    end proc;

  ;
    ModuleApply := proc()::t_Hakaru;
      local todo,expr,t;
      expr, todo := disint:-`do`(args)[];
      for t in todo do expr := t(expr); end do; expr;
    end proc;

   `do` := proc(
    m::t_Hakaru,
    #var &M wrt-var type, or Pairs thereof
    A::{t_disint_var, t_disint_var_pair},
    ctx::{t_kb_atoms,t_kb}:= [] #context: parameter assumptions, "knowledge"
   ):: [t_Hakaru, list(appliable)];
   local
    mc,  #final integral to be passed to improve @ toLO; then result
         #of each disintegration step
    kb, var_rn := table(), mc_prts,
    V, #wrt vars
    v::name, #iterator over V
    improve_opts := [],
    todo := NULL,
    atodo := proc(z) todo := eval(todo), z; end proc,
    di, da, m_var, m_var_rn, m_ty, m_body, ctx1, x
   ;
    if m :: t_lam then
      m_var, m_ty, m_body := op(m);
      ctx1 := KB:-build_kb(ctx,"disint",KB:-empty);
      m_var_rn, ctx1 := KB:-genType(m_var, m_ty, ctx1);
      return
        applyop( t->[op(t),x->'lam'(m_var_rn, m_ty, x)]
               , 2,`do`(subs(m_var=m_var_rn, m_body)
                       , A, ctx1, _rest));
    end if;

    if not {_rest} in {{'do_lam'},{}} then
      error "bad extra args: %1", {_rest};
    end if;

    #Init module variables.
    DV:= table();
    p:= gensym('p');
    path:= fst(p);

    traverse_var_tree(A); # collect information about A in DV
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
         ));

    kb := empty;
    for v in ListTools[Reverse](V) do
        var_rn[v], kb := DV[v]:-disintegrator_mktype(kb);
    end do;
    kb := build_kb(ctx,"disint",kb);
    mc := subs_disint_data(var_rn, mc);

    atodo(x->toLO(x));
    atodo(x->improve(x, _ctx=kb,improve_opts));
    #Does the order of application of the disintegrators matter?
    #Theoretically, I think not, it's just like differentiation. As far
    #as Maple's ability to do the computation, maybe it matters.
    for v in V do
      di   := Wrt_var_types[op(0, DV[v]:-wrt_var_type)]:-disintegrator;
      da   := DV[v]:-disintegrator_arg;
      atodo(unapply('applyop'(di, 2, x, da),x));
      atodo(x->improve(x, _ctx=kb,improve_opts));
    end do;

    atodo(x->fromLO(x, _ctx= kb));
    ## simplify integrals which do not mention the LO var (i.e. integrals in
    ## weights). this is a hack, we should do this inside of `improve'* in
    ## the correct place.  It is required to see the correct output for
    ## d7_normalFB1.
    #
    ## * Or, some other simplifier, which does only specific things - note
    ## the simplification we hope to see here (in d7) can only be done after
    ## the application of the `diff'. So just chucking it into `improve'
    ## might not be the correct thing to do. Calling `improve' at all might
    ## be wrong since we roundtrip through pulling off domains and replacing
    ## them (this is sort of expensive..), although we may also want such
    ## simplifications here - the application of the `diff' might give a new
    ## domain problem that can be improved significanly.
    # 'Simplify' partitions in weights by converting them to piecewise and
    # letting piecewise simplify do the work; and evaluate integrals in weights
    atodo(x->
          subsindets( x, 'Weight(anything, anything)'
                    , mw -> applyop(x->simplify_assuming(
                        subsindets( subsindets(x,Partition,PartitionToPW)
                                  , And(specfunc(`Int`)
                                       ,satisfies(e->indets(e,specfunc(`exp`))<>{})
                                       )
                                  , value
                                  )
                        , kb ), 1, mw)));

    atodo(x->subs_disint_data( table([seq(var_rn[v]=v, v=V)]), x));

    if 'do_lam' in {_rest} then
      for v in ListTools[Reverse](V) do
        atodo(x->DV[v]:-disintegrator_mkctx(x));
      end do;
    end if;

    [mc, [todo]];
   end proc; #disint:-ModuleApply
   ModuleLoad();
  end module; #disint
  ###################### end of Carl's code ######################
