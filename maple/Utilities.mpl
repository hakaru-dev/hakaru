# Various utilities used by Hakaru which don't fit logically elsewhere
Utilities := module ()
  option package;

  # Returns true for a sequence for which all the elements are equal up to the
  # specified equality, or false otherwise. A 0-length sequence produces an
  # error.
  export the := proc(as, eq:=`=`, $)
    if nops(as)=0 then error "sequence %1 must have at least one operand", as; end if;
    andmap(x -> eq(x,op(1,as)), [op(2..-1,as)]);
  end proc;

  # zip together an arbitrary number of lists;
  # - if any lists are shorter, the function recieves all available arguments
  #    e.g. zip_k(F, [a,b], [c]) -> [F(a, c), F(b)]
  # - if any lists contain subslists, those are also zipped together, so
  #   zip_k(F, as) and zip_k(F, [as]) are equivalent. To avoid this, use a 0-th
  #   operand other than `[]`.
  #    e.g. zip_k(F, [a,b], [ [c,d], [e,f] ]) -> [F(a, c, d), F(b, e, f)]
  export zip_k := proc(f)
    map(f@op@ListTools[Flatten], foldl((a,b)->zip(`[]`,a,b,[]), _rest));
  end proc;

  # Merges two records, `rspec' and `rdef'. If `rspec' contains any fields of
  # `rdef', the fields of `rspec' are taken.
  export merge_record_default := proc(rdef::record, rspec::record, $)
    local s;
    s   := {exports(rdef)} intersect {exports(rspec)};
    Record[ Record[rdef](op(map(`-`,s))) , rspec ]();
  end proc;

  # Creates a new record with `field' updated to the given function applied to
  # `field' of the given record.
  export upd_field := proc(r::record, field::name, k, $)
    Record[r](-field,field=k(r[field]))
  end proc;

  # Simplistic negation of relations. Used by Hakaru:-flatten_piecewise, KB, and
  # Domain.
  export negated_relation:= table([`<`, `<=`, `=`, `<>`] =~ [`>=`, `>`, `<>`, `=`]);

  # Takes the bool type (true/false) to mean universal and empty relations
  # respectively.  i.e. negate R, where R is an 'atomic' relation of a KB.
  # This is used by KB and Partition
  export negate_rel:= proc(R::Relation, $)::Relation;
    if R :: truefalse then
      not R
    elif R :: relation then
      negated_relation[op(0,R)](op(R));
    else
      # This is to appease 'piecewise', which won't be happy with Not
      # However, KB doesn't really care - it's already expecting {Not,not}
      # 'Technically' this is a KB 'constructor'!
      not(R);
    end if;
  end proc;

  # Differs from negate_rel in that
  #  [ negate_rel (x) ] = "Not x"  but
  #  [ negate_rels(x) ] = "x"
  export negate_rels := proc(e, $)
    subsindets(e, { specfunc(relation, `Not`), `not`(relation) }, negate_rel@op );
  end proc;

  # Creates an N-ary operator `Plus` such:
  #  Plus(Plus(a,b),c)=Plus(a,Plus(a,b))
  #  Plus(a,Iden)=a
  #  Plus(a,Zero)=Zero
  #  Plus(a)=a
  #  Plus(x,x)=x
  export Mk_Plus := proc(plus,iden,zero,$) proc()
    local as := {args};
    as := map(a->if op(0,a)=plus then op(a) else a end if, as);
    if zero in as then return zero end if;
    as := remove(`=`,as,iden);
    if nops(as)=0 then iden
    elif nops(as)=1 then op(1,as)
    else plus(op(as))
    end if;
  end proc; end proc;

  # Replacements for `and`, `or`, `not` which do not
  # evaluate "x = y" to "false" when "x,y" are unbound vars.
  export bool_And := Mk_Plus(And,true ,false);
  export bool_Or  := Mk_Plus(Or ,false,true);
  export bool_Not := proc(a,$)
    if a :: Relation and not (a :: `::`) then
      subsindets(negate_rel(a), `not`, Not@op);
    else
      Not(a)
    end if;
  end proc;

  # boolean_if should be equivalent to `if`, but it assumes
  # all its arguments are boolean conditions, so it basically
  # simplifies "cond and th or not cond and el"
  export boolean_if := proc(cond, th, el, $)
    use
      a = ((x,y)-> `if`(x=true,y, `if`(x=false,x,
                   `if`(y=true,x, `if`(y=false,y, And(x,y)))))),
      o = ((x,y)-> `if`(x=false,y, `if`(x=true,x,
                   `if`(y=false,x, `if`(y=true,y, Or (x,y)))))),
      n = (x    -> `if`(x=false,true,
                   `if`(x=true,false,             Not(x))))
    in
      o(a(cond,th), a(n(cond),el))
    end use
  end proc;

  # In order to hopefully produce a simplification,
  #   assert_deny will on some occasions repeatedly apply
  #   `simplify@ln` in the hopes of producing an 'improved'
  #   constraint. This metric gives the stopping condition
  # - when the simplification ceases to improve the constraint
  # - which is when the metric is made no less by the `simplify@ln`.
  # Since this is a `length`, this is strictly decreasing,
  #  so such a loop will 'provably' always terminate
  export log_metric := proc(e, x, $)
    local m, L;
    m := select(depends, indets(e, 'exp(anything)'), x);
    length(subsindets(map2(op, 1, m), name, _->L));
  end proc;

  # Used by both KB and Domain
  export try_improve_exp := proc(b0, x, ctx, $)
    local b := b0, log_b;
    do
      try log_b := map(simplify@ln, b) assuming op(ctx); catch: break; end try;

      if log_metric(log_b, x) < log_metric(b, x)
         and (andmap(e->is(e,real)=true, log_b) assuming op(ctx)) then
        b := log_b;
      else
        break;
      end if;
    end do;
    b;
  end proc;

  # Given an expression containing products and sums, i.e. polynomials
  # and a function , applies this expression to each factor and summand
  export for_poly := proc(e, f, $)
    if e :: '{`+`,`*`}' then map(for_poly, e, f)
    elif e :: 'specfunc({product,Product,sum,Sum})' then
      applyop(for_poly, 1, e, f)
    else f(e)
    end if
  end proc;

  # Apply a function to each summand at the top level of the expression
  export distrib_over_sum := proc(f,e,$) `+`(op(map(f,convert(e, 'list',`+`)))) end proc;

  # Like convert(e, 'list', `*`) but tries to keep the elements positive
  export list_of_mul := proc(e, $)
    local rest, should_negate, can_negate, fsn;
    rest := convert(e, 'list', `*`);
    rest := map((f -> [f, signum(f),
                       `if`(f::'{specfunc({Sum,sum}),anything^odd}',
                            applyop(`-`,1,f),
                       `if`(f::'specfunc(ln)',
                            applyop(`/`,1,f),
                            -f))]),
                rest);
    should_negate, rest := selectremove(type, rest,
      '[anything, -1, Not(`*`)]');
    if nops(should_negate) :: even then
      [seq(op(3,fsn), fsn=should_negate),
       seq(op(1,fsn), fsn=rest)]
    else
      can_negate, rest := selectremove(type, rest,
        '[{`+`, specfunc({Sum,sum,ln}), `^`}, Not(1), Not(`*`)]');
      if nops(can_negate) > 0 then
        [seq(op(3,fsn), fsn=should_negate),
         op([1,3], can_negate),
         seq(op(1,fsn), fsn=subsop(1=NULL, can_negate)),
         seq(op(1,fsn), fsn=rest)]
      else
        [seq(op(3,fsn), fsn=subsop(-1=NULL, should_negate)),
         op([-1,1], should_negate),
         seq(op(1,fsn), fsn=rest)]
      end if
    end if
  end proc;

  export mysolve := proc(constraints)
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

  # A debugging utility that's like `and` except it calls `userinfo` if there is
  # disagreement
  export and_info := proc(e :: {list,set})
    local s, r;
    s, r := selectremove(evalb, e);
    if nops(r) = 0 then return true end if;
    if nops(s) > 0 then userinfo(op([_rest, s, r])) end if;
    return false;
  end proc;

  # Simplifies relations using `Logic:-Normalize' and places the result in a
  # canonical form. The input can be {and,not,or} but the output is always
  # {And,Or,Not}.
  #  - false, true are expressed as And and Or
  #  - When `norty' is DNF/CNF then the outer constructor is always Or/And
  #
  # TODO:
  # A better interface for `simpl_relation` - something that allows it to treat
  #   arbitrary constructor forms as And, Or, Not. Typically, we do a `subs` right
  #   before the call to `simpl_relation` to put things in the right form, then
  #   another `subs` immediately inside `simpl_relation` to turn `And,Or` into `&and,&or`.
  export simpl_relation :=
  proc( expr_ :: {relation, boolean, specfunc({`And`,`Not`,`Or`}), `and`, `not`, `or`}
      , { norty := 'DNF' }
      , $) :: { specfunc(specfunc({Relation, specfunc(relation, Not)}, `Or`), `And`)
              , specfunc(specfunc({Relation, specfunc(relation, Not)}, `And`), `Or`)
              };
      local expr := expr_, outty, outmk, inty, inmk, ty_ord ;

      expr := foldr( proc(v,e) subsindets(e, op(v)) end proc
                   , expr
                   , [ { specfunc(relation, `Not`), `not`(relation) }
                     , x-> negate_rel(op(1,x)) ]
                   , [ { specfunc(`Not`), `not` }
                     , x->Logic:-`&not`(op(1,x)) ]
                   , [ { specfunc(`Or`), `or` }
                     , x->Logic:-`&or`(op(x)) ]
                   , [ { specfunc(`And`), `and` }
                     , x->Logic:-`&and`(op(x)) ] );
      expr := Logic:-Normalize(expr, form=norty);
      expr := foldr( proc(v,e) subsindets(e, op(v)) end proc
                   , expr
                   , [ specfunc(Logic:-`&and`), x->`And`(op(x)) ]
                   , [ specfunc(Logic:-`&or`) , x->`Or`(op(x)) ]
                   , [ specfunc(Logic:-`&not`), x->negate_rel(op(1,x))  ] );

      if expr :: identical(false) then
        return `if`(norty='DNF', `Or`(), `And`(`Or`()));
      elif expr :: identical(true) then
        return `if`(norty='DNF', `Or`(`And`()), `And`());
      end if;

      ty_ord := `if`(norty='DNF', [1,2], [2,1]);
      outty, inty := [ 'specfunc(Or)', 'specfunc(And)' ][ty_ord][];
      outmk, inmk := [ `Or`, `And` ][ty_ord][];

      if not expr :: outty then expr := outmk(expr) end if;
      map(x -> if not x :: inty then inmk(x) else x end if, expr);
  end proc;

  # Classify a relation by matching either the LHS or RHS against
  # a given predicate, and placing the relation in a canonical form
  # where the LHS (3rd component of the result) is the side matching
  # the predicate, or FAIL of neither side matches.
  export classify_relation := proc(r0::relation, vars0, $)
    ::{identical(FAIL), [identical(B_LO,B_HI,B_EQ,B_NEQ),
                         satisfies(q->q in {indices(flip_relation,nolist)}),
                         anything, anything]};
    local r_k, r_s, in_vars, vars := vars0, r := r0;
    if vars :: ({set,list})({name,list(name)}) then
      vars := map(x->`if`(x::list,op(1,x),x),vars);
      vars := {op(vars)}; in_vars := x->x in vars;
    elif vars :: procedure then
      in_vars := vars;
    elif vars :: type then
      in_vars := x->type(x,vars);
    else error "unknown argument: %1 "
               "(expecting variables, variable membership check)"
               , vars;
    end if;
    if r :: {`<=`,`<`, `=`, `<>`} then
      if in_vars(rhs(r)) then
        r_k := flip_relation[op(0,r)]; r_s := rhs(r), lhs(r);
      elif in_vars(lhs(r)) then
        r_k := op(0,r); r_s := op(r);
      else return FAIL end if;
      [ classify_relop[r_k], r_k, r_s ];
    else FAIL
    end if;
  end proc;
  local flip_relation := table([`=`=`=`,`<>`=`<>`,`<=`=`>=`,
                                `<`=`>`,`>=`=`<=`,`>`=`<`]);
  local classify_relop := table([`=`=B_EQ,`<>`=B_NEQ,`<=`=B_HI,
                                 `<`=B_HI,`>=`=B_LO,`>`=B_LO]);

  # Functionalized, curried `if' statement
  export Case :=
  proc(ty,f,g)
    proc(x)
      if x::ty then f(x) else g(x) end if
    end proc
  end proc;

  # A replacement for `coulditbe .. assuming ..' which uses `is' internally
  # (since `is' is actually stronger than `coulditbe'); tries to handle `Or`s
  # correctly (which don't do well with `assuming'); and catches some exceptions
  # which we are reasonably sure have a valid interpretation.
  export rel_coulditbe := ProfileFn(do_rel_coulditbe, 1);
  local do_rel_coulditbe := proc(a,as_,$)
    option remember, system;
    local os, rs, as := as_;
    if as::{set,list,specfunc(And),`and`} then
      as := [op(as)];
    elif as::Relation then
      as := [as];
    else
      error "unknown input format: %1", as;
    end if;
    os, rs := selectremove(type, as, {specfunc(Or),`or`});

    if os=[] then
      try
        not(is(bool_Not(a)) assuming op(as));
      catch "when calling '%1'. Received: 'contradictory assumptions'" :
        # technically this means the KB was already contradictory, we
        # just didn't know?
        return false;
      catch "when calling '%1'. Received: "
            "'side relations must be polynomials in"
            " (name or function) variables'":
        # This is seemingly a Maple bug - the condition could still be, but we
        # don't know, so conservatively return true.
        WARNING( sprintf( "siderels bug:\n\t'%s'\n"
                          "when calling coulditbe(%%1) assuming (%%2)"
                          , StringTools[FormatMessage](lastexception[2..-1])),
                 a, as );
        return true;
      catch "when calling '%3'. Received: "
            "'when calling '%2'. Received: "
            "'expression independent of, %0''":
        error expr_indp_errMsg(), a, as;
      catch "when calling '%2'. Received: 'expression independent of, %0'":
        error expr_indp_errMsg(), a, as;
      end try;
    else
      ormap(o1->rel_coulditbe(a,[o,op(rs)])=true, os);
    end if;
  end proc;

  local expr_indp_errMsg := proc($)
    sprintf("Something strange happened(%s)\n"
            "\tin coulditbe(%%1) assuming %%2"
            ,StringTools[FormatMessage](lastexception[2..-1]))
  end proc;


  # Print profiling information for a function when `infolevel' for that
  # function is set to at least 3, and assertlevel>0; e.g.
  #  > do_func := proc() .. func .. end: func := ProfileFn(do_func):
  #  > infolevel[func] := 3:
  #  > kernelopts(assertlevel) := 1:
  #  > func(a,b,c);
  #
  #  - profiling information is only printed for runs of the function
  #    which use a minimum amount of time, bytesalloc, or bytesused
  #  - setting infolevel >= 5 prints profiling information for all runs of the
  #    function.
  #  - less than a minimum amount of a resource consumed omits the actual usage
  #    with both infolevel >= 3 < 5 and infolevel >= 5 (just "less than <min>"
  #    is printed instead)
  #  - profiling information is not printed for recursives calls of a function
  #    (in other words, if a recursive function is profiled, only non-recursive
  #     instances will have profiling attached)
  export ProfileFn := module()
    local get_prof := proc()
      [ time[real](), kernelopts(bytesalloc)/2^20, kernelopts(bytesused)/2^20 ];
    end proc;
    local ppr_prof1 := proc(m,a,nm,fmt0,$)
      local v,p,fmt;
      v,p,fmt := `if`(a>=m, ["",a,fmt0], ["less than ",m,"%a"])[];
      cat(v,sprintf(fmt,p)," ",nm);
    end proc;
    local ppr_prof := proc(min_t, t, nms, $)
      local prefix, prefixl, strs;
      prefix := "took "; prefixl := length(prefix);
      strs :=
      zip_k(ppr_prof1, min_t, t, nms);
      cat(op(
        ListTools:-Interleave(
          ["\n\t"$nops(strs)],
          [prefix,cat(" "$prefixl)$(nops(strs)-1)],
          strs)));
    end proc;
    export ModuleApply :=
    proc(fn,min_t:=0.1,min_ba:=100,min_bu:=100)
      proc()
        local t, min_prof, profs, res, ctx, fncall;
        if kernelopts(assertlevel) > 0 and
           not (assigned(_Env_ProfileFn_inside[fn])) and
           assigned(infolevel['procname']) and
           infolevel['procname'] >= 3
        then
          _Env_ProfileFn_inside[fn] := true;
          t[0] := get_prof();
          res  := fn(args);
          t[1] := get_prof();
          t[2] := zip(`-`,t[1],t[0]);
          ctx  := map(op@getassumptions,indets([fn,args],Name));
          fncall := sprintf("%a(%q)",'procname',args);
          ctx    := sprintf("assuming (%q)", op(ctx));
          min_prof := [min_t,min_ba,min_bu];
          profs  := ppr_prof(min_prof, t[2],
                             [["seconds","%.3f"],
                              ["MiB alloc", "%.3f"],
                              ["MiB total used", "%.3f"]]);
          userinfo(`if`(`or`(zip(`>`,t[2], min_prof)[]),3,5),
                   'procname',
                   printf("Evaluating\n\t%s\n\t%s%s\n",fncall,ctx,profs));
          res;
        else
          fn(args)
        end if;
      end proc;
    end proc;
  end module;

  # The closure of `f:set->set' with respect to `x:set'. That is, all values
  # which are outputs of `f' applied to `x' or an output of `f'.
  export cl := proc(f,x,$)
    local rs := f(x) minus x;
    if rs={} then x else cl(f,rs) union x end if;
  end proc;

  # The first `n' elements of a list, or the entire list if it has fewer than
  # `n' elements.
  export take := proc(xs,n,$)
    op(1,[ListTools[LengthSplit](xs,n)]);
  end proc;

  # A copy of `:-profile' with
  #  - better pretty printing of the result
  #  - bug fix for the fact that multiple names of sub-modules with the same
  #    'root' name cannot be profiled (e.g. M1:-x and M2:-x, commonly an issue
  #    with ModuleApply)
  #  - automatic collection of the names present in the Hakaru library
  # To profile `f(as)', call `Profile(f,_args=[as])'. Profiling information
  #  if printed to stdout
  # Extra arguments to `Profile' are passed to `GetProf' and `PPrProf', which
  #  determine which stats to profile and how to pretty print profiling
  #  information.
  # Environment variables affecting this function:
  #  _Env_Profile_count_ppr  = number of profiled names to print
  #  _Env_Profile_remove_ppr = selector function (: name->bool) to omit
  #    certain names from the profiling output
  export Profile := module()
    option package;
    export ModuleApply, GetProf, PPrProf, modules_to_profile, names_to_profile;
    local ModuleLoad, cl, profile_flag_to_ord, name_to_string, take;

    modules_to_profile := proc()
      kernelopts(opaquemodules=false):
      { 'BindingTools', 'Hakaru', 'KB', 'Partition', 'Partition:-Simpl', 'Loop'
      , 'Domain', 'NewSLO', 'Summary'
      , entries(Domain:-Improve:-Simplifiers, nolist)
      };
    end proc;

    names_to_profile := proc()
      option remember, system;
      local ns;
      kernelopts(opaquemodules=false):
      ns := cl(curry(map,x->CodeTools:-Profiling:-getMemberFuncs(x,true)),
               modules_to_profile());
      map(proc(n)
            if n::`module`('ModuleApply') then 'n[ModuleApply]' elif n::procedure then n else NULL end if
          end proc, ns);
    end proc;

    name_to_string := (x->convert(x,'string'));

    profile_flag_to_ord := table(
       ['alpha' = (proc (a, b) lexorder(a[1],b[1]) end proc)
       ,'ralpha' = (proc (a, b) not lexorder(a[1],b[1]) end proc)
       ,'time' = (proc (a, b) evalb(a[4] < b[4]) end proc)
       ,'rtime' = (proc (a, b) evalb(b[4] < a[4]) end proc)
       ,'bytes' = (proc (a, b) evalb(a[6] < b[6]) end proc)
       ,'rbytes' = (proc (a, b) evalb(b[6] < a[6]) end proc)
       ,'load' = (proc (a, b) evalb(a[6]*a[6]*a[4] < b[6]*b[6]*b[4]) end proc)
       ,'rload' = (proc (a, b) evalb(b[6]*b[6]*b[4] < a[6]*a[6]*a[4]) end proc)
       ]);

    GetProf := proc(fns::({list,set})(satisfies(x->member(x,:-profile_profiled)))
                   ,{_flag:='rload'}
                   )
      local i, totaltime, totalbytes, totaldepth, totalcalls, timepc, bytespc, numargs, displist, totaltimepc, totalbytespc
           , ix, get_timepc, get_bytespc, get_nm, nm, flag ;
      global profile_time, profile_bytes, profile_maxdepth, profile_calls, profile_profiled;

      flag := _flag;
      totaltime, totalbytes, totalcalls, totaldepth := 0$4;
      numargs := nops(fns);

      for i to nops(profile_profiled) do
        ix := name_to_string(profile_profiled[i]);
        totaltime := totaltime+profile_time[ix];
        totalbytes := totalbytes+profile_bytes[ix];
        totalcalls := totalcalls+profile_calls[ix];
        totaldepth := totaldepth+profile_maxdepth[ix];
      end do;

      if totaltime = 0 then
        get_timepc := i->0;
        totaltimepc := 0;
      else
        get_timepc := i->100*profile_time[name_to_string(profile_profiled[i])]/totaltime;
        totaltimepc := 100;
      end if;
      for i to nops(profile_profiled) do
        timepc[name_to_string(profile_profiled[i])] := get_timepc(i);
      end do;

      if totalbytes = 0 then
        get_bytespc := i->0;
        totalbytespc := 0;
      else
        get_bytespc := i->100*profile_bytes[name_to_string(profile_profiled[i])]/totalbytes;
        totalbytespc := 100;
      end if;
      for i to nops(profile_profiled) do
        bytespc[name_to_string(profile_profiled[i])] := get_bytespc(i);
      end do;

      displist := [];
      if 0 < numargs then
        get_nm := i->op(i,fns);
      else
        numargs := nops(profile_profiled);
        get_nm := i->profile_profiled[i];
      end if;
      for i to numargs do
        nm := get_nm(i); ix := name_to_string(nm);
        displist := [op(displist),
                     [nm, map(q->q[ix],[profile_maxdepth, profile_calls,
                                        profile_time, timepc, profile_bytes, bytespc])[]  ]];
      end do;

      displist := sort(displist, profile_flag_to_ord[flag]);
      displist, [totaldepth,totalcalls,totaltime,totaltimepc,totalbytes,totalbytespc];
    end proc;

    PPrProf := proc(dat,tot,{_max_name_len:=55,_prof_name:=`function`})
      local i, k, pr_nm;
      k := _max_name_len; pr_nm := _prof_name;

      printf(cat(pr_nm,(" "$k-StringTools[Length](convert(pr_nm,string))),
                 `depth    calls     time    time%%     `));
      printf(`    bytes   bytes%%\n`);
      printf(cat("--"$k+1,`\n`));
      for i from 1 to nops(dat) do
        printf(cat(`%-`,convert(k,string),`a%7d%9d%9.3f%9.2f%14d%9.2f\n`),
               op(1..7,dat[i]));
      end do;
      printf(cat("--"$k+1,`\n`));
      printf(cat(`%-`,convert(k,string),`a%7d%9d%9.3f%9.2f%14d%9.2f\n\n`),
             `total:`,op(1..6,tot));
        return NULL
    end proc;

    ModuleApply := proc(f,{_args:=[]})
      local names_prof, res, nppr, rm_ppr, prf, tot, as; as := _args;
      if assigned(_Env_Profile_count_ppr) then
        nppr := _Env_Profile_count_ppr;
      else nppr := 25; end if;
      if assigned(_Env_Profile_remove_ppr) then
        rm_ppr := _Env_Profile_remove_ppr;
      else rm_ppr := (x->andmap(q->op(q,x)<0.001,[3,4,6])); end if;

      unprofile();
      names_prof := names_to_profile();
      profile(op(names_prof));
      if   f::string then res := NULL; read(f);
      else                res := f(op(as)); end if;
      prf, tot := GetProf(names_prof,_rest);
      unprofile();
      prf := remove(rm_ppr, prf);
      PPrProf(take(prf,nppr),tot,_rest);
      res;
    end proc;

    ModuleLoad := proc($)
      unprotect(:-convert);
      :-convert := overload([proc(x::name,_::identical(string),$) option overload(callseq_only); sprintf("%a",x) end proc
                            ,:-convert]);
      protect(:-convert);
      NULL;
    end proc;
    ModuleLoad();
  end module;

  local ModuleLoad := proc($)
    BindingTools:-load_types_from_table(
      table(
        [(Relation=
          ''{`::`, boolean, `in`, specfunc(anything,{Or,Not,And})}'')
        ,(Name = 'And(name, Not({constant,undefined}))')
        ]));
  end proc;
  ModuleLoad();
end module;
