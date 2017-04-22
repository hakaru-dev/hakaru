export Improve := module ()
    export Simplifiers := table();
    export ModuleApply := proc(dom :: HDomain, $)::HDomain_mb;
        local es := map(si->Simplifiers[si]
                       , sort( [indices(Domain:-Improve:-Simplifiers,nolist) ]
                             , key=(si->Simplifiers[si]:-SimplOrder)))
             , bnd, sh;
        bnd, sh := op([1..2], dom);
        sh := foldr(((f,q)->proc() cmp_simp_sh(f,q,args) end proc)
                   ,(proc(_,b,$) b end proc), op(es))(bnd, sh);
        DOMAIN(bnd, sh);
    end proc;

    local ModuleLoad := proc($)
      LoadSimplifiers();
      LoadSimplifiers := (proc() end proc);
    end proc;#ModuleLoad

    local LoadSimplifiers := proc($)
      local lib_path, drs, improve_path, simpls_paths, simpl_path, names0, names1, new_names, nm;
      unprotect(Simplifiers);
      lib_path := LibraryTools:-FindLibrary(Hakaru);
      ASSERT(lib_path<>NULL);
      lib_path := FileTools:-ParentDirectory(lib_path);
      drs := kernelopts(dirsep);
      improve_path := `cat`(lib_path,drs,"Domain",drs,"Improve");

      simpls_paths := FileTools:-ListDirectory(improve_path);
      for simpl_path in simpls_paths do
        names0 := {anames(user)};
        read(`cat`(improve_path,drs,simpl_path));
        names1 := {anames(user)};
        new_names := names1 minus names0;
        for nm in new_names minus {entries(Simplifiers,nolist)} do
          if nm :: `module`(SimplName,SimplOrder) then
            if assigned(Simplifiers[nm:-SimplName])
            and not Simplifiers[nm:-SimplName] = nm then
              WARNING("overwriting old simplifier! (%1)", Simplifiers[nm:-SimplName]):
            end if;
            Simplifiers[nm:-SimplName] := eval(nm);
          else
            WARNING("not recognized as a simplifier: %1", nm);
          end if;
        end do;
      end do;
      protect(Simplifiers);
    end proc;#LoadSimplifiers

    local combine_errs := proc(err::DomNoSol, mb, $)
        if mb :: DomNoSol then
            DNoSol(op(err),op(mb));
        else
            mb
        end if;
    end proc;

    # compose two simplifiers, combining errors if both fail
    local cmp_simp_sh := proc(simp0, simp1, bnd, sh :: {DomShape,DomNoSol}, $)::{DomShape,DomNoSol};
      local res, sh1; sh1 := simp0(bnd, sh); simp0:-SimplName;
      if not sh1 :: DomNoSol then
          simp1(bnd, sh1);
      else
          combine_errs( sh1, simp1(bnd, sh) );
      end if;
    end proc;

    export classify_relation := proc(r0::relation, vars0, $)
      ::{identical(FAIL), [identical(B_LO,B_HI,B_EQ,B_NEQ), satisfies(q->q in {indices(flip_relation,nolist)}), name, algebraic]};
      local r_k, r_s, in_vars, vars := vars0, r := r0;
      if vars :: ({set,list})(name) then
        vars := {op(vars)}; in_vars := x->x in vars;
      elif vars :: DomBound then
        vars := DomBound:-Bound:-varsOf(vars,"set"); in_vars := x->x in vars;
      elif vars :: appliable then
        in_vars := vars;
      elif vars :: type then
        in_vars := x->type(x,vars);
      else error "unknown argument: %1 (expecting variables, variable membership check, "
                 "or domain bounds)", vars;
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
    local flip_relation := table([`=`=`=`,`<>`=`<>`,`<=`=`>=`,`<`=`>`,`>=`=`<=`,`>`=`<`]);
    local classify_relop := table([`=`=B_EQ,`<>`=B_NEQ,`<=`=B_HI,`<`=B_HI,`>=`=B_LO,`>`=B_LO]);
end module;
