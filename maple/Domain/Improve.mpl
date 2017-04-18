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
    export ModuleLoad := proc($) LoadSimplifiers() end proc;#ModuleLoad

    local unknown_Simplifiers := {};
    local LoadSimplifiers := proc($)
      local lib_path, drs, improve_path, simpls_paths, simpl_path, names0, names1, new_names, nm;
      unprotect(Simplifiers);
      lib_path := FileTools:-ParentDirectory(LibraryTools:-FindLibrary(Hakaru));
      ASSERT(lib_path<>NULL);
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
            Simplifiers[nm:-SimplName] := nm;
          elif not nm in unknown_Simplifiers then
            unknown_Simplifiers := { nm, op(unknown_Simplifiers) };
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
      local res, sh1; sh1 := simp0(bnd, sh);
      if not sh1 :: DomNoSol then
          simp1(bnd, sh1);
      else
          combine_errs( sh1, simp1(bnd, sh) );
      end if;
    end proc;
end module;
