UpdateArchive := proc(lib_::string:="ppaml.mla")
  local libdir, drs, olddir, do_read, do_save, prev, fn, getVer, lib := lib_;
  drs := kernelopts(dirsep);

  libdir := eval(`if`(nargs=2,'args[2]','currentdir()'));
  if nargs=2 then
    libdir := args[2];
  else
    libdir := LibraryTools:-FindLibrary(Hakaru);
    if libdir <> NULL then
      libdir := FileTools:-ParentDirectory(libdir);
    else
      libdir := currentdir();
    end if;
  end if;
  olddir := currentdir(libdir):

  if not FileTools:-Exists(lib) then
    LibraryTools:-Create(lib):
  else
    try
      FileTools:-Remove(lib)
    catch:
      map(curry(march,'delete',lib)@curry(op,1),march('list', lib));
      if nops( march('list', lib) ) <> 0 then
        WARNING("Failed to delete all contents of %1",lib);
      end if;
    end try;
  end if:

  do_read := proc(x,$) read(cat(".",drs,x,".mpl")); NULL; end proc;
  do_save := proc(x,$) LibraryTools:-Save(x,lib); NULL; end proc;

  map(do_read,
   ["BindingTools", "Utilities", "Hakaru", "KB", "Partition", "Loop"
   ,"Domain", "NewSLO", "Summary"]);

  prev := kernelopts(opaquemodules=false):
  unprotect(Hakaru:-UpdateArchive);
  Hakaru:-UpdateArchive := copy(procname);
  protect(Hakaru:-UpdateArchive);

  # Gets the version from git
  # May be a way to retrieve all this information in one go?
  getVer := proc()
    local v, ns, vs := NULL;
    currentdir(olddir);
    v := ssystem(`git show -s --format="[\\"%h\\", \\"%ad\\"]"`);
    if v::[0,string] then
      vs := vs,op(parse(op(2,v)));
    else vs := vs,{}$3;
    end if;

    # Commit name might contain " or `
    v := ssystem(`git show -s --format=%s`);
    if v::[0,string] then
      vs := vs,op(2,v);
    else vs := vs,{}$3;
    end if;

    v := ssystem(`git rev-parse --abbrev-ref HEAD`);
    if v::[0,string] then
      vs := vs,op(2,v);
    else vs := vs,{};
    end if;

    v := ssystem(`git diff-index HEAD`);
    if v::[0,string] then
      vs := vs,`if`(length(op(2,v))=0,"clean","dirty");
    else vs := vs,{};
    end if;

    currentdir(libdir);
    ns := [`commit hash`,`date`,`commit title`,`branch`,`status`];
    zip(`=`,ns,map(StringTools:-Chomp,[vs]));
  end proc;
  unprotect(Hakaru:-Version);
  Hakaru:-Version := getVer();
  protect(Hakaru:-Version);

  map(do_save,
   ['Utilities', `gensym`, 'BindingTools', `depends/lam`, `depends/Branch`, `depends/Bind`, `depends/ary`, `depends/Plate`, `eval/lam`, `eval/Branch`, `eval/Bind`, `eval/ary`, `eval/Plate`, 'Hakaru', 'KB', `depends/forall`, `depends/Ints`, `depends/Sums`, `depends/ints`, `depends/sums`, `eval/forall`, `eval/Ints`, `eval/Sums`, `eval/ints`, `eval/sums`, `eval/Int`, `eval/Sum`, `eval/Product`, `eval/int`, `eval/sum`, `eval/product`, 'Loop', `depends/Integrand`, `depends/LO`, `eval/Integrand`, `eval/LO`, 'Domain_Type', 'Domain', 'NewSLO', 'Partition', `depends/Bucket`, `depends/Index`, `eval/Bucket`, `eval/Index`, 'Summary', 'Bind', seq(parse(cat("`print/",q,"`")),q=[ints,sums,Ints,Sums]) ]);

  Domain:-Improve:-ModuleLoad():
  kernelopts(opaquemodules=prev):
  do_save('Domain:-Improve'):
  currentdir(olddir);
  NULL;
end proc:

UpdateArchive():
