UpdateArchive := proc(lib_::string:="ppaml.mla")
  local libdir, drs, do_read, do_save, prev, fn, lib := lib_;
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
  if not FileTools:-Exists(lib) then
    LibraryTools:-Create(lib):
  else
    try
      FileTools:-Remove(lib)
    catch:
      WARNING("Hakaru archive %1 already exists, but failed to delete it... "
              "overwriting old archive.", lib):
    end try;
  end if:
  currentdir(libdir):

  do_read := proc(x,$) read(cat(libdir,drs,x,".mpl")); NULL; end proc;
  do_save := proc(x,$) LibraryTools:-Save(x,lib); NULL; end proc;

  map(do_read,
   ["BindingTools", "Hakaru", "KB", "Partition", "Loop"
   ,"Domain", "NewSLO", "Summary"]);

  prev := kernelopts(opaquemodules=false):
  unprotect(Hakaru:-UpdateArchive);
  Hakaru:-UpdateArchive := copy(procname);
  protect(Hakaru:-UpdateArchive);

  map(do_save,
   [`gensym`, 'BindingTools', `depends/lam`, `depends/Branch`, `depends/Bind`, `depends/ary`, `depends/Plate`, `eval/lam`, `eval/Branch`, `eval/Bind`, `eval/ary`, `eval/Plate`, 'Hakaru', 'KB', `depends/forall`, `depends/Ints`, `depends/Sums`, `depends/ints`, `depends/sums`, `eval/forall`, `eval/Ints`, `eval/Sums`, `eval/ints`, `eval/sums`, `eval/Int`, `eval/Sum`, `eval/Product`, `eval/int`, `eval/sum`, `eval/product`, 'Loop', `depends/Integrand`, `depends/LO`, `eval/Integrand`, `eval/LO`, 'Domain', 'NewSLO', 'Partition', `depends/Bucket`, `depends/Index`, `eval/Bucket`, `eval/Index`, 'Summary']);

  Domain:-Improve:-ModuleLoad():
  kernelopts(opaquemodules=prev):
  do_save('Domain:-Improve');
end proc:

UpdateArchive();
