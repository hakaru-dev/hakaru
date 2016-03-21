
lib := "ppaml.mla":
if FileTools:-Exists(lib) then FileTools:-Remove(lib) end if:
LibraryTools:-Create(lib):

read("./NewSLO.mpl"):
LibraryTools:-Save(`depends/Integrand`, lib):
LibraryTools:-Save(`depends/LO`, lib):
LibraryTools:-Save(`depends/lam`, lib):
LibraryTools:-Save(`depends/Branch`, lib):
LibraryTools:-Save(pattern_binds, lib):
LibraryTools:-Save(`depends/Bind`, lib):
LibraryTools:-Save(`depends/ary`, lib):
LibraryTools:-Save(generic_evalat, lib):
LibraryTools:-Save(`eval/Integrand`, lib):
LibraryTools:-Save(`eval/LO`, lib):
LibraryTools:-Save(`eval/lam`, lib):
LibraryTools:-Save(`eval/Branch`, lib):
LibraryTools:-Save(`eval/Bind`, lib):
LibraryTools:-Save(`eval/ary`, lib):
LibraryTools:-Save(`gensym`, lib):
LibraryTools:-Save('NewSLO', lib):
