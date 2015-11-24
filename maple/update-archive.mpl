
lib := "ppaml.mla":
if FileTools:-Exists(lib) then FileTools:-Remove(lib) end if:
LibraryTools:-Create(lib):

read("./Haskell.mpl"):
LibraryTools:-Save(Haskell, lib):

read("./SLO.mpl"):
LibraryTools:-Save(SLO, lib):
LibraryTools:-Save(`evalapply/if_`, lib):
LibraryTools:-Save(`evalapply/Pair`, lib):
# LibraryTools:-Save(`evalapply/piecewise`, lib):
LibraryTools:-Save(`if_`, lib):
LibraryTools:-Save(`fst`, lib):
LibraryTools:-Save(`snd`, lib):
LibraryTools:-Save(`unpair`, lib):
LibraryTools:-Save(`uneither`, lib):
LibraryTools:-Save(`WeightedM`, lib):
LibraryTools:-Save(`Superpose`, lib):
LibraryTools:-Save(`Bind`, lib):
LibraryTools:-Save(`If`, lib):
LibraryTools:-Save('`type/Context`', lib):
#LibraryTools:-Save(`index/TopProp`, lib):
#LibraryTools:-Save(`gensym`, lib): # use the one from NewSLO.mpl
LibraryTools:-Save(`MVECTOR`, lib):
LibraryTools:-Save(`Reduce`, lib):
LibraryTools:-Save(`vindex`, lib):
LibraryTools:-Save(`vsize`, lib):

read("./NewSLO.mpl"):
LibraryTools:-Save(`depends/Integrand`, lib):
LibraryTools:-Save(`depends/LO`, lib):
LibraryTools:-Save(`depends/lam`, lib):
LibraryTools:-Save(`depends/Bind`, lib):
LibraryTools:-Save(`depends/ary`, lib):
LibraryTools:-Save(generic_evalat, lib):
LibraryTools:-Save(`eval/Integrand`, lib):
LibraryTools:-Save(`eval/LO`, lib):
LibraryTools:-Save(`eval/lam`, lib):
LibraryTools:-Save(`eval/Bind`, lib):
LibraryTools:-Save(`eval/ary`, lib):
LibraryTools:-Save(`gensym`, lib):
LibraryTools:-Save(NewSLO, lib):
