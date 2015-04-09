
lib := "ppaml.mla":
if FileTools:-Exists(lib) then FileTools:-Remove(lib) end if:
LibraryTools:-Create(lib):

read("./Haskell.mpl"):
LibraryTools:-Save(Haskell, lib):

read("./SLO.mpl"):
LibraryTools:-Save(SLO, lib):
LibraryTools:-Save(`evalapply/if_`, lib):
LibraryTools:-Save(`evalapply/Pair`, lib):
LibraryTools:-Save(`if_`, lib):
LibraryTools:-Save(`fst`, lib):
LibraryTools:-Save(`snd`, lib):
LibraryTools:-Save(`WeightedM`, lib):
LibraryTools:-Save(`Superpose`, lib):
LibraryTools:-Save(`Bind`, lib):
LibraryTools:-Save(`If`, lib):
LibraryTools:-Save('`type/Context`', lib):
#LibraryTools:-Save(`index/TopProp`, lib):
LibraryTools:-Save(`gensym`, lib):
LibraryTools:-Save(`MVECTOR`, lib):
LibraryTools:-Save(`Reduce`, lib):
LibraryTools:-Save(`vindex`, lib):
