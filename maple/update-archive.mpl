
lib := "ppaml.mla":
FileTools:-Remove(lib):
LibraryTools:-Create(lib):

read("./Haskell.mpl"):
LibraryTools:-Save(Haskell, lib):

read("./SLO.mpl"):
LibraryTools:-Save(SLO, lib):
#LibraryTools:-Save(unsafeProb, lib):
#LibraryTools:-Save(`simplify/unsafeProb`, lib):
LibraryTools:-Save(`evalapply/if_`, lib):
LibraryTools:-Save('`type/Context`', lib):
LibraryTools:-Save('if_', lib):
LibraryTools:-Save(`index/TopProp`, lib):
