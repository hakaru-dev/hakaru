
lib := "ppaml.mla":
if FileTools:-Exists(lib) then FileTools:-Remove(lib) end if:
LibraryTools:-Create(lib):

read("./Haskell.mpl"):
LibraryTools:-Save(Haskell, lib):

read("./SLO.mpl"):
LibraryTools:-Save(SLO, lib):
LibraryTools:-Save(`evalapply/if_`, lib):
LibraryTools:-Save('`type/Context`', lib):
LibraryTools:-Save('if_', lib): # hopefully can remove this later
LibraryTools:-Save(`index/TopProp`, lib):
