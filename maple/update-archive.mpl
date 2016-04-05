
lib := "ppaml.mla":
if FileTools:-Exists(lib) then FileTools:-Remove(lib) end if:
LibraryTools:-Create(lib):

read("./BindingTools.mpl"):
read("./Hakaru.mpl"):
read("./KB.mpl"):
read("./NewSLO.mpl"):
LibraryTools:-Save(`gensym`, lib):
LibraryTools:-Save('BindingTools', lib):
LibraryTools:-Save(`depends/lam`, lib):
LibraryTools:-Save(`depends/Branch`, lib):
LibraryTools:-Save(`depends/Bind`, lib):
LibraryTools:-Save(`depends/ary`, lib):
LibraryTools:-Save(`eval/lam`, lib):
LibraryTools:-Save(`eval/Branch`, lib):
LibraryTools:-Save(`eval/Bind`, lib):
LibraryTools:-Save(`eval/ary`, lib):
LibraryTools:-Save('Hakaru', lib):
LibraryTools:-Save('KB', lib):
LibraryTools:-Save(`depends/Integrand`, lib):
LibraryTools:-Save(`depends/LO`, lib):
LibraryTools:-Save(`depends/forall`, lib):
LibraryTools:-Save(`depends/Ints`, lib):
LibraryTools:-Save(`depends/Sums`, lib):
LibraryTools:-Save(`depends/ints`, lib):
LibraryTools:-Save(`depends/sums`, lib):
LibraryTools:-Save(`eval/Integrand`, lib):
LibraryTools:-Save(`eval/LO`, lib):
LibraryTools:-Save(`eval/forall`, lib):
LibraryTools:-Save(`eval/Ints`, lib):
LibraryTools:-Save(`eval/Sums`, lib):
LibraryTools:-Save(`eval/ints`, lib):
LibraryTools:-Save(`eval/sums`, lib):
LibraryTools:-Save(`eval/Int`, lib):
LibraryTools:-Save(`eval/Sum`, lib):
LibraryTools:-Save(`eval/int`, lib):
LibraryTools:-Save(`eval/sum`, lib):
LibraryTools:-Save('NewSLO', lib):
