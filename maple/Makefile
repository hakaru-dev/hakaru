.SUFFIXES: .out .mpl

all: ppaml.mla NewSLOTests.out PlateT.out DisintT.out call-graph.pdf

ppaml.mla: update-archive.mpl BindingTools.mpl Hakaru.mpl KB.mpl Loop.mpl NewSLO.mpl
	maple -q $<

.mpl.out: ppaml.mla
	maple -q $< 2>&1 | tee $@ | grep -v " passed$$"

call-graph.svg: call-graph.dot
	dot -Tsvg $< > $@

call-graph.pdf: call-graph.dot
	dot -Tpdf $< > $@

call-graph.dot: call-graph NewSLO.mpl
	./$^ > $@
