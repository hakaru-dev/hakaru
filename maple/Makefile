all: ppaml.mla test call-graph.pdf

ppaml.mla: update-archive.mpl BindingTools.mpl Hakaru.mpl KB.mpl Loop.mpl NewSLO.mpl
	maple -q $<

test: ppaml.mla NewSLOTests.mpl PlateT.mpl DisintT.mpl
	parallel -j 3 maple -q -- $(filter %.mpl,$^) 2>&1 | tee $@ | grep -v " passed$$"

call-graph.svg: call-graph.dot
	dot -Tsvg $< > $@

call-graph.pdf: call-graph.dot
	dot -Tpdf $< > $@

call-graph.dot: call-graph NewSLO.mpl
	./$^ > $@
