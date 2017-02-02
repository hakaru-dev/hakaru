all: ppaml.mla NewSLOTests.out PlateT.out SummaryT.out # call-graph.pdf

ppaml.mla: update-archive.mpl BindingTools.mpl Hakaru.mpl KB.mpl Loop.mpl NewSLO.mpl Summary.mpl
	maple -q $<

%.out: %.mpl ppaml.mla
	maple -q $< 2>&1 | tee $@ | (grep -v " passed$$" || true)

call-graph.svg: call-graph.dot
	dot -Tsvg $< > $@

call-graph.pdf: call-graph.dot
	dot -Tpdf $< > $@

call-graph.dot: call-graph NewSLO.mpl
	./$^ > $@
