all: ppaml.mla test call-graph.svg

ppaml.mla: update-archive.mpl BindingTools.mpl Hakaru.mpl KB.mpl Loop.mpl NewSLO.mpl
	maple -q $<

test: ppaml.mla NewSLOTests.mpl PlateT.mpl DisintT.mpl
	for f in $(filter %.mpl,$^); do maple -q "$$f" | grep -v " passed$$"; done 2>&1 | tee $@

call-graph.svg: call-graph.dot
	dot -Tsvg $< > $@

call-graph.dot: call-graph NewSLO.mpl
	./$^ > $@
