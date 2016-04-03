all: ppaml.mla test call-graph.svg

ppaml.mla: update-archive.mpl NewSLO.mpl
	maple -q $<

test: ppaml.mla NewSLOTests.mpl PlateT.mpl DisintT.mpl
	for f in $(filter %.mpl,$^); do maple -q "$$f" | grep -v " passed$$"; done 2>&1 | tee $@

call-graph.svg: call-graph NewSLO.mpl
	./$^ | dot -Tsvg > $@
