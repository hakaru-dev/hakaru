all: ppaml.mla NewSLOTests.out PlateT.out SummaryT.out PlateT2.out # call-graph.pdf

disint: ppaml.mla DisintT.out 

ppaml.mla: update-archive.mpl BindingTools.mpl Hakaru.mpl KB.mpl Partition.mpl Loop.mpl Summary.mpl \
    Domain.mpl \
    Domain/Has.mpl \
    Domain/Bound.mpl \
    Domain/Shape.mpl \
    Domain/Types.mpl \
    Domain/Extract.mpl \
    Domain/Apply.mpl \
    Domain/Improve.mpl \
    Domain/Improve/LMS.mpl \
    Domain/Improve/redundant_DIntos.mpl \
    Domain/Improve/constraints_about_vars.mpl \
    Domain/Improve/singular_pts.mpl \
    Domain/Improve/single_case_Partition.mpl \
    NewSLO.mpl \
    NewSLO/Interface.mpl \
    NewSLO/To.mpl \
    NewSLO/From.mpl \
    NewSLO/Banish.mpl \
    NewSLO/Improve.mpl \
    NewSLO/Disint.mpl \
    NewSLO/Reparam.mpl \
    NewSLO/Factor.mpl \
    NewSLO/Beta.mpl \
    NewSLO/Piecewise.mpl
	maple -q $<

%.out: %.mpl ppaml.mla
	maple -q $< 2>&1 | tee $@ | (grep -v " passed$$" || true)

call-graph.svg: call-graph.dot
	dot -Tsvg $< > $@

call-graph.pdf: call-graph.dot
	dot -Tpdf $< > $@

call-graph.dot: call-graph NewSLO.mpl
	./$^ > $@
