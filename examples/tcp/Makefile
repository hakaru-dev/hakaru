all: build

data:
	bash ./download-data.sh

run:
	sh run.sh

clean:
	rm naive_bayes_gibbs_simp.hk NaiveBayes.hs *.o *.hi *.core

distclean : clean
	rm 20news-19997.tar.gz

naive_bayes_gibbs_simp.hk: 
	simplify naive_bayes_gibbs.hk > naive_bayes_gibbs_simp.hk

NaiveBayes.hs: naive_bayes_gibbs_simp.hk
	compile naive_bayes_gibbs_simp.hk -o NaiveBayes.hs -M NaiveBayes

build: NaiveBayes.hs data
	ghc -O2 --make Scaffold -o NaiveBayes

# %.hs : %.hk
#       compile $<
# 
# %.core : %.hs
#       ghc -O2 -ddump-simpl -dverbose-core2core -dppr-cols200 $< nb_simp.o > $@
