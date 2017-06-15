interface(screenwidth=9999):
if not (NewSLO :: `module`) then
  WARNING("loading NewSLO failed");
  `quit`(3);
end if;

with(Hakaru):
with(NewSLO):

#####################################################################
#
# Dirichlet conjugacy tests
#
#####################################################################

(dice_index, dice_index_t) := Concrete("examples/dice_index.hk"):
dice_index := value(eval(dice_index)):

# BUG: naming the var `lda' with a lowercase causes "Error: recursive
# assignment", but *not* inside Concrete (in the evaluation of the resulting
# expression!). `lda' doesn't seem to be a special name.
(LDA, LDA_t) := Concrete("examples/lda2.hk"):
LDA := value(eval(LDA)):

(gmm_gibbs, gmm_gibbs_t) := Concrete("examples/gmm_gibbs.hk"):
gmm_gibbs := value(eval(gmm_gibbs)):

(naive_bayes_gibbs, naive_bayes_gibbs_t) := Concrete("examples/naive_bayes_gibbs.hk"):
naive_bayes_gibbs := value(eval(naive_bayes_gibbs)):

#####################################################################
TestEfficient( dice_index, dice_index_t, KB:-empty, label="dice index" ):
TestEfficient( LDA, LDA_t, KB:-empty, label="LDA" ):
TestEfficient( gmm_gibbs, gmm_gibbs_t, KB:-empty, label="gmm gibbs" ):
TestEfficient( naive_bayes_gibbs, naive_bayes_gibbs_t, KB:-empty, label="naive bayes gibbs" ):

