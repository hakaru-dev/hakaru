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

(gmm_gibbs, gmm_gibbs_t) := Concrete("examples/gmm_gibbs.hk"):
gmm_gibbs := value(eval(gmm_gibbs)):

(naive_bayes_gibbs, naive_bayes_gibbs_t) := Concrete("examples/naive_bayes_gibbs.hk"):
naive_bayes_gibbs := value(eval(naive_bayes_gibbs)):

#####################################################################
TestEfficient( dice_index, dice_index_t, KB:-empty, label="dice index" ):
TestEfficient( gmm_gibbs, gmm_gibbs_t, KB:-empty, label="gmm gibbs" ):
TestEfficient( naive_bayes_gibbs, naive_bayes_gibbs_t, KB:-empty, label="naive bayes gibbs" ):

