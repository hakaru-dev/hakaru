# If X ~ Exp(λ) and Y ~ Exp(ν) 
# 	then min(X, Y) ~ Exp(λ + ν).

# Rewrite for scale: 
#	λ = 1/α and ν = 1/β 
#	λ + ν = (β + α)/αβ
#	If X ~ Exp(α) and Y ~ Exp(β) 
# 	then min(X, Y) ~ Exp(αβ/(β + α)).

# Proof:

PDF_exponential := (alpha, x) -> exp(-x/alpha)/alpha;

PDF_sum_rates := (alpha, beta, x) -> PDF_exponential(alpha*beta/(alpha+beta),x);

simplify(PDF_sum_rates(alpha, beta, x));

PDF_sum_equiv := (alpha, beta, x) -> min(PDF_exponential(alpha,x), PDF_exponential(beta,x));

simplify(PDF_sum_equiv(alpha, beta, x));

evalb(PDF_sum_rates(alpha, beta, x) = PDF_sum_equiv(alpha, beta, x));