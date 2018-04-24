#If X ~ Pareto(λ, 1) then log(X) ~ Exp(λ).

# Proof:
PDF_pareto := (lambda, k, x) -> lambda * k ^ lambda / x ^ (lambda + 1);

PDF_exponential := (alpha, x) -> exp(-x/alpha)/alpha;

simplify(PDF_pareto(lambda, 1, exp(x))*diff(exp(x),x));

simplify(PDF_exponential(1/lambda, x));

