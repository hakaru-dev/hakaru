# If X ~ Exponential(λ) then k*exp(X) ~ Pareto(λ, k)

# Proof:

PDF_exponential := (alpha, x) -> exp(-x/alpha)/alpha;

PDF_pareto := (lambda, k, x) -> lambda * k ^ lambda / x ^ (lambda + 1);


simplify(PDF_exponential(1/lambda, log(x/k))*diff(log(x/k), x));

simplify(PDF_pareto(lambda, k, x));