# If X ~ Exp(α) then e^−X ~ Beta(1/α, 1).

# Proof:

PDF_exponential := (alpha, x) -> exp(-x/alpha)/alpha;

PDF_beta := (beta, gamma, x) -> GAMMA(beta+gamma) * x^(beta-1) * (x - 1)^(gamma-1) / GAMMA(beta) / GAMMA(gamma);

simplify(PDF_exponential(1/lambda, -log(x))*diff(log(x), x));

simplify(PDF_beta(lambda, 1, x));