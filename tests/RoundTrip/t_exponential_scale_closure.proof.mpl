#If X ~ Exp(λ) then kX ~ Exp(λ/k).

#Equivalent: If X ~ Exp(α) then kX ~ Exp(kα)

#Proof:
PDF_exponential := (alpha, x) -> exp(-x/alpha)/alpha;

PDF_kX := (alpha, x, k) -> PDF_exponential(alpha, x/k)/k;
simplify(PDF_kX(alpha, x, k));

PDF_exp_scaled := (alpha, x, k) -> PDF_exponential(k*alpha, x);
simplify(PDF_exp_scaled(alpha, x, k));

evalb(PDF_kX(alpha, x, k) = PDF_exp_scaled(alpha, x, k));
