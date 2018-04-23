# Proof by PDF that X <~ standardChiSq(2) == Y <~ exponential(2)

PDF_chisq := (n, x) -> x^(1/2*n-1)*exp(-1/2*x)/(2^(1/2*n))/GAMMA(1/2*n); 
simplify(PDF_chisq(2,x));

PDF_exponential := (alpha, x) -> exp(-x/alpha)/alpha;
simplify(PDF_chisq(2,x));

evalb(PDF_chisq(2,x) = PDF_exponential(2,x));