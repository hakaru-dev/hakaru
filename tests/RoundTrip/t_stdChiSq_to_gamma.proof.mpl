# Proof by PDF that 
#	if X <~ standardChiSq(n) then cX <~ gamma(k = n/2, t = 2*c)		

PDF_chisq := (n, x) -> x^(n/2-1)*exp(-x/2)/(2^(n/2)*GAMMA(n/2)); 
PDF_cX := (n, c, x) -> PDF_chisq(n, x/c)/c;
PDF_sub := (k, t, x) -> PDF_cX(2*k, t/2, x);
simplify(PDF_sub(k, t, x));


PDF_gamma := (k, t, x) -> x^(k-1)*exp(-x/t)/(GAMMA(k)*t^k);
simplify(PDF_gamma(k, t, x));

# NOTE: Doesn't evaluate true, but inspection of forms given by
#		the 2 calls to simplify prove it so
evalb(PDF_sub(k, t, x) = PDF_gamma(k, t, x));
