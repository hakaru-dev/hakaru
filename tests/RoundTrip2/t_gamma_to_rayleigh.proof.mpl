# Proof by PDF that X <~ rayleigh(1) == X^2 <~ gamma(1,2)

PDF_rayleigh := (a, x) -> 2*x*exp(-x^2/a)/a;

PDF_gamma := (k, t, x) -> x^(k-1)*exp(-x/t)/(GAMMA(k)*t^k);
simplify(PDF_gamma(1, 2, x));

PDF_transform := (x) -> PDF_rayleigh(2,sqrt(x))*diff(sqrt(x),x);
simplify(PDF_transform(x));

evalb(PDF_gamma(1, 2, x) = PDF_transform(x));