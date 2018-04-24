# Proof by PDF that X <~ rayleigh(1) == X^2 <~ weibull(1,1)

PDF_rayleigh := (a, x) -> 2*x*exp(-x^2/a)/a;

PDF_transform := (x) -> PDF_rayleigh(1,sqrt(x))*diff(sqrt(x),x);
simplify(PDF_transform(x));

PDF_weibull := (k, t, x) -> k/t*x^(k-1)*exp(-1*(1/t)*x^k);
simplify(PDF_weibull(1, 1, x));

evalb(PDF_weibull(1, 1, x) = PDF_transform(x));