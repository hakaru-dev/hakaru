# Proof by PDF that X <~ rayleigh(1/sqrt(2*lambda)) == X^2 <~ exponential(lambda)

PDF_rayleigh := (a, x) -> 2*x*exp(-x^2/a)/a;

PDF_transform := (x) -> PDF_rayleigh(1,sqrt(x))*diff(sqrt(x),x);
simplify(PDF_transform(x));

PDF_exponential := (l, x) -> l*exp(-l*x);
simplify(PDF_exponential(1, x));

evalb(PDF_exponential(1, x) = PDF_transform(x));