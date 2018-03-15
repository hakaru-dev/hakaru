# Proof by PDF that 
# If R ~ rayleigh(2) then R^2 ~ stdChiSq(2)


PDF_rayleigh := (a, x) -> 2*x*exp(-x^2/a)/a;

# Transform on random variable is f(R)=R^2. Inverse function is g(x) = sqrt(x)
PDF_transform := (x) -> PDF_rayleigh(2,sqrt(x))*diff(sqrt(x),x);

PDF_chisq := (n, x) -> x^(1/2*n-1)*exp(-1/2*x)/(2^(1/2*n))/GAMMA(1/2*n); 
simplify(PDF_chisq(2,x));


evalb(PDF_chisq(2,x) = PDF_transform(x));
