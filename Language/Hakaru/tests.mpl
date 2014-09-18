# The inputs below are the results of 'tester tN' from Tests/Syntax.hs

# t1 = uniform 0 1 `bind` \x -> factor (unsafeProb x)
t1 := (x0->(x1->int((x1(x2)/(1-0)),x2=0..1))((x1->(x2->(x1*x2(Unit)))(x0)))):

# t2 = beta 1 1
t2 := (x0->(x1->int((x1(x2)/(1-0)),x2=0..1))((x1->(x2->(x3->((((x1^(1-1))*((1-x1)^(1-1)))/Beta(1,1))*x3(Unit)))((x3->(x4->x4(x1))(x2))))(x0)))):
# t3 = normal 0 10
t3 := (x0->(x1->int(x1(x2),x2=-infinity..infinity))((x1->(x2->(x3->(((1/(10*sqrt((2*Pi))))*exp((-(((x1-0)*(x1-0))/((2*10)*10)))))*x3(Unit)))((x3->(x4->x4(x1))(x2))))(x0)))):
# t4 = beta 1 1 `bind` \bias -> bern bias `bind` \coin -> dirac (pair bias coin)
t4 := (x0->(x1->(x2->int((x2(x3)/(1-0)),x3=0..1))
    ((x2->(x3->(x4->((((x2^(1-1))*((1-x2)^(1-1)))/Beta(1,1))*x4(Unit)))
    ((x4->(x5->x5(x2))(x3))))(x1))))
    ((x1->(x2->(x3->(x4->int((x4(x5)/(1-0)),x5=0..1))((x4->(x5->x5((x4<x1)))(x3))))
               ((x3->(x4->x4(Pair(x1, x3)))(x2))))(x0)))):
# t5 is "the same" as t1.
# t5 = factor (1/2) `bind_` dirac unit
t5 := (x0->(x1->((1/2)*x1(Unit)))((x1->(x2->x2(Unit))(x0)))):

t6 := (x0->x0(5));

t7 := (x0->(x1->int((x1(x2)/(1-0)),x2=0..1))
           ((x1->(x2->(x3->((x1+1)*x3(Unit)))
                      ((x3->(x4->x4((x1*x1)))(x2))))(x0))));

t8 := (x0->(x1->(x2->int(x2(x3),x3=-infinity..infinity))
                ((x2->(x3->(x4->
                  (((1/(10*sqrt((2*Pi))))*exp((-(((x2-0)*(x2-0))/((2*10)*10)))))*x4(Unit)))
                ((x4->(x5->x5(x2))(x3))))(x1))))
        ((x1->(x2->(x3->(x4->int(x4(x5),x5=-infinity..infinity))
                ((x4->(x5->(x6->
                   (((1/(20*sqrt((2*Pi))))*exp((-(((x4-5)*(x4-5))/((2*20)*20)))))*x6(Unit)))
                ((x6->(x7->x7(x4))(x5))))(x3))))
                  ((x3->(x4->x4(Pair(x1, x3)))(x2))))(x0))));

t9 := (x0->(x1->int(x1(x2),x2=-infinity..infinity))
           ((x1->(x2->
              (x3->(piecewise(piecewise((3<x1), (x1<7), false), (1/2), 0)*x3(Unit)))
              ((x3->(x4->x4(x1))(x2))))(x0))));

# for now, just read the code in.
read "SLO.mpl":

# for now, just print the results to the screen
r1 := SLO(t1);
r2 := SLO(t2);
r3 := SLO(t3);
r4 := SLO(t4);
r5 := SLO(t5);
r6 := SLO(t6);
r7 := SLO(t7);
r8 := SLO(t8);
r9 := SLO(t9);

# printlevel := 10;
SLO:-AST(r1);
SLO:-AST(r2);
SLO:-AST(r3);
SLO:-AST(r4);
SLO:-AST(r5);
SLO:-AST(r6);
SLO:-AST(r7);
SLO:-AST(r8);
SLO:-AST(r9);
