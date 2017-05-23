# Loops

We also express loops that compute sums (`summate`) and products (`product`).
The syntax of these loops begins by declaring an **inclusive** lower bound and
an **exclusive** upper bound.  For example, the factorial of `n` is not
`product i from 1 to n: i` but rather `product i from 1 to n+1: i`.
This convention takes some getting used to but it makes it easy to deal
with arrays.  For example, if `a` is an array of numbers then their sum is
`summate i from 0 to size(a): a[i]`.

