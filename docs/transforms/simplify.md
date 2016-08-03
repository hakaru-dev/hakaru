# Simplify transformation

The simplify transformation provides a way to automaticaly improve our
programs. Simplify works by turning our programs into their expectation
representation and sending to Maple to be algebraically-simplified.

For example, the following represents a program from values of type
`prob` to a measure of real numbers.

````nohighlight
fn a prob:
  x <~ normal(a,1)
  y <~ normal(x,1)
  z <~ normal(y,1)
  return z
````

And it will simplify to the following equivalent program.

````nohighlight
fn a prob: normal(prob2real(a), sqrt(3))
````
