# Let and Bind

In Hakaru, we can give names for expressions to our programs with `=`,
which we call _Let_. This gives us the ability to share computation
that might be needed in the program.

````nohighlight
x = 2
x + 3
````

We can use `=` to give a name to any expression in our language. The
name you assign is in scope for the rest of the body it was defined in.

## Bind

Hakaru also has the operator `<~`. This operator, which call _Bind_
can only be used with expressions that denote probability distributions.
Bind allows us to talk about draws from a distribution using a name for
any particular value that could have come from that distribution.

````nohighlight
# Bad
x <~ 2 + 3
x
````

````nohighlight
# Good
x <~ normal(0,1)
return x
```

Because Bind is about draws from a distribution, the rest of the body
must also denote a probability distribution.

````nohighlight
# Bad
x <~ normal(0,1)
x
````

````nohighlight
# Good
x <~ normal(0,1)
return x
```

To help distinguish Let and Bind. Here is a probabilistic program, where we
let _f_ be equal to the normal distribution, and take draws from _f_.

````nohighlight
f = normal(0,1)
x <~ f
return x*x
````

