# Program transformations in Hakaru

## Coalesce

Coalesce is an internal transformation that works on the untyped Hakaru AST. It
takes recursive `NAryOp` terms that have the same type and combines them into
a single term. For instance:

```
3.0 + 1.5 + 0.3
```
is parser as:

```
NaryOp Sum [3.0, NaryOp Sum [1.5, NaryOp Sum [0.3]]]
```
which when coalesced becomes:
```
NaryOp Sum [3.0,1.5,0.3]
```

## Optimizations

The Hakaru AST has a suite of standard compiler optimizations which have
a substantial effect on the runtime of the resulting program.
The current pipeline is described by the `optimizations` variable in
`Language.Hakaru.Syntax.Transforms`.
In order, the optimizations performed are:

1. A-normalization
2. Uniquification of variables (needed for let-floating)
3. Let-floating
4. Common subexpression elimination
5. Pruning of dead binders
6. Uniquification of variables (for the C backend)
7. Constant Propagation

Each pass is described in more detail below.

### A-normalization

Found in `Language.Hakaru.Syntax.ANF`

See **The Essence of Compiling with Continuations by Flannigan, Sabry, Duba, and
Felleisen**

A-normalization converts expressions into *administrative normal form* (ANF).
This ensures that all intermediate values are named and all arguments to
functions or primitive operations are either literals or variables.
ANF is a common program representation for functional language compilers which
can simplify some compiler passes and make others more effective.
As an example, consider

```
(add1 (let ([x (f y)]) 5))
```

This expression in ANF looks like the following

```
(let ([x (f y)]) (add1 5))
```

which opens up the opportunity for constant folding to eliminate the `(add1 5)`
expression.
This pass exists mostly to simplify the implementation of CSE, but is useful for
other passes as well.

### Uniquification

Found in `Language.Hakaru.Syntax.Uniquify`

Ensures all variables in the program have unique variable identifiers.
This is not strictly necessary, but simplifies the implementation of other
passes, several of which rely on this property.

### Let-floating

Found in `Language.Hakaru.Syntax.Hoist`

See **Let-Floating: Moving Bindings to Give Faster Programs (1996)
by Simon Peyton Jones , Will Partain , André Santos**

Let-floating alters the bindings structure of the program in order to improve
performance.
Typically, this entails moving definitions into or out of lambda expressions.
When a lambda expression encodes a loop, this effectively accomplishes
loop invariant code motion.
This pass only moves definitions upward in the AST.
For the most part, we are only interested in looping constructs like `summate` and
`product`, and moving `summate` expressions out of other `summate` or `product`
expressions when they do not depend on the index.
This can radically alter the asymptotics of the resulting program, as nested
loops are converted into sequentially executed loops.

The only assumption this pass makes about the input AST is that all variable
identifiers are unique.
This is to handle the case where two branches of a match statement introduce the
same variable.
If both binders are hoisted out of the match statement, they one binding will
shadow the other.

This pass, as implemented, unconditionally floats expression to where their data
dependencies are fulfilled.
This is not safe in a general purpose language, and we may need to layer some
heuristics on top of this pass to make it less aggressive if we end up
introducing performance regressions.

### Common Subexpression Elimination

Found in `Language.Hakaru.Syntax.CSE`

Common subexpression elimination eliminates redundant computation by reusing
results for equivalent expressions.
The current implementation of this pass relies on the program being in ANF.

ANF simplifies the implementation of CSE greatly by ensuring all expressions are
named and that if two expressions may be shared, one of them is let-bound so
that it dominates the other.
In short, ANF simplifies the program to a simple top-down traversal of the AST.
Consider the example

```
(+ (add1 z) (add1 z))
```

Eliminating the common expression `(add1 z)` requires us to traverse the
expression in evaluation order, track expression which have already been
evaluated, recognize when an expression is duplicated, and introduce it
with a new name that dominates all use sites of that expression.
However, an expression in ANF allows us to perform CSE simply by keeping track
of let-bound expressions and propagating those expressions downward into the
AST.
Consider the example in ANF

```
(let ([t1 (add1 z)])
  (let ([t2 (add1 z)])
    (+ t1 t2)))
```

To remove the common subexpression, we simply have to note that the `(add1 z)`
bound to `t2` is equivalent to the expression bound to `t1` and replace it with
the variable `t1`.

```
(let ([t1 (add1 z)])
  (let ([t2 t1])
    (+ t1 t2)))
```

Trivial bindings can then be eliminated, if desired, giving

```
(let ([t1 (add1 z)])
  (+ t1 t1)))
```

A major goal of CSE is to cleanup any work which is duplicated by the
let-floating pass.

### Pruning

Found in `Language.Hakaru.Syntax.Prune`

This is essentially a limited form of dead code elimination.
If an expression is bound to a variable which is never referenced, then that
expression need never be executed, as the code language has no side effects.
This pass serves to clean up some of the junk introduced by other passes.

Cases which are handled

1. `(let ([x e1]) e2) => e2 if x not in fv(e2)`
2. `(let ([x e1]) x)  => e1`

### Constant Propagation

Found in `Language.Hakaru.Evalutation.ConstantPropagation`

Performs simple constant propagation and constant folding.
The current implementation does not do that much work, mostly just evaluating
primitive operations when their arguments are constant.

## Unused Passes

### Loop Peeling

Found in `Language.Hakaru.Syntax.Unroll`

Loop peeling was an initial attempt at performing loop invariant code motion by
leveraging CSE to do most of the heavy lifting.
Peeling is a common strategy to make other optimization passes "loop-aware".
The idea is to peel off one iteration of a loop and then apply the existing
suite of optimizations.
Consider the following `summate` whose body  `e` is some loop-invariant
computation.

```
(summate lo hi (λ x -> e))
```

After peeling we obtain

```
(if (= lo hi)
    0
    (let ([x lo])
      (let ([t1 e])
        (let ([t2 (summate (+ lo 1) hi (λ x -> e))])
          (+ t1 t2)))))
```

After applying CSE, the loop invariant body is simply reused on each iteration

```
(if (= lo hi)
    0
    (let ([x lo])
      (let ([t1 e])
        (let ([t2 (summate (+ lo 1) hi (λ x -> t1))])
          (+ t1 t2)))))
```

ANF ensures that all subexpression in the `e` bound to `t1` are shareable with
the copy of `e` used in the body of the `summate`, allowing us to hoist out
subexpressions of `e` and not just the entire `summate` body.

This pass is currently disabled in favor of the let-floating pass, which does
a better job without causing an exponential blow up in code size.
Some of Hakaru's looping constructs, such as `array`, cannot be peeled, so we
cannot move loop invariant operations out of `array` statements.

