# Hakaru-Maple #

Hakaru uses the computer algebra system Maple to aid in performing program
transformations. You can use this functionality of Hakaru if you have Maple
installed locally or can access Maple remotely. 

Maple can be accessed through the module `Language.Hakaru.Maple` or through the
Hakaru program `hk-maple`.

The `hk-maple` command invokes a Maple command on a Hakaru program. Given a
Hakaru program in concrete syntax and a Maple-Hakaru command, typecheck the
program invoke the Maple command on the program and its type pretty print, parse
and typecheck the program resulting from Maple. See the `--help` flag of
`hk-maple` for more information.

The currently available Maple-Hakaru commands (also called subcommands):

- Simplify 
- Disintegrate 
- Summarize 

Note: calls to Maple may take a very long time. To see if your program is taking
an appreciable amount of time to parse and typecheck, use the `--debug` flag.

## Subcommands 
### Simplify
Hakaru programs are interpreted by Maple as linear operators. In this
interpretation, many commonly understood (by Maple) and powerful tools for
simplification become available. The metric for simplification as understood by
this command is sampling efficiency. `Simplify` attempts to be as conservative
as possible in changing the given program. In particular, it should not change
terms unless an improvement with respect to sampling is performed; in this case,
arbitrary rearrangement may happen, even if an expression more similair to the
original could be produced.

`Simplify` is the default subcommand.

`Simplify` preserves the semantics of the given program up to normalization of
weights. If the stronger sense of equivalence is needed, the output of
`Simplify` can be passed to `normalize`. 

Historical note: the `Simplify` subcommand of `hk-maple` used to be known as a
seperate command named `simplify`. If you encounter `simplify someprog.hk
<options>` in this documentation, you may replace it by `hk-maple someprog.hk
<options>`.

### Disintegrate
The Maple disintegrator is an alternative implementation of the program
transformation described in [Disintegrate](/transforms/disintegrate). Semantically, the Maple
disintegrator and Haskell disintegrator implement the same transformation. In
particular, their outputs are not (often) identical, but have equivalent
sampling semantics. In practice, the ouputs may differ, since one may fail where
the other succeeds. 

If in doubt about which disintegrator to use, consider the following order:

1. `disintegrate x`
2. `disintegrate x | hk-maple -`
3. `hk-maple --command disintegrate x`
4. `hk-maple x | disintegrate -` 
5. etc...

All of the above programs should be equivalent as samplers. 

The disintegrator internally relies heavily on the `Simplify` command, so if the
given problem is an easy disintegration problem but a difficult simplification
problem, it is preferred to use the Haskell disintegrator followed by a call
to `Simplify`.

The chance that the Maple disintegrator produces a good program (or any program
at all) is proportional to the type of program it is given. In addition to
programs whose disintegration by Haskell is not efficient as a sampler, the
following programs are good candidates:

- programs which contain superpositions with complicated conditions
- programs which contain complicated rational polynomials 

The Maple disintegrator follows the same conventions as the Haskell
disintegrator.

Like `Simplify`, `Disintegrate` preserves the semantics of the given program only up to
normalization of weights.

### Summarize

Recall that our simplifier generates sampler code such as

````nohighlight
    fn as array(prob):
     fn z array(nat):
      fn t array(real):
       fn docUpdate nat:
        array zNew of size(as):
         ... (summate _b from 0 to size(as):
               ... (summate i from 0 to size(t):
                     if _b == (if i == docUpdate: zNew else: z[i]):
                      t[i]
                     else: 0) ...) ...
````

(that's from `examples/gmm_gibbs.hk`) and

````nohighlight
    fn topic_prior array(prob):
     fn word_prior array(prob):
      fn z array(nat):
       fn w array(nat):
        fn doc array(nat):
         fn docUpdate nat:
          ... (array zNew of size(topic_prior):
                product k from 0 to size(topic_prior):
                 product i from 0 to size(word_prior):
                  ... (summate j from 0 to size(w):
                        if doc[j] == docUpdate:
                         if k == zNew && i == w[j]: 1 else: 0
                        else: 0) ...) ...
````

(that's from `examples/naive_bayes_gibbs.hk`).  In this Hakaru code, `fn` makes
a function (whose argument type is explicit), and `array`, `summate`, and
`product` are looping constructs.  In particular, the innermost loops (`summate
i` and `summate j`) run many times due to the outer loops.  Furthermore, most
iterations of the innermost loops produce 0 and so don't contribute to the
result.  We can dramatically speed up this computation by precomputing a
"summary" outside the loops then replacing the innermost loop by an expression
that reuses the summary rather than looping.

To understand our current approach to this optimization, let's look at
a simpler example.  Suppose the innermost loop is merely

````nohighlight
    summate i from 0 to size(t):
     if _b == z[i]: t[i] else: 0
````

where the free variable `_b` denotes a natural number known to be bounded
by `size(as)`.  This loop denotes a real number that depends on `_b` and the
arrays `z` and `t`.  It turns out that we can rewrite it to the equivalent
expression

````nohighlight
    let summary = Bucket i from 0 to size(t):
                   Index _b = z[i] of size(as):
                    Add t[i]
    in summary[_b]
````

where the capitalized keywords are newly introduced to support this
optimization.  The variable `summary` is bound to an array whose size
is `size(as)` and whose element at each index `_b` is the sum of those `z[i]`
whose corresponding `t[i]` matches `_b`.  A good way to compute the summary
on sequential hardware is to initialize the summary to an all-zero
mutable array then

````nohighlight
    for i from 0 to size(t):
     summary[z[i]] += t[i]
````

A good way to compute the summary on parallel hardware is to divide the
data among the cores and summarize each portion in parallel then sum
the summaries elementwise.  The `Bucket` construct just introduced can
carry out either of these implementation strategies, by accordingly
interpreting the sub-language of map-reduce loops that `Index` and `Add` are
part of.  (Hence realizing this optimization from end to end in Hakaru
calls for adding the capitalized constructs to the Hakaru grammar and
extending the code generator(s) to handle them.)

Out of context, the let-expression above seems like a waste because
it computes a summary then uses only one element of it.  But the
right-hand-side of the summary-binding does not contain `_b` free, only
`t` and `z` and `as`, because the occurrences of `i` and `_b` are not uses but
bindings.  So, as an instance of loop-invariant code motion, we can move
the let-binding out of the loop over `_b`, and reuse the same summary
across all iterations over `_b`.  This way, we cut time complexity by a
factor of `size(as)` (the number of iterations over `_b`).

To pave the way for loop-invariant code motion, the summary should
depend on as few inner-scoped variables as possible.  This goal is
illustrated by the very first example above (from `gmm_gibbs.hk`).
Following the footsteps of the let-expression above, the `summate i`
expression is equivalent to

````nohighlight
    let summary = Bucket i from 0 to size(t):
                   Index _b = (if i == docUpdate: zNew else: z[i]) of size(as):
                    Add t[i]
    in summary[_b]
````

but this summary depends on zNew (and on docUpdate).  Our prototype
implementation of summarization finds a better rewrite:

````nohighlight
    let summary = Bucket i from 0 to size(t):
                   Split i == docUpdate:
                    Fanout(Add t[i], Nop)
                   else:
                    Index _b = z[i] of size(as):
                     Add t[i]
    in (if _b == zNew: fst(fst(summary)) else: 0) + snd(summary)[_b]
````

The type of this summary is not `array(real)` but `pair(pair(real,unit),
array(real))`.  The `array(real)` summarizes those `i` that are not equal
to `docUpdate`, whereas the `pair(real,unit)` turns out to be equal to
`(t[docUpdate],())`.  The check `_b == zNew` is postponed until the body
of the let, so the summary does not depend on zNew and can be moved out
of the `array zNew` loop, reducing time complexity by another factor of
`size(as)`.

Another way to understand this optimization is that we use loop exchange
to move the innermost loop out, then sum sparse arrays inside.

At least for the examples above, it turns out to be not very difficult
to automate rewriting a summate loop into a let-expression of the form

````nohighlight
    let summary = Bucket i...
    in ...summary...
````

whose body does not loop over `i`.  The automatic rewriting traverses the
body of the original loop, using a set of rewriting rules -- one for
each of `Index`, `Add`, `Split`, `Fanout`, and `Nop` -- that are easy to pretend
for expository purposes to have been derived by equational reasoning
from the monoidal denotational semantics of the newly introduced
constructs.  The trick is as usual to design the map-reduce sub-language
right.  The design notes below provide some details, couched somewhat in
Maple syntax.

The summarization optimization can be accessed with `hk-maple -c Summarize`,
which only calls `Summarize` on the input program, and with `summary`, which
calls `Summarize` as well as generating Haskell code corresponding to the
summarized program. The `summary` command has its own options regarding the
generation of Haskell code; see `summary --help` for details.

#### The language of mapreductions:

  A mapreduction mr denotes a monoid along with a map from indices (i) to
  monoid elements (such as e being t[i]).  There is an implicit index 'i',
  allowed to appear in e and cond.

````nohighlight
  mr ::= Fanout(mr,mr) | Index(n,o,e,mr) | Split(cond,mr,mr) | Nop() | Add(e)
````

- `Nop()` denotes the trivial monoid along with the constant map.
  
- `Add(e)` denotes the monoid of numbers under addition,
    along with the map i->e.
    
- `Fanout(mr1,mr2)` and `Split(cond,mr1,mr2)` both denote the product monoid of
    the monoids denoted by `mr1` and by `mr2`.  But if the maps denoted by
    `mr1` and `mr2` are `map1` and `map2` then `Fanout(mr1,mr2)` denotes the map
    `i->[map1(i),map2(i)]` whereas `Split(cond,mr1,mr2)` denotes the map
    `i->piecewise(cond,[map1(i),identity],[identity,map2(i)])`.
    
- `Index(n,o,e,mr(o))` denotes the product monoid of the monoids denoted by
    `mr(0)..mr(n-1)`, along with a map that returns a tuple that is
    all identity except at `o = e`.

Run-time helpers:


````nohighlight
  Bucket(mr, i=rng) =
    summary := Init(mr);
    for iv=rng do Accum(i, iv, mr, summary) end do;
    return summary
````

````nohighlight
  Init(Fanout(mr1, mr2))      = [Init(mr1), Init(mr2)]
  Init(Index(n, o, e, mr))    = [seq(Init(mr), o=0..n-1)]
  Init(Split(cond, mr1, mr2)) = [Init(mr1), Init(mr2)]
  Init(Nop())                 = []
  Init(Add(e))                = 0
````

````nohighlight
  Accum(i, iv, Fanout(mr1, mr2), summary) =
    Accum(i, iv, mr1, summary[1]);
    Accum(i, iv, mr2, summary[2]);
  Accum(i, iv, Index(n, o, e, mr), summary) =
    ov := eval(e, i=iv);
    if o::nonnegint and o<n then Accum(i, iv, mr, summary[ov+1]) end if;
  Accum(i, iv, Split(cond, mr1, mr2), summary) =
    if eval(cond, i=iv) then Accum(i, iv, mr1, summary[1])
                        else Accum(i, iv, mr2, summary[2]) end if;
  Accum(i, iv, Nop(), summary) = ;
  Accum(i, iv, Add(e), summary) = summary += eval(e, i=iv);
````

Specification:

````nohighlight
  If [mr, f] = summarize(e, kb, i)
  then f(Bucket(mr, i=rng)) = sum(e, i=rng)
  and we try to make mr depend on as little as possible
````

Implementation:


````nohighlight
  summarize(C[piecewise(cond,a,b)], kb, i) =
    [Fanout(mr1, mr2),
     summary -> piecewise(cond, f1(summary[1]), f2(summary[2]))]
    where [mr1, f1] = summarize(C[a], kb, i)
          [mr2, f2] = summarize(C[b], kb, i)
    if not depends(cond, i)
````

  Choose between the two rules below by outermosting the variables in
    `indets(e,name) minus {i}`  versus  `indets(cond,name) minus {i}`

````nohighlight
  summarize(piecewise(o=e,a,0), kb, i) =
    [Index(n, o, e, mr),
     summary -> piecewise(o::nonnegint and o<n, f(summary[o+1]), 0)]
    where [mr, f] = summarize(a, kb, i)
    if not depends(o, i) and kb entails o::nonnegint and o<n

  summarize(C[piecewise(cond,a,b)], kb, i) =
    [Split(cond, mr1, mr2),
     summary -> f1(summary[1]) + f2(summary[2])]
    where [mr1, f1] = summarize(C[a], kb, i)
          [mr2, f2] = summarize(C[b], kb, i)

  summarize(0, kb, i) = [Nop(), summary -> 0]

  summarize(e, kb, i) = [Add(e), summary -> summary]
````

## Examples ##
### Simplify ###

This program takes in a value of type `prob` and returns a measure of type `real`:

````nohighlight
fn a prob:
  x <~ normal(a,1)
  y <~ normal(x,1)
  z <~ normal(y,1)
  return z
````

The returned value, `z`, is generated by passing the last value generated by the function, starting with the original function argument. This indicates that it might be 
reducible to a smaller program. Assuming that we named the program `simplify_before.hk`, we can call the `Simplify` transform by running:

````bash
hk-maple simplify_before.hk
````

**Note:** The output for `Simplify` will be printed in the console. You can easily save this program to a file by redirecting the output to a file by calling 
`hk-maple model1.hk > model2.hk`. For this example, we will call our new program `simplify_after.hk`. 

When you open our new program, `simplify_after.hk`, you will see that the original five-line program has been reduced to a single line:

````nohighlight
fn a prob: normal(prob2real(a), sqrt(3))
````

### Disintegrate ###
(TODO)


### Summarize ###

These examples are given in Maple syntax as opposed to typical examples in Hakaru syntax. 

First "summate i" in offshore under gmm_gibbs.hk

````nohighlight
summarize(piecewise(_b=piecewise(i=docUpdate,zNew,z[i]),t[i],0), kb, i)
  =
  [Split(i=docUpdate, Fanout(Add(t[i]), Nop()),
                        Index(size(as), _b, z[i], Add(t[i]))),
     summary -> piecewise(_b=zNew, summary[1][1], 0) + summary[2][_b+1]]

      Recursive call to summarize assuming i=docUpdate is true:
      summarize(piecewise(_b=zNew,t[i],0), kb, i)
      = [Fanout(Add(t[i]), Nop()), summary -> piecewise(_b=zNew, summary[1], 0)]

      Recursive call to summarize assuming i=docUpdate is false:
      summarize(piecewise(_b=z[i],t[i],0), kb, i)
      = [Index(size(as), _b, z[i], Add(t[i])), summary -> summary[_b+1]]

          summarize(t[i], kb, i)
          = [Add(t[i]), summary -> summary]
````

First "summate j" in offshore under naive_bayes_gibbs.hk
````nohighlight
  summarize(piecewise(doc[j]=docUpdate,piecewise(k=zNew,piecewise(i=w[j],1,0),0),0), kb, j)
  = [Fanout(Index(size(word_prior), i, w[j], Index(size(z), docUpdate, doc[j], Add(1))),
            Index(size(z), docUpdate, doc[j], Nop())),
     summary -> piecewise(k=zNew, summary[1][w[j]+1][docUpdate+1]], 0)]

      Recursive call to summarize assuming k=zNew is true:
      summarize(piecewise(doc[j]=docUpdate,piecewise(i=w[j],1,0),0), kb, j)
      = [Index(size(word_prior), i, w[j], Index(size(z), docUpdate, doc[j], Add(1))),
         summary -> summary[w[j]+1][docUpdate+1]]

          Recursive call to summarize assuming i=w[j]:
          summarize(piecewise(doc[j]=docUpdate,1,0), kb, j)
          = [Index(size(z), docUpdate, doc[j], Add(1)),
             summary -> summary[docUpdate+1]]

      Recursive call to summarize assuming k=zNew is false:
      summarize(piecewise(doc[j]=docUpdate,0,0), kb, j)
      = [Index(size(z), docUpdate, doc[j], Nop()),
         summary -> 0]
````
