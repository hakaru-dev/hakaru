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
