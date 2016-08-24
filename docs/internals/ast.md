# Internal Representation of Hakaru terms

The Hakaru AST can be found defined in
[haskell/Language/Hakaru/Syntax/AST.hs](https://github.com/hakaru-dev/hakaru/blob/master/haskell/Language/Hakaru/Syntax/AST.hs). It is made up of several parts which this section and the next one will explain.

We should note, this datatype makes use of
[Abstract Binding Trees](http://winterkoninkje.dreamwidth.org/103978.html)
which we discuss in more detail in the next
[section](/internals/abt). ABTs can be understood as a way to abstract
the use of variables in the AST. The advantage of this is it allows
all variable substitution and manipulation logic to live in one place
and not be specific to a particular AST.

## Datakind

## Term

## SCons and SArgs

## PrimOp

## MeasureOp

## ArrayOp
