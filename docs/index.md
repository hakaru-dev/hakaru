<h1 class="logo">Hakaru</h1>

----------------------------

Hakaru is a probabilistic programming language. A probabilistic programming
language is a language specifically designed for manipulating probability
distributions. These sorts of languages are great for machine learning and
stochastic modeling.

## Overview

This manual provides a guide for how to use Hakaru.

## Introduction

### [What is Probabilistic Programming](intro/probprog)

Probabilistic programming systems allow us to write programs which
describe probability distributions, and provide mechanisms to
sample and condition the distributions they represent on data. In
this page, we give a sense of the sorts of problems Hakaru is
great at solving, and how you would describe them in Hakaru.

### [Installation](intro/installation)

Learn how to install Hakaru

### [Quickstart](intro/quickstart)

Get started with this quickstart page. Where we show
how to sample and condition from a small Hakaru program.

## [Examples](examples)

Here we go through several more involved examples of the kinds of
problems Hakaru is uniquely well-suited to solve.

In particular, we describe a model for Gaussian Mixture Models and
using a form of Bayesian Naives Bayes as applied to document
classification.

## Language Guide

The language section provides an overview of the syntax of Hakaru as
well as some of the primitives in the language.

### [Random Primitives](/lang/rand)

These are the built-in probability distributions.

### [Let and Bind](/lang/letbind)

This is how we can give names to subexpressions and a
draw from a probability distribution.

### [Conditionals](/lang/cond)

Hakaru supports a restricted `if` expression

### [Types and Coercions](/lang/coercions)

Hakaru is a simply-typed language. This section
describes the types available and functions for
moving between them.

### [Functions](/lang/functions)

Defining and using functions

### [Datatypes and match](/lang/datatypes)

Hakaru supports a few built-in datatypes, and offers functionality for
taking them apart and reconstructing them.

### [Arrays and loops](/lang/arrays)

We offer special support for arrays, and for probability
distributions over arrays.
We also express loops that compute sums and products.

## Transformations

Hakaru implements its inference algorithms predominately as
program transformations. The following are the major ones
our system provides.

### [Expect](/transforms/expect)

Computing expectation of a measure

### [Disintegrate](/transforms/disintegrate)

A transformation which takes a joint distribution and
produces a program representing the conditional distribution.

### [Simplify](/transforms/simplify)

Any Hakaru expression can be simplified, using
the Maple computer-algebra system.

### [Metropolis Hastings](/transforms/mh)

Automatically transform a measure into a transition kernel usable
in a Metropolis Hastings algorithm.

### [Compiling to Haskell](/transforms/compile)

### [Compiling to C](/transforms/hkc)

## Internals

The internals section of the manual provides some insight into how
Hakaru is implemented and offers guidance into how the system can
be extended.

[AST](/internals/ast)

[ABT](/internals/abt)

[Datums](/internals/datums)

[Coercions](/internals/coercions)

[Transformations](/internals/transforms)

[Testing](/internals/testing)

[Adding a Language Feature](/internals/newfeature)
