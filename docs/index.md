<h1 class="logo">Hakaru</h1>

----------------------------

Hakaru is a probabilistic programming language. A probabilistic programming
language is a language specifically designed for manipulating probability
distributions. These sorts of languages are great for machine learning and
stochatic modeling.

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

### [Random Primitives](lang/rand)

### Let and Bind

### Conditionals

### Functions

### Datatypes and match

### Arrays

## Transformations

Hakaru implements its inference algorithms predominately as
program transformations. The following are the major ones
our system provides.

Expect

Disintegrate

Simplify

Metropolis Hastings

## Internals

The internals section of the manual provides some insight into how
Hakaru is implemented and offers guidance into how the system can
be extended.

AST

ABT

Datums

Coercions

Transformations

Testing

Adding a Language Feature
