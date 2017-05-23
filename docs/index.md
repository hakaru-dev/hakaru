<h1 class="logo">Hakaru</h1>

----------------------------

Hakaru is a simply-typed probabilistic programming language, designed for easy specification of probabilistic models and inference algorithms. This type of language is useful
for the development of machine learning algorithms and stochastic modeling. Hakaru enables the design of modular probabilistic inference programs by providing:

-  A language for representing probabilistic distributions, queries, and inferences
-  Methods for transforming probabilistic information, such as conditional probability and probabilistic inference, using computer algebra

This documentation provides information for installing and using Hakaru. Sample programs are included to demonstrate some of Hakaru's functionality and Hakaru implementation
details are included to help guide future Hakaru developments and extensions.

**Warning: This code is alpha and experimental.**

Contact us at ppaml@indiana.edu if you have any questions or concerns.

## Introduction ##

The Introduction presents probabilistic programming and illustrates how Hakaru can be used to solve and describe these types of problems, how to install Hakaru on your 
machine, and some sample programs to get you started.

### [What is Probabilistic Programming?](intro/probprog)

Probabilistic programming systems allow us to write programs which describe probability distributions, and provide mechanisms to sample and condition the distributions 
they represent on data. In this page, we give a sense of the sorts of problems Hakaru is great at solving, and how you would describe them in Hakaru.

### [Installing Hakaru](intro/installation) ###

You can install Hakaru on Linux, OSX, and Windows and extend its functionality using MapleSoft's Maple. 

### [Quick Start: A Mixture Model Example](intro/quickstart) ###

This page will introduce you to Hakaru's basic functionality by creating a program to sample and condition a mixture model of a coin toss.

### [Examples](examples) ###

Two examples, a Gaussian Mixture Model and a Latent Dirichlet Allocation (LDA) topic model, highlight the types of problems that Hakaru is uniquely suited to help you solve.

## Language Guide ##

The Language Guide presents an overview of Hakaru's language primitives and core functionality.

### [Primitive Probability Distributions](/lang/rand) ###

Common probability distributions, such as the normal distribution, are already encoded in Hakaru and are considered to be language primitives. This page provides usage
instructions for accessing the primitive distributions in your programs.

### [Let and Bind](/lang/letbind) ###

Let (`=`) and Bind (`<~`) enable the use of variables in Hakaru programs, which is essential for extracting a value from a probability distribution.

### [Conditionals](/lang/cond) ###

Hakaru supports a restricted `if` expression for selections between two conditions.

### [Functions](/lang/functions)

Defining and using functions

### [Types and Coercions](/lang/coercions)

Hakaru is a simply-typed language. This section describes the types available and functions for moving between them.

### [Data Types and Match](/lang/datatypes)

Hakaru supports a few built-in datatypes, and offers functionality for taking them apart and reconstructing them.

### [Arrays and Plate](/lang/arrays)

We offer special support for arrays, and for probability distributions over arrays.

### [Loops](/lang/loops)

You can use Hakaru loops to compute sums and products of arrays.

## Transformations

Hakaru implements its inference algorithms predominately as program transformations. The following are the major ones our system provides.

### [Expect and Normalize](/transforms/expect)

Computing expectation of a measure

### [Disintegrate and Density](/transforms/disintegrate)

A transformation which takes a joint distribution and produces a program representing the conditional distribution.

### [Simplify](/transforms/simplify)

Any Hakaru expression can be simplified, using the Maple computer-algebra system.

### [Metropolis Hastings](/transforms/mh)

Automatically transform a measure into a transition kernel usable in a Metropolis Hastings algorithm.

### [Compiling to Haskell](/transforms/compile)

### [Compiling to C](/transforms/hkc)

## Internals

The internals section of the manual provides some insight into how Hakaru is implemented and offers guidance into how the system can be extended.

- [AST](/internals/ast)
- [ABT](/internals/abt)
- [Datums](/internals/datums)
- [Coercions](/internals/coercions)
- [Transformations](/internals/transforms)
- [Testing Hakaru modules](/internals/testing)
- [Adding a Language Feature](/internals/newfeature)

## Citing Us ##

When referring to Hakaru, please cite the following [academic paper](http://homes.soic.indiana.edu/ccshan/rational/system.pdf):

P. Narayanan, J. Carette, W. Romano, C. Shan and R. Zinkov, "Probabilistic Inference by Program Transformation in Hakaru (System Description)", Functional and Logic 
Programming, pp. 62-79, 2016.

```nohighlight
@inproceedings{narayanan2016probabilistic,
	title = {Probabilistic inference by program transformation in Hakaru (system description)},
	author = {Narayanan, Praveen and Carette, Jacques and Romano, Wren and Shan, Chung{-}chieh and Zinkov, Robert},
	booktitle = {International Symposium on Functional and Logic Programming - 13th International Symposium, {FLOPS} 2016, Kochi, Japan, March 4-6, 2016, Proceedings},
	pages = {62--79},
	year = {2016},
	organization = {Springer},
	url = {http://dx.doi.org/10.1007/978-3-319-29604-3_5},
	doi = {10.1007/978-3-319-29604-3_5},
}
```
