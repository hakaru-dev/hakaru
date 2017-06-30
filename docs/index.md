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

### [Generating Samples from your Hakaru Program](intro/samplegen) ###

You can use the `hakaru` command to generate samples from your probabilistic model.

### [Quick Start: A Mixture Model Example](intro/quickstart) ###

This page will introduce you to Hakaru's basic functionality by creating a program to sample and condition a mixture model of a coin toss.

### [Compiling to Haskell](/transforms/compile) ###

A Hakaru program can be ported into Haskell which can then be converted into machine code for other applications.

### [Compiling to C](/transforms/hkc) ###

Depending on the scale, a Hakaru program might be resource-intensive to run. In these situations, you could port your Hakaru program to C using the `hkc` command to take
advantage of other tools such as OpenMP for parallel processing. 

## Hakaru Workflow and Examples ##

### [What is the Hakaru Workflow?](/workflow/intro.md) ###

Hakaru provides a language and tools to aid in each step of the Bayesian inference workflow.

### [Tutorial: Hakaru Workflow for Discrete Models](workflow/discrete.md) ###

This example of a burglary alarm demonstrates the workflow typically followed when creating Hakaru programs.

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

### [Functions](/lang/functions) ###

Hakaru supports both named and anonymous function definitions.

### [Types and Coercions](/lang/coercions) ###

Hakaru has basic types which can also be combined to make complex ones. To aid in the communication of information between Hakaru functions, coercions are defined to allow 
conversions between compatible types.

### [Data Types and Match](/lang/datatypes) ###

Hakaru supports some built-in data types from Haskell. The `match` function is used for deconstructing them to extract their elements and to reconstructing data back into
these data types.

### [Arrays and Plate](/lang/arrays) ###

Hakaru has special syntax for arrays, which is considered distinct from the other supported data types. A specialized array, `plate`, is used for describing measures over
arrays.

### [Loops](/lang/loops) ###

Hakaru loops are specialized to compute the summation or product of the elements in an array.

### [Expect](/transforms/expect) ###

The expectation feature (`expect`) computes expectation of a measure with respect to a given function. 

## Transformations ##

Hakaru includes some inference algorithms that you can use to transform your probabilistic models into other forms to extract desireable information. Its inference 
algorithms are implemented predominantly as program transformations.

**Note:** By default, Hakaru assigns a weight to each generated sample. Typically a weight of one is used, but it is possible for the weights to vary between samples. This 
might result in differing results from the original and transformed programs when summarizing a program's output by counting them.

### [Normalize](/transforms/normalize) ###

The normalization transformation (`normalize`) reweights a program so that it represents a normal distribution.

### [Disintegrate](/transforms/disintegrate) ###

The disintegration transformation (`disintegrate`) produces a program representing the conditional distribution based on a joint probability distribution. This command
is equivalent to model conditioning in probability theory. 

### [Density](/transforms/density) ###

The density transformation (`density`) is used to create a conditional distribution model that is used to estimate the density of the distribution at a particular point.

### [Hakaru-Maple](/transforms/hk-maple) ###

The simplify transformation (`hk-maple -c Simplify`) is used to improve Hakaru programs by simplifying probabilistic models using computer algebra. This transformation requires the
use of Maple. Hakaru provides two other transformations also written in Maple.

### [Metropolis Hastings](/transforms/mh) ###

The Metropolis Hastings transform (`mh`) is used to convert a Hakaru program into a Metropolis Hastings transition kernel.

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
