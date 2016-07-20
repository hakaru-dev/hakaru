# Adding a feature to the Hakaru language

To add a feature to the Hakaru language you must

* Add an entry to the AST
* Update symbol resolution and optionally the parser to recognize this construct
* Update the pretty printers if this is something exposed to users
* Update the typechecker to handle it
* Update all the program transformations (Expect, Disintegrate, Simplify, etc) to handle it
* Update the sampler if this primitive is intended to exist at runtime
* Update the compilers to emit the right code for this symbol

We give an example of what this looks like by adding `double` to the language.
