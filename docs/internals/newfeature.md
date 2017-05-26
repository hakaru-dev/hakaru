# Adding a feature to the Hakaru language

To add a feature to the Hakaru language you must

* Add an entry to the AST
* Update symbol resolution and optionally the parser to recognize this construct
* Update the pretty printers if this is something exposed to users
* Update the typechecker to handle it
* Update all the program transformations (Expect, Disintegrate, Simplify, etc) to handle it
* Update the sampler if this primitive is intended to exist at runtime
* Update the compilers to emit the right code for this symbol

TODO: We give an example of what this looks like by adding `double` to the language.

## Documenting a Hakaru Feature

If you add a new feature to Hakaru, you should write accompanying documentation so that others can learn how to use it. The Hakaru documentation is written using 
[MkDocs](http://www.mkdocs.org/), which uses MarkDown to format source files. In order to download MkDocs, it is recommended that you use the [Python](https://www.python.org/) 
package manager `pip`. The `pip` package manager is bundled with Python starting in versions 2.7.9 and 3.4, so it will be installed alongside Python. If you are using an 
earlier version of Python, you will need to install `pip` manually. 

- On Windows, you must download `get-pip.py` and run it in the command prompr using `python get-pip.py`
- On Linux, you can install `pip` from the command line using `sudo apt-get install python-pip`
- On OSX, you can install `pip` from the command line using `sudo easy-install pip`

Once you have installed `pip`, you can download the required packages for the Hakaru documentation:

````bash
pip install mkdocs
pip install python-markdown-math
pip install mkdocs-extensions
pip install mkdocs-bootswatch
````