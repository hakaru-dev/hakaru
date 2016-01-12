hakaru
======

A probabilistic programming language.

Warning: this code is alpha and experimental.

Installation
------------

Hakaru has multiple components. To build it by default run

    cabal update
    cabal install -j --only-dependencies
    cabal configure --enable-tests
    cabal build
    cabal test

If you have Maple installed and wish to take advantage
of Hakaru's program simplifier run

    export LOCAL_MAPLE="`which maple`"
    cd hakaru/maple
    maple update-archive.mpl
    echo 'libname := "'"$HOME"'/hakaru/maple",libname:' >~/.mapleinit

Installation - Windows
------------

It is possible to use Hakaru on Windows; there are some possible concerns. Due to a
[ghc bug](https://ghc.haskell.org/trac/ghc/ticket/3242), one of the dependencies
(logfloat) must be installed separately:
  
    cabal install -j logfloat -f -useffi
    cabal install -j --only-dependencies
    ...

In order to use Maple for simplification, set the LOCAL_MAPLE environment
variable in the command prompt (cmd) to cmaple.exe (instead of `export LOCAL_MAPLE...'):

    SETX LOCAL_MAPLE "<path to Maple bin directory>\cmaple.exe"

The other commands can be run with in a cygwin shell. Lacking a cygwin shell,
the following will work in a command prompt: 

    cd hakaru\maple 
    cmaple update-archive.mpl
    echo libname := "C:\\<path to hakaru>\\hakaru\\maple",libname: > "C:\<path to maple>\lib\maple.ini"

Note the escaped backslashes.

Citing us
---------
When referring to Hakaru please cite the following [paper](http://homes.soic.indiana.edu/ccshan/rational/system.pdf):

> Probabilistic inference by program transformation in Hakaru (system description).
> Praveen Narayanan, Jacques Carette, Wren Romano, Chung-chieh Shan, and Robert Zinkov, 2015. To appear at FLOPS 2016 (13th international symposium on functional and logic programming).


