[![Hackage](https://img.shields.io/hackage/v/hakaru.svg)](https://hackage.haskell.org/package/hakaru)
[![Build Status](https://travis-ci.org/hakaru-dev/hakaru.svg?branch=master)](https://travis-ci.org/hakaru-dev/hakaru)
[![Windows Build Status](https://ci.appveyor.com/api/projects/status/3dbdr2hjfk40x697?svg=true)](https://ci.appveyor.com/project/zaxtax/hakaru)
[![licence](http://img.shields.io/badge/licence-BSD-blue.svg?style=flat)](https://github.com/hakaru-dev/hakaru/blob/master/LICENSE)

Hakaru
======

A simply-typed probabilistic programming language, designed for easy
specification of probabilistic models, and inference algorithms.

Warning: this code is alpha and experimental.

Contact us at ppaml@indiana.edu

Documentation
-------------
Learn more at [hakaru-dev.github.io](http://hakaru-dev.github.io).

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
    echo 'libname := "/path-to-hakaru/hakaru/maple",libname:' >> ~/.mapleinit

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
    echo 'libname := "C:\\<path to hakaru>\\hakaru\\maple",libname:' >> "C:\<path to maple>\lib\maple.ini"

Note the escaped backslashes.

Citing us
---------
When referring to Hakaru please cite the following [paper](http://homes.soic.indiana.edu/ccshan/rational/system.pdf):

Probabilistic inference by program transformation in Hakaru (system description).
Praveen Narayanan, Jacques Carette, Wren Romano, Chung-chieh Shan, and Robert Zinkov,
FLOPS 2016 (13th international symposium on functional and logic programming).

	@article{NarayananCRSZ16,
	  author  = {Praveen Narayanan and
			     Jacques Carette and
			     Wren Romano and
			     Chung{-}chieh Shan and
			     Robert Zinkov},
	  title   = {Probabilistic Inference by Program Transformation in Hakaru (System
			     Description)},
	  journal = {Functional and Logic Programming - 13th International Symposium, {FLOPS}
			     2016, Kochi, Japan, March 4-6, 2016, Proceedings},
	  pages   = {62--79},
	  year    = {2016},
	  url     = {http://dx.doi.org/10.1007/978-3-319-29604-3_5},
	  doi     = {10.1007/978-3-319-29604-3_5},
    }


