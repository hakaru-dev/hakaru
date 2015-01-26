hakaru
======

A probabilistic programming language.

Warning: this code is alpha and experimental.

Installation
------------

Hakaru has multiple components to build it by default run

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

Example
-------

Coming soon.
