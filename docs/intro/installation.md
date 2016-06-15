# Installation

Install Hakaru by cloning the latest version from our Github repo

````bash
git clone https://github.com/hakaru-dev/hakaru
cd hakaru
````

Hakaru can then be installed either with `cabal install` or `stack install`

## Installing on Windows

Due to a [ghc bug](https://ghc.haskell.org/trac/ghc/ticket/3242), until ghc 8.0
is released Windows machines need to install the logfloat library separately

````bash
cabal install -j logfloat -f -useffi
cd hakaru
cabal install
````

# Maple extension

Within Hakaru, we use [Maple](http://www.maplesoft.com/) to perform
computer-algebra guided optimizations. To get access to these optimizations
you must have a licensed copy of Maple installed.

In addition to this, we must autoload some Maple libraries that come
with the system to access this functionality

````bash
export LOCAL_MAPLE="`which maple`"
cd hakaru/maple
maple update-archive.mpl
echo 'libname := "/path-to-hakaru/hakaru/maple",libname:' >> ~/.mapleinit
````

Under Windows the instructions become

````bash
SETX LOCAL_MAPLE "<path to Maple bin directory>\cmaple.exe"
cd hakaru\maple 
cmaple update-archive.mpl
echo 'libname := "C:\\<path to hakaru>\\hakaru\\maple",libname:' >> "C:\<path to maple>\lib\maple.ini"
````

If the Maple extension has been properly installed running

````bash
echo "normal(0,1)" | simplify -
````

should return

````bash
normal(0, 1)
````

If the `LOCAL_MAPLE` environment variable is not set, then `simplify`
defaults to invoking `ssh` to access a remote installation of Maple.
The invocation is
````bash
"$MAPLE_SSH" -l "$MAPLE_USER" "$MAPLE_SERVER" "$MAPLE_COMMAND -q -t"
````
and defaults to
````bash
/usr/bin/ssh -l ppaml karst.uits.iu.edu "maple -q -t"
````
