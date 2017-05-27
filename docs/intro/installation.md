# Installing Hakaru #

You can download Hakaru by cloning the latest version from our GitHub repository:

```bash
git clone git@github.com:hakaru-dev/hakaru
```

Hakaru can be installed by using either `stack install` or `cabal install` inside the `hakaru` directory. One way that you can access these tools is by installing the [Haskell Platform](https://www.haskell.org/platform/) which supports Linux, OSX, and Windows operating systems.

If you are using `stack install`, you can install and verify your installation of Hakaru by running the commands:

```bash
stack install
stack test
```

You can find the output of `stack test` in the `.stack-work/logs/hakaru-0.4.0-test.txt` file.

If you are using `cabal install`, you can install Hakaru by running the commands:

```bash
cabal update    
cabal install -j --only-dependencies --enable-tests
cabal configure --enable-tests
cabal build
cabal test
```

On Windows systems, you can use the `stack install` and `cabal install` commands by running them in a Linux shell such as [Cygwin](https://www.cygwin.com/) or Git Bash.

**Note:** If you want to use `cabal install` and have installed the Haskell Platform, you might need to add a reference to the directory containing `cabal.exe` to the `PATH` environment variable.

If you are using GHC 7.10 or earlier on a Windows system and want to use the `cabal install` command, you must install the `logfloat` dependency manually after running `cabal update` due to a
[GHC bug](https://ghc.haskell.org/trac/ghc/ticket/3242):

```bash  
cabal update    
cabal install -j logfloat -f -useffi
cabal install -j --only-dependencies --enable-tests
cabal configure --enable-tests
cabal build
cabal test
```

## Extending Hakaru with Maple ##

Hakaru uses [Maple](http://www.maplesoft.com/products/maple/) to perform computer-algebra guided optimizations. You must have a licensed copy of Maple installed to access this component of the Hakaru language.

On Linux systems, Hakaru can be setup to use Maple by running:

```bash
export LOCAL_MAPLE="`which maple`"
cd hakaru/maple
maple update-archive.mpl
echo 'libname := "/path-to-hakaru/hakaru/maple",libname:' >> ~/.mapleinit
```

On Windows systems, Hakaru can be setup to use Maple by performing the following steps in Administrator mode:

1. Create a User Environment Variable `LOCAL_MAPLE` using the Windows command prompt (cmd) by running:
	
	`SETX LOCAL_MAPLE "<path to Maple bin directory>\cmaple.exe"`

	This variable can also be created via the Advanced System Properties.
	
	**Note:** You might need to restart your computer for the variable to be recognized.
	
2. Add the path to `cmaple.exe` to your PATH system environment variable. This can be done via the Advanced System Properties.

	**Note:** You might need to restart your computer for the variable to be recognized.	

3. In the Windows command prompt (cmd), Navigate to the `hakaru\maple` directory and run:
	
	`cmaple update-archive.mpl`

4. In the Windows command prompt (cmd), create a file `maple.ini` by running:

	`echo libname := "C:\\<path to hakaru>\\hakaru\\maple",libname: >> "C:\<path to maple>\lib\maple.ini"`
	
### Testing Your Maple Installation with Hakaru ###

If you have correctly installaed Hakaru's Maple extension, running `echo "normal(0,1)" | simplify -` in a `bash` command line will return `normal(0, 1)`.

If you have not set the `LOCAL_MAPLE` environment variable, then `simplify` command might try to locate a `SSH` file that might not exist on your machine to try and access a remote installation of Maple.