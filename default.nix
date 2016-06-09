{ nixpkgs ? import <nixpkgs> {}, compiler ? "default" }:

let

  inherit (nixpkgs) pkgs;

  f = { mkDerivation, ansi-terminal, base, Cabal, containers
      , directory, filepath, ghc-prim, HUnit, indentation-parsec
      , integration, language-c, logfloat, math-functions, mtl
      , mwc-random, optparse-applicative, parsec, pretty, primitive
      , process, QuickCheck, semigroups, stdenv, text, transformers
      , vector
      }:
      mkDerivation {
        pname = "hakaru";
        version = "0.3.0";
        src = ./.;
        isLibrary = true;
        isExecutable = true;
        libraryHaskellDepends = [
          ansi-terminal base Cabal containers directory filepath ghc-prim
          HUnit indentation-parsec integration logfloat math-functions mtl
          mwc-random parsec pretty primitive process semigroups text
          transformers vector
        ];
        executableHaskellDepends = [
          base filepath language-c mtl mwc-random optparse-applicative pretty
          text
        ];
        testHaskellDepends = [
          ansi-terminal base Cabal containers ghc-prim HUnit
          indentation-parsec integration logfloat math-functions mtl
          mwc-random parsec pretty primitive process QuickCheck semigroups
          text transformers vector
        ];
        homepage = "http://indiana.edu/~ppaml/";
        description = "A probabilistic programming embedded DSL";
        license = stdenv.lib.licenses.bsd3;
      };

  haskellPackages = if compiler == "default"
                       then pkgs.haskellPackages
                       else pkgs.haskell.packages.${compiler};

  drv = haskellPackages.callPackage f {};

in

  if pkgs.lib.inNixShell then drv.env else drv
