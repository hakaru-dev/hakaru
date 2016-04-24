with (import <nixpkgs> {}).pkgs;
let pkg = haskellPackages.callPackage
            ({ mkDerivation, ansi-terminal, base, Cabal, containers, directory
             , filepath, ghc-prim, HUnit, indentation, integration, logfloat
             , math-functions, mtl, mwc-random, parsec, pretty, primitive
             , process, QuickCheck, semigroups, stdenv, text, transformers
             , vector
             }:
             mkDerivation {
               pname = "hakaru";
               version = "0.3.0";
               src = ./.;
               isLibrary = true;
               isExecutable = true;
               buildDepends = [
                 ansi-terminal base Cabal containers directory filepath ghc-prim
                 HUnit indentation integration logfloat math-functions mtl
                 mwc-random parsec pretty primitive process semigroups text
                 transformers vector cabal-install
               ];
               testDepends = [
                 ansi-terminal base Cabal containers ghc-prim HUnit indentation
                 integration logfloat math-functions mtl mwc-random parsec pretty
                 primitive process QuickCheck semigroups text transformers vector
               ];
               homepage = "http://indiana.edu/~ppaml/";
               description = "A probabilistic programming embedded DSL";
               license = stdenv.lib.licenses.bsd3;
             }) {};
in
  pkg.env
