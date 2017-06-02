# Testing infrastructure in Hakaru

Unit testing has been created for Hakaru's main functions. The test suite is managed by Cabal and written in Haskell.

Tests written to test programs written using Hakaru are located in the `tests/` subdirectory at the root of the 
project. Tests written in Haskell to check Hakaru functionality can be found at `haskell/Tests/`.

## Running Tests ##

Hakaru can be tested by running `cabal test` or `stack test` from the root directory of the project.

**Note:** Tests that require Maple, such as `simplify` tests, are only run if a local installation of Maple is detected.

## Creating New Tests ##

Hakaru testing is managed in the `hakaru.cabal` file found in the root directory. The main file for using the test suite is `TestSuite.hs`, which can be
found in `haskell\tests`.

For all tests, two programs are required -- the program to test and a program representing the expected result.

### Writing Hakaru Tests ###

When creating Hakaru tests, your two programs must be saved as seperate files.

You can add a test of your Hakaru programs to a Haskell program by using the `testConcreteFiles` function from `haskell/Tests/TestTools.hs`. This function 
takes two Hakaru programs as arguments. It first runs `simplify` on the first file and then asserts if it is equivilant to the second file.

### Writing Haskell Tests ###

Haskell tests are created using the `HUnit` testing framework. Most existing Haskell tests use the `testSStriv` function from `haskell/Tests/TestTools.hs`.
This function asserts that the first Haskell function passed to it simplifies to the same function provided by the second function argument. The 
simplification performed specifically calls the `simplify` Hakaru transform.