Predicativize: a tool for making proofs predicative
=============================================

## Installation

First start by installing Dedukti (https://github.com/Deducteam/Dedukti hash `c65e7e`) and then simply run `make`. In order to test the tool, run `make test` which will predicativize the Fermat's little theorem library. If Agda is installed, then you can also run `make test_agda`, which also translates the results to Agda files and typechecks them.

## Modes

By running `dune exec -- predicativize --help` we can see that the following modes are available.
```
  -s      Handles files in the sttfa syntax, else it expects files in the pts syntax (see theory/pts.dk)
  -o      Enables optmizations to make the result depend on less universe variables (might render the level constraints unsolvable)
  -a      Automatically translates the output to agda files and typechecks them
```
