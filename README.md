Predicativize: A tool for sharing proofs with predicative system
=============================================

We refer to the paper [Translating proofs from an impredicative type system to a predicative one](https://github.com/thiagofelicissimo/my-files/blob/master/predicativize.pdf?raw=true) for an introduction to the tool.

## Installation

First start by installing Dedukti (https://github.com/Deducteam/Dedukti hash `c65e7e`) and then simply run `make`. In order to test the tool, run `make test_agda` which will predicativize the Fermat's little theorem library. If Agda is installed, then you can also run `make test_agda_with_typecheck`, which also translates the results to Agda files and typechecks them.

You can also test the tool with Matita's arithmetic library, by running `make matita_agda`, and with a fragment of Isabelle's library, by running `make isabelle_agda`. However, be advised that these take a lot of time.

## Modes

By running `dune exec -- predicativize --help` we can see that the following modes are available.
```
  -a      Automatically translates the output to agda files
  -at     Automatically translates the output to agda files and typechecks them
  --eta   Uses eta equality
  --cstr  A file containing extra constraints to be taken into account
  --meta  A file containing metarules to be applied to the files
  --path  Paths to look for .dko files
```

The `--path` option should be used to point to the theory files defining the encoding.

The meta file supplied to `--meta` should be used to translate from the source file's syntax to the `theory/pts.dk` syntax, which is the one used. You can look at `metas/sttfa_to_pts.dk` for a meta file allowing to translate from the syntax of `theory/sttfa.dk` to the syntax of `theory/pts.dk`.

In order to see an example of cstr file, you can look at `extra_cstr/matita.dk`.

You can look at the makefile to see examples of how these options are used.

## Times

- matita - with `lt_4_to_fact` and `le_fact_10` : ~37 min
- matita - without `lt_4_to_fact` and `le_fact_10` : ~7 min
- test (fermat's little theorem proof in hol) : ~2 min
