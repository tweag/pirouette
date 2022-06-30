# Disclaimer

### This branch is deprecated; latest work is in `dev`

`dev` will be merged as soon as possible

# Pirouette

_Pirouette is a research prototype under active development_

* [Bounded Symbolic Evaluation](#bounded-symbolic-evaluation)
  - [Use case: Example](#example-language)
  - [Use case: Plutus Smart Contracts](#plutus-smart-contracts)
  - [Limitations](#limitations)
* [Building, Installing and Hacking](#building-installing-and-hacking)
* [Contributing](#contributing)
* [License](#license)

Pirouette is a framework for constructing different static
analysis tools for [System F][systemf]-based languages. It has a number of
transformations (monomorphization, defunctionalization, prenex, etc...) implemented,
which can be composed in different ways to cater for different goals.

# Bounded Symbolic Evaluation

There is one analysis currently built into pirouette, which symbolically evaluates terms
while looking for counterexamples based on a mixture of [incorrectness][incorrectness] and Hoare triples.
Say we have a function `t :: Ins -> Outs`, we can check that for all `i :: Ints` up to a certain
size, `P (t i) i` implies `Q (t i) i`, where `P` and `Q` are the user-defined predicates we
interested in enforcing. We invite the interested reader to our [blog-post][tweag-blogpost] for more 
details on these reasoning techniques.

[systemf]: https://en.wikipedia.org/wiki/System_F
[incorrectness]: https://dl.acm.org/doi/pdf/10.1145/3371078
[tweag-blogpost]: TODO

## Use Cases

### Example Language

The `Language.Pirouette.Example` defines the `Ex` language: pirouette's example language.
We refer the interested reader to this module for guidelines on using pirouette over
your own language.

Now, say we have the simple program:

```haskell
addone :: Integer -> Integer
addone x = x + 1
```

And we wish to check the incorrectness triple `[x > 0] addone x [result > 0]`, that
is: if `addone x > 0`, then `x > 0`. We obviously expect a counterexample with `x = 0`.
Because pirouette conveniently uses the `-XQuasiQuotes` extension, we can 
quickly use it find that assignment:

```haskell
params :: IncorrectnessParams Ex
params = IncorrectnessParams
          [term| \x:Integer . x + 1 |] -- A function term to symbolically evaluate, this is our t above
          [ty| Integer |] -- type of the result of the function term above
          -- Conditions to check, they take the result and the inputs of the function term,
          -- these are our P and Q above
          ([term| \(res:Integer) (x:Integer) . 0 < res |]
            :==>: [term| \(res:Integer) (x:Integer) . 0 < x |])
```

Now we can run `replIncorrectnessLogicSingl 10 params` in a repl and we should see:
```
💸 COUNTEREXAMPLE FOUND
{ __result ↦ 1
  x ↦ 0 }
```

### Plutus Smart Contracts

[Plutus] is a subset of Haskell used to
write smart contracts for Cardano blockchain.
Pirouette has a prototype interface to interacting with
plutus through `Language.Pirouette.PlutusIR`, but further work is necessary to
seamlessly interact with validator scripts.

An example of using pirouette to load and check an incorrectness triple over a `.pir` file
can be found [here](tests/unit/Language/Pirouette/PlutusIR/SymEvalSpec.hs).

[Plutus]: https://plutus.readthedocs.io/en/latest/

## Limitations

In its current form, `pirouette` itself is still a research prototype,
hence, it has plenty of limitations. The overall approach of pirouette's
symbolic engine is an intersection of bounded model checking and symbolic execution, hence,
it also carries the limitations of a model checker: exploration of the state space can be slow
and it is not a substitute for a formal
proof of correctness.

# Building, Installing and Hacking

The recommended way of building pirouette is through [Nix](https://nixos.org/guides/install-nix.html).
Enter the Nix shell with `nix-shell` then run `cabal build` at the
root of the repository. It is important that you *set up your nix cache* according to the
[instructions in the plutus repository](https://github.com/input-output-hk/plutus#iohk-binary-cache)
to avoid building GHC when you start the nix shell.

You might want to consider `direnv` and [`nix-direnv`](https://github.com/nix-community/nix-direnv)
instead of running `nix-shell` directly.

## Pre-commit Hooks and CI

Our CI runs `ormolu` and `cabal test`. In order to help avoid CI failures due to 
formatting problems, we recommend that you install the 
[pre-commit hook for running ormolu](tests/ormolu-pre-commit-hook.sh).
To do so, simply copy (or link) the script into `.git/hooks/pre-commit`.

# Contributing

Did you find a bug while using `pirouette`? 
Please [report it](https://github.com/tweag/pirouette/issues/new?assignees=&labels=type%3A+bug&template=bug_report.md). 
Would you like to help fix a bug or add a feature?
We welcome pull requests! Check the [issue](https://github.com/tweag/pirouette/issues) page for inspiration.

# License

See [LICENSE](LICENSE).

Copyright © 2021–present Tweag I/O

