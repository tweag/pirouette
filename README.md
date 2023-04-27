# Pirouette

_Pirouette is a research prototype under active development_

Pirouette is a framework for constructing different static
analysis tools for [System F]-based languages. It has a number of
transformations (monomorphization, defunctionalization, prenex, etc...) implemented,
which can be composed in different ways to cater for different goals.

[System F]: https://en.wikipedia.org/wiki/System_F

## Bounded Symbolic Evaluation

There is one analysis currently built into pirouette, which symbolically evaluates terms
while looking for counterexamples based on a mixture of [incorrectness] and Hoare triples.
Say we have a function `t :: Ins -> Outs`, we can check that for all `i :: Ints` up to a certain
size, `P (t i) i` implies `Q (t i) i`, where `P` and `Q` are the user-defined predicates we
interested in enforcing. We invite the interested reader to our [blog-post][tweag-blogpost] for more
details on these reasoning techniques.
The design of Pirouette is discussed in more details in [DESIGN.md](./DESIGN.md).

[incorrectness]: https://dl.acm.org/doi/pdf/10.1145/3371078
[tweag-blogpost]: https://www.tweag.io/blog/2022-07-01-pirouette-2/

### Use Cases

#### Example Language

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
quickly use it to find that assignment:

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

#### Plutus Smart Contracts

[Plutus] is a subset of Haskell used to write smart contracts for Cardano blockchain.
Pirouette has a prototype interface to interacting with
plutus through `Language.Pirouette.PlutusIR`, but further work is necessary to
seamlessly interact with validator scripts.

To run Pirouette on Plutus Intermediate Representation scripts,
one has to use the [pirouette-plutusir library].

[Plutus]: https://plutus.readthedocs.io/en/latest/
[pirouette-plutusir library]: https://github.com/tweag/pirouette-plutusir

### Limitations

In its current form, pirouette itself is still a research prototype,
hence, it has plenty of limitations. The overall approach of pirouette's
symbolic engine is an intersection of bounded model checking and symbolic execution, hence,
it also carries the limitations of a model checker: exploration of the state space can be slow
and it is not a substitute for a formal proof of correctness.

## Building, Installing and Hacking

The recommended way of building pirouette is through [Nix].
Enter the Nix shell with `nix develop` then run `cabal update` and `cabal build` at the
root of the repository.

[Nix]: https://nixos.org/

### Pre-commit Hooks and CI

In order to help avoid CI failures due to formatting problems,
we recommend that you install a pre-commit hook for running Ormolu.
The Nix shell already enables such a pre-commit hook transparently.

## Contributing

Did you find a bug while using pirouette?
Please [report it][new-issue].
Would you like to help fix a bug or add a feature?
We welcome pull requests! Check [the issue page][issues] for inspiration.

[issues]: https://github.com/tweag/pirouette/issues
[new-issue]: https://github.com/tweag/pirouette/issues/new?assignees=&labels=type%3A+bug&template=bug_report.md

## License

See [LICENSE](LICENSE).

Copyright © 2021–present Tweag I/O
