# Pirouette

_Pirouette is a research prototype under active development_

* [Use case: Example](#example-language)
* [Use case: Plutus Smart Contracts](#plutus-smart-contracts)
* [Limitations](#limitations)
* [Building, Installing and Hacking](#building-installing-and-hacking)
* [Contributing](#contributing)
* [License](#license)

Pirouette is being built as framework for constructing different static
analisys tools for [System F][systemf] based languages. It has a number of
transformations (monomorphization, defunctionalization, prenex, etc...) defined
and relies on the `-XQuasiQuotes` extension to be able to easily write
properties in the target language.

There is one analisys currently built into pirouette, which symbolic evaluates terms up to
a certain bound while looking for counterexamples based on [incorrectness][incorrectness]
or Hoare triples.

[systemf]: https://en.wikipedia.org/wiki/System_F
[incorrectness]: https://dl.acm.org/doi/pdf/10.1145/3371078
[tweag-blogpost]: TODO

# Use Case: Example

The `Language.Pirouette.Example` defines the `Ex` language: pirouette's example language.
We refer the interested reader to check the respective module for guidelines on using pirouette over
your own language.

Now, say we have the simple program:

```haskell
addone :: Integer -> Integer
addone x = x + 1
```

And we wish to check the incorrectness triple `[x > 0] addone x [result > 0]`, that
is: if `addone x > 0`, then `x > 0`. We obviously expect a counterexample with `x = 0`.
We can use pirouette to find that assignment:

```haskell
parms :: IncorrectnessParams Ex
parms = IncorrectnessParams
          [term| \x:Integer . x + 1 |] -- Term to symbolically evaluate
          [ty| Integer |] -- type of the term above
          -- Conditions to check
          ([term| \(res:Integer) (x:Integer) . 0 < res |]
            :==>: [term| \(res:Integer) (x:Integer) . 0 < x |])
```

Now we can run `replIncorrectnessLogic1 10 params` in a repl and we should see:
```
💸 COUNTEREXAMPLE FOUND
{ __result ↦ 1
  x ↦ 0 }
```

# Use Case: Plutus Smart Contracts

[Plutus] is a subset of Haskell used to
write smart contracts for Cardano blockchain, which utilizes the _Extended UTxO_
[[1](https://iohk.io/en/research/library/papers/the-extended-utxo-model/),
[2](https://iohk.io/en/research/library/papers/native-custom-tokens-in-the-extended-utxo-model/)]
model to represent its accounts. Pirouette has a prototype interface to interacting with
plutus through `Language.Pirouette.PlutusIR`, but further work is necessary to
seamlessly interact with validator scripts.

An example of using pirouette to load and check an incorrectness triple over a `.pir` file
can be found in [here](tests/unit/Language/Pirouette/PlutusIR/SymEvalSpec.hs).

## Building, Installing and Hacking

The recommended way of building pirouette is through [Nix](https://nixos.org/guides/install-nix.html).
Enter the Nix shell with `nix-shell` then run `cabal build` at the
root of the repository. It is important that you *set up your nix cache* according to the
[instructions in the plutus repository](https://github.com/input-output-hk/plutus#iohk-binary-cache)
to avoid building GHC when you start the nix shell.

You might want to consider `direnv` and [`nix-direnv`](https://github.com/nix-community/nix-direnv)
instead of running `nix-shell` directly.

## Limitations

In its current form, `pirouette` itself is still a research prototype
and, hence, it has plenty of limitations. The overall approach of pirouette's
symbolic engine is an intersetion of bounded model checking and symbolic executon, hence,
it also carries the limitations of a model checker: it can be slow
space can be slow and a model checker is not a substitute for a formal
proof of correctness.

## Contributing

Did you find a bug while using `pirouette`? Please [report it](https://github.com/tweag/pirouette/issues/new?assignees=&labels=type%3A+bug&template=bug_report.md). Would you like to help fix a bug or add a feature?
We welcome pull requests! Check the [issue](https://github.com/tweag/pirouette/issues) page for inspiration.

## License

See [LICENSE](LICENSE).

Copyright © 2021–present Tweag I/O

[Plutus]: https://plutus.readthedocs.io/en/latest/
