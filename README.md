# Pirouette

_Pirouette is a research prototype under active development_

* [Use case: Example](#example-language)
* [Use case: Plutus Smart Contracts](#plutus-smart-contracts)
* [Limitations](#limitations)
* [Building, Installing and Hacking](#building-installing-and-hacking)
* [Contributing](#contributing)
* [License](#license)

Pirouette is being built as framework for constructing different static
analisys tools for [System F][systemf] based languages. It posseses a multitude of
transformations (monomorphization, defunctionalization, prenex, etc...)
and relies on the `-XQuasiQuotes` extension to be able to easily write
properties in the target language.

There is one analisys currently built into pirouette, which symbolic evaluates terms up to
a certain bound while looking for counterexamples based on [incorrectness][incorrectness]
or [Hoare][hoare] triples.

[systemf]: https://en.wikipedia.org/wiki/System_F
[incorrectness]: TODO
[hoare]: TODO

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


----

Pirouette is a semi-automatic code extraction tool. It extracts a
[TLA+](https://lamport.azurewebsites.net/tla/tla.html) specification
from a [Plutus] Mealy Machine. The extracted TLA+ specification can then be used to
study and model-check properties over the Plutus Mealy
Machine.

## Plutus Smart Contracts and Transition Systems

[Plutus] is a subset of Haskell used to
write smart contracts for Cardano blockchain, which utilizes the _Extended UTxO_
[[1](https://iohk.io/en/research/library/papers/the-extended-utxo-model/),
[2](https://iohk.io/en/research/library/papers/native-custom-tokens-in-the-extended-utxo-model/)]
model to represent its accounts. This means that smart contracts
written for the Cardano ecosystem are different from the usual
account-based ledger format we see in most other blockchain ecosystems.

The core of a EUTxO contract is the _[validator script](https://plutus.readthedocs.io/en/latest/plutus/tutorials/basic-validators.html)_ and in a multitude of scenarios, these validator scripts will be created with the help
of either the _StateMachine_ library [[1](https://plutus-pioneer-program.readthedocs.io/en/latest/week7.html#code-example-2),[2](https://github.com/input-output-hk/plutus/blob/master/plutus-contract/src/Plutus/Contract/StateMachine.hs)] or a custom implementation of state machines. Therefore, the core of most contracts will be a Mealy Machine of the form:

```haskell
transition :: State -> Input -> Maybe (State, Output)
```

Pirouette's main functionality is extracting the `transition` function into TLA+ in such a way that
the constructors of the `Input` datatype are used to represent the possible state transitions. This means
that when TLA+ finds a counter-example, we will see the sequence `[i0, ..., iN] :: [Input]` of inputs
we need to pass to `transition` to witness the failure.

## Building, Installing and Hacking

The recommended way of building pirouette is through [Nix](https://nixos.org/guides/install-nix.html).
Enter the Nix shell with `nix-shell` then run `cabal build` at the
root of the repository. It is important that you *set up your nix cache* according to the
[instructions in the plutus repository](https://github.com/input-output-hk/plutus#iohk-binary-cache)
to avoid building GHC when you start the nix shell.

You might want to consider `direnv` and [`nix-direnv`](https://github.com/nix-community/nix-direnv)
instead of running `nix-shell` directly.

### Profling Pirouette

To build with profiling enabled, open a nix shell with `nix-shell --arg enableHaskellProfiling true` (
_WARNING:_ This will take a long time to complete). Once inside the nix shell, you can
`cabal build --enable-profiling` and pass `+RTS` options to the executable normally.

## Usage

Run `cabal run pirouette -- --help` to see an updated list of options.
For a more in depth tutorial on using Pirouette, have a look at the [MultiSigStateMachine tutorial](tests/integration/MultiSigStateMachine/TUTORIAL.md).

Because the PlutusIR parser is [still experimental](https://github.com/input-output-hk/plutus/issues/3445),
we recommend to pass a binary PlutusIR file
to `pirouette`. You can save the PlutusIR code of your contract as a binary file
by loading your contract on GHCi, then running the `saveBinaryFile` or `savePirFile` functions, exemplified below.


```haskell
import qualified Data.ByteString as BS
import           Flat

import           Your.Plutus.Contract (mkValidator)

saveBinaryFile :: Haskell.IO ()
saveBinaryFile = case getPir $$(PlutusTx.compile [|| mkValidator ||]) of
                   Just res -> BS.writeFile "contract.flat" (flat res)
                   Nothing  -> error "plutus compilation failed"

-- If you want to save a .pir file, make sure to call prettyClassicDebug to avoid
-- a pretty printer bug where variables can get shadowed
import qualified PlutusCore.Pretty as P
savePirFile :: Haskell.IO ()
savePirFile = case getPir $$(PlutusTx.compile [|| mkValidator ||]) of
                Just res -> Haskell.writeFile "contract.pir" (show $ P.prettyClassicDebug res)
                Nothing  -> error "plutus compilation failed"
```

Note that you _do not_ need to import Pirouette to get a `.pir` or a `.flat` file from your contract,
The `getPir` function comes from `plutus-core`.


## Limitations

In its current form, `pirouette` itself is still a research prototype and, hence, has its limitations.
In particular, it has difficulties dealing with arbitrary higher-order PlutusIR code. When pirouette successfully
outputs a TLA+ spec, some familiarity and experience with TLA+ itself are required to extract useful results
out of it. The tool does not figure out the specification for you.

The overall approach of using TLA+ also carries the usual limitations
of a model checker: the process of exhaustively checking the state
space can be slow and a model checker is not a substitute for a formal
proof of correctness.

## Contributing

Did you find a bug while using `pirouette`? Please [report it](https://github.com/tweag/pirouette/issues/new?assignees=&labels=type%3A+bug&template=bug_report.md). Would you like to help fix a bug or add a feature?
We welcome pull requests! Check the [issue](https://github.com/tweag/pirouette/issues) page for inspiration.

## License

See [LICENSE](LICENSE).

Copyright © 2021–present Tweag I/O

[Plutus]: https://plutus.readthedocs.io/en/latest/
