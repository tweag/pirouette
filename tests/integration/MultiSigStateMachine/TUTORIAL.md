# Tutorial

## Prerequisites

Because Pirouette is still in a prototype phase, operating the tool can feel a little
awkward for the uninitiated. We will work on the user interface soon, but the primary priority
is validating our research ideas and building a reliable tool first.

In this tutorial we assume some familiarity with standard PL jargon
and expect the reader to be somewhat familiar with Haskell, Plutus and the Extended UTxO model [[1](https://iohk.io/en/research/library/papers/the-extended-utxo-model/), [2](https://iohk.io/en/research/library/papers/native-custom-tokens-in-the-extended-utxo-model/)].

## Introduction

Smart Contracts are interactive programs that take actions based on
some input, in the form of transactions. A number of bugs and exploits
arise from writing contracts that accept more input traces than
previously thought of by its designers. Verification for smart contracts is both
important and achievable. It is
important since there is limited opportunity for patching mistakes and
bugs can potentially be exploited leading to the undue extraction or
loss of funds. And it is achievable because the self-contained nature
of Smart Contracts and the limited interaction with the off-chain
world make them particularly amenable to verification.

The goal of pirouette is to extract the on-chain transition function
of your Plutus smart contract into TLA+, which in turn enables us to
experiment with and exhaustively check the state space for certain
conditions. Even though model-checking is no substitute to a full
development in a proof-assistant, it greatly increases our assurance
that the contract is correct.

In this tutorial, we will go over how to extract the TLA+ code for an
example contract and how to use TLC to check the extracted TLA+
against a specification.  We focus on the
[MultiSigStateMachine](https://github.com/input-output-hk/plutus/blob/master/plutus-use-cases/src/Plutus/Contracts/MultiSigStateMachine.hs)
contract, which gathers a number of signatures from a predetermined
set of signers and issues a payment when enough signatures have been
gathered. The transition function is:


```haskell
transition :: Params -> State MSState -> Input -> Maybe (TxConstraints Void Void, State MSState)
transition params State{ stateData =s, stateValue=currentValue} i = case (s, i) of
    (Holding, ProposePayment pmt)
        | isValidProposal currentValue pmt ->
            Just ( mempty
                 , State
                    { stateData = CollectingSignatures pmt []
                    , stateValue = currentValue
                    })
    (CollectingSignatures pmt pks, AddSignature pk)
        | isSignatory pk params && not (containsPk pk pks) ->
            let constraints = Constraints.mustBeSignedBy pk in
            Just ( constraints
                 , State
                    { stateData = CollectingSignatures pmt (pk:pks)
                    , stateValue = currentValue
                    })
    (CollectingSignatures payment _, Cancel) ->
        let constraints = Constraints.mustValidateIn (Interval.from (paymentDeadline payment)) in
        Just ( constraints
             , State
                { stateData = Holding
                , stateValue = currentValue
                })
    (CollectingSignatures payment pkh, Pay)
        | proposalAccepted params pkh ->
            let Payment{paymentAmount, paymentRecipient, paymentDeadline} = payment
                constraints = Constraints.mustValidateIn (Interval.to $ paymentDeadline - 1)
                           <> Constraints.mustPayToPubKey paymentRecipient paymentAmount
            in Just ( constraints
                    , State
                        { stateData = Holding
                        , stateValue = currentValue - paymentAmount
                        })
    _ -> Nothing
```

### Obtaining the `.pir` and `.flat` files.

The `MultiSigStateMachine.flat` file in this folder was obtained by appending the snippet below to the source code, loading the resulting file into GHCi then running `saveBinaryFile`.

```haskell
saveBinaryFile :: Haskell.IO ()
saveBinaryFile = case getPir $$(PlutusTx.compile [|| mkValidator ||]) of
                   Just res -> BS.writeFile "MultSigStateMachine.flat" (flat res)
                   Nothing  -> error "plutus compilation failed"
```

## Extracting the TLA+ implementation

When extracting TLA+, pirouette expets to receive a valid PlutusIR program
and a speficic enough `--prefix <PRFX>` such that only one PlutusIR definition contains `<PRFX>`
as a prefix. That's the function pirouette will interpret as the main function for the contract.
In general, pirouette will check that the given selected function has the form:

```
case i of
  C1 ... -> f1
  ...
  CN ... -> fN
```

Pirouette will then interpret this first pattern-match as being the different entrypoints of the contract.
Hence, its important that the given transition function starts by pattern-matching on the user input.
Pirouette will then generate TLA+ code that looks like:

```tlaplus
... \* all auxiliary definitions for the body of the actions f1, ..., fN

\* The actions with inputs and their wrapped variant, where the inputs are
\* existentially quantified
C1(...) == f1
WrappedC1 == \E a0 \in SetOfA , ... : C1(a0, ...)

...

CN(...) == fN
WrappedCN == \E b0 \in SetOfB , ... : CN(b0, ...)

\* The Next state predicate
Next == WrappedC1 \/ ... \/ WrappedCN
```

To obtain correct TLA+ from the `transition` function
above we must instruct `pirouette` to perform certain transformations to it.
In fact, to go from `MultiSigStateMachine.flat` to a model-checkable TLA+ spec
we need to run:

```
cabal run pirouette -- MultiSigStateMachine.flat \
  --prefix transition \
  --pull-destr 2 \
  --with-args param,st,i \
  --tla-skel Skeleton.tla \
  --action-wrapper "LET res == ___ IN st' = res.arg1 /\ txConstr' = res.arg0"
```

Through this tutorial, we will go over each of those options and explain how could you
write the equivalent command line for your contract.

### Identifying the User Input

The Plutus Intermediate Representation language is not meant to be
read nor written by a human, therefore, it has no case
statement. Instead, it uses datatype destructors (or eliminators) as a
builtin to represent pattern matching.  A destructor for a type is the
opposite of a constructor. It characterizes the use of the type's
inhabitants.  As a concrete example, the `maybe` function in Haskell
is the destructor (or eliminator) for the `Maybe` datatype.  In
PlutusIR there is no pattern-matching hence we must rely on destructors
to do case analisys.

The `--pull-destr n` (or `-p n`) option will instruct pirouette to pull the `n`-th destructor
to the top of the program, if possible. Because we are receiving generated code, we never know for sure
which value the plutus decided to pattern-match on first. We can, however, interactively discover this.
We can ask pirouette to print its _terms_ and inspect what we're dealing with by running:

```
cabal exec pirouette -- MultiSigStateMachine.flat --prefix transition --term-only | less
```

Here, we are instructing pirouette to load the definitions from `MultiSigStateMachine.flat`, filter all of those whose name contains `transition` as a prefix and print their definitions. In this case, we should see a lot of output, the beginning of which is:

```
transition :=
  Params0 -> (State0 MSState) -> Input -> (Maybe (Tuple20 (TxConstraints0 Void
                                                                          Void)
                                                          (State0 MSState)))
  λ (params1098 : Params0) (ds1099 : State0 MSState) (i1100 : Input)
  . State_match @MSState
      1#ds1099
      @(Maybe (Tuple20 (TxConstraints0 Void Void) (State0 MSState)))
      (λ (ds1101 : MSState) (ds1102 : List0 (Tuple20 ByteString
                                                     (List0 (Tuple20 ByteString
                                                                     Integer))))
       . MSState_match 1#ds1101
           @(Maybe (Tuple20 (TxConstraints0 Void Void) (State0 MSState)))
           (λ (pmt1107 : Payment0) (pks1108 : List0 ByteString)
            . Input_match 4#i1100
                @(Maybe (Tuple20 (TxConstraints0 Void Void) (State0 MSState)))
  ...
```

This is a simplification of the PlutusIR representation of the
`transition` function and is what pirouette is going to use
when extracting the TLA+ model from it.  Yet, the first
pattern-match happens on the variable `1#ds1099` (the `1#` prefix is the De Bruijn index of this variable),
of type `State`.  If we were to ask `pirouette` for some TLA+ without any further
modification, it would think that the `1#ds1099` is the variable that
represents user input. In fact, the variable representing the user's
input is matched third. First we match on `State`, then we match on
`MSState`, then finally we match on `Input`. Hence, we pass `--pull-destr 2`
or `-p 2` to instruct pirouette to pull the (starting at 0) destructor number 2
to the root of the term.


```
cabal exec pirouette -- MultiSigStateMachine.flat --prefix transition --term-only -p 2 | less
```

Which will instruct pirouette to pull the third destructor to the root (the first destructor is of index 0).  We should now see:

```
transition :=
  Params0 -> (State0 MSState) -> Input -> (Maybe (Tuple20 (TxConstraints0 Void
                                                                          Void)
                                                          (State0 MSState)))
  λ (params1098 : Params0) (ds1099 : State0 MSState) (i1100 : Input)
  . Input_match 0#i1100
      @(Maybe (Tuple20 (TxConstraints0 Void Void) (State0 MSState)))
      (λ pk1110 : ByteString . State_match @MSState
           2#ds1099
           @(Maybe (Tuple20 (TxConstraints0 Void Void) (State0 MSState)))
           (λ (ds1101 : MSState) (ds1102 : List0 (Tuple20 ByteString
                                                          (List0 (Tuple20 ByteString
                                                                          Integer))))
            . MSState_match 1#ds1101
                @(Maybe (Tuple20 (TxConstraints0 Void Void) (State0 MSState)))
```

### Using a TLA+ Skeleton

Running the command:

```
cabal exec pirouette -- MultiSigStateMachine.flat --prefix transition -p 2 | less
```

Will produce a large amount of TLA+ code, but this code will not work
with TLA+ out-of-the-box. That is because pirouette produces the `Next` predicate,
but it does not produce the `Init` predicate nor fairness annotations or any other
boilerplate including declaration of variables, constants and module dependencies.
Hence, the user should provide a skeleton file, which is
TLA+ spec that contains two consecutive separators and the necessary
boilerplate to make the extracted TLA+ code into a working TLA+ spec for their contract.
Pirouette will insert the generated definitions in between the two consecutive separators.
A separator in TLA+ is a line containing four or more `'-'` characters. A Skeleton will look somewhat like:

```tlaplus
---- MODULE xxx ----

EXTENDS Integers, FiniteSequences, ...
CONSTANTS ...
VARIABLES ...

vars == << ... >>

----
----

\* initial state definition
Init == ...

\* specification
Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

===
```

For the particular case of the `MultiSigStateMachine`, we use the [Skeleton.tla](Skeleton.tla) file present
in this directory. We can instruct pirouette to use said file with the `--tla-skel` or `-s` option.

### Wrapping the Action Formulas

When translating the main program, we translate each branch of the first case analisys into a TLA+ operator.
Say we're translating:

```
transition :: State -> Input -> Maybe (Output, State)
transition st i = case i of
  C1 ... -> f1
  ...
  CN ... -> fN
```

Each `f_i` is a term of type `Maybe (Output, State)`. Pirouette understands that the branches
that lead to a `Notinhg` represent _invalid transitions_ of the mealy machine, hence it will
prune these cases out, and we will be left with an operator `fi(...)` that computes the TLA+ representation
of a value of type `(Output, State)`. This is not a TLA+ _action_ just yet because it does not define the value
of the variables in the _next state_. Looking at [the skeleton](Skeleton.tla) for the `MultiSigStateMachine`, we see
two TLA+ `VARIABLE`s: `st` and `txConstr`. Hence, there must be a statement for `st' = ...` and `txConstr' = ...`
somewhere, which specifies the value of those variables in the next state. For our particular case, we want to
our resulting operators to be:

```tlaplus
Action_f_i(...) == LET res == f_i(...)
                    IN st' = res.arg1 /\ txConstr' = res.arg0
```

Which computes the values for the next state and then assigns them as such. Pirouette will apply the `--action-wrapper` (`-w`)
to all operators representing the entrypoints of the contract and it will substitute the occurrence of `___` for the generated
body of the operator. Hence, for the multisig contract, the `--action-wrapper` is:

```
LET res == ___ IN st' = res.arg1 /\ txConstr' = res.arg0
```

#### Haskell Values in TLA+

A value of an algebraic datatype is represented using a TLA+ record
with fields `cons,arg0,...,argN`. Take the value `Just 42` of type `Maybe Int`.
It is represented with:

```
[ cons |-> "Just" , arg0 |-> 42 ]
```

## Conclusion

We have seen how to produce a usable TLA+ model from the `MultiSigStateMachine` contract. Running this TLA+ model
and specifying properties for it is out of the scope of this tutorial and, for the time being, does require
some expertise in TLA+.