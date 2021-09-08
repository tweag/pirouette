# Manual Test Cases

These are PlutusIR files that have been written by hand in order to exercise
specific parts of pirouette. Because the PIR parser does not support comments
we'll have the tests documented here.

## [Basic 1](basic-01.pir)

Responsible for testing basic parsing, normalization and code generation functionality.
Consits in a simple pir file containing a transition function that is equivalent to `const id`.

## [Basic 2](basic-02.pir)

Contains a more involved transition system that stores a list of booleans in its state
and, as an input, can either extend that list with some value or compress
the entire list `xs` replacing it by `[or xs]`.

## [Basic 3](basic-03.pir)
_PENDING:_ Waiting for issue #3, then needs to be added to `all.json`.

Similar to `basic-02`, but with another input option for replacing the
state `xs` with `map (const b) xs`, for some user given `b` and it 
defines `or` using a `AdditiveMonoid` just like the PlutusIR that is generated 
by the plutus compiler.

## [HO Constructor, Simple Transition](ho-constr-simple-transi.pir)

Defines a simple contract that uses values of type `forall s . Maybe (s -> s)` but,
upon normalization reduzes to a first order program. The main objective here
is testing the `removeExcessiveDestrArgs` function ([here](https://github.com/tweag/pirouette/blob/88d38d34b52184957e89d9183db1fbd45e0055ea/src/Pirouette/Term/Transformations.hs#L165)), 
which ensures that the over-saturated `Input_match` on `ho-constr-simple-transi.pir:45`
gets its last parameter distributed, then gets all its branches normalized.
Note that this tests `removeExcessiveDestrArgs` with distributing both term and type arguments.

## [HO Constructor, HO transition](ho-constr-ho-transi.pir)
_PENDING:_ Waiting for issue #3

Just like `ho-constr-simple-transi.pir`, but eta reduces the `transition` function, meaning that
now our PIR program is already in normal form, and we must represent functions as data
or eta-expand things. For now, our strategy is to rely on defunctionalization. We can
always try to do something smarter with eta expansions if the need for it arises.

## [HO Destructor](ho-destr.pir)

Defines a trivial contract but uses a destructor that returns a value of a function type.
Also tests normalization and destructor eta-reduction.

## [Inner Let Statements](inner-let.pir)
_PENDING:_ needs to be added to `all.json`

Tests let-expansion. Our representation of System F has no let-bindings, hence we lift all
definitions within a let-binding to the outer scope transforming its free variables
into bound variables, then passing all the necessary arguments on all call sites.

## [Mutual Recursion](mutual-recursion.pir)
_PENDING:_ Pirouette cannot output valid TLA+ for mutually recursive datatypes; nevertheless, we need to add this to `all.json`

Defines a _ZigZag_-like mutually recursive datatype, then uses it in a trivial transition function.
