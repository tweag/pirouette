Pirouette's Design
==================

This document aims at giving an overview of the crucial parts of Pirouette, and
pointers to get familiar with the code. As such, it contains three parts.

1. The [first part][languages] describe how Pirouette supports several input
   languages as well as two languages that are particularly relevant to us: [the
   example language] and the support for Plutus IR – [Plutus intermediate
   representation].

2. The [second part][transformations] describes the transformations that
   Pirouette performs on the input language to get it in a shape ready for
   symbolic execution.

3. The [third part][symbolic engine] digs into what constitutes the heart of
   Pirouette: its symbolic engine, and in particular the [symbolic evaluator]
   and the [symbolic prover].

Languages
---------

[languages]: #languages

### Pirouette's genericity

Pirouette attempts to be generic in the input language by only assuming that it
is System F-like. Anyone can then come and define their instance of
`LanguageBuiltins`, which is Pirouette's way of defining the constants, builtin
terms and builtin types of a language. The definition of the classes can be
found in [`Pirouette.Term.Syntax.Base`]. For a simple, concrete instantiation of
a language, you might want to check [the example language]. For a more involved
one, you might want to check [the support for Plutus IR][plutus intermediate
representation].

### The example language

[the example language]: #the-example-language

The example language is the only instance of a language included in Pirouette.
It is a simple functional language supporting higher-order types with explicit
type annotations, basic types (booleans, integers, strings) with their
associated operators, algebraic datatypes and pattern-matching. The definition
of the language is done by providing the `LanguageBuiltins` instance. You will
find all the heavy work in [`Language.Pirouette.Example`].

The example language also has a concrete syntax heavily inspired by Haskell.
Thanks to quasi-quoters, it is easy to define a set of unordered value
definitions for the `Ex`ample language:

```haskell
myProgram :: PrtUnorderedDefs Ex
myProgram = [prog|
  addone : Integer -> Integer
  addone x = x + 1

  addtwo : Integer -> Integer
  addtwo x = x + 2
|]
```

Now for a more involved example. Say we want to compute a sum of integers in a
generic way. We can do that by writing a function `sum` taking a list of
integers and returning the total. In order to do that, we first need a notion of
lists, which we choose to do in a generic way. Here we go:

```haskell
data List a
  = Nil : List a
  | Cons : a -> List a -> List a
```

Computing the sum of the elements of a list requires traversing it, which we can
also decide to do in a generic way with a fold over the list.

```haskell
foldr : forall a r . (a -> r -> r) -> r -> List a -> r
foldr @a @r f e l =
  match_List @a l @r
    e
    (\(x : a) (xs : List a) . f x (foldr @a @r f e xs))
```

Note how quantification in types has to be explicit, and the definition of the
datatype `List` also creates the corresponding `match_List` function taking, in
that order, the datatype type arguments, an element of that datatype, the
returning type, and as many cases as there are constructors, in the same order.

The hardest part has been done. It is now simple to define a `sum` function, a
list of integers -- say `1`, `2`, `3` -- and apply `sum` over them.

```haskell
sum : List Integer -> Integer
sum =
  foldr
    @Integer
    @Integer
    (\(x : Integer) (y : Integer) . x + y)
    0

myList : List Integer
myList = Cons @Integer 1 (Cons @Integer 2 (Cons @Integer 3 (Nil @Integer)))

myListTotal : Integer
myListTotal = sum myList
```

For more examples, check out the standard library for the example language in
[`Language.Pirouette.Example.StdLib`]. The standard library also comes with a
quasi-quoter of its own allowing you to leverage it in your code should you want
it:

```haskell
myProgram :: PrtUnorderedDefs Ex
myProgram = [progWithStdLib|
  sum : List Integer -> Integer
  sum =
    foldr
      @Integer
      @Integer
      (\(x : Integer) (y : Integer) . x + y)
      0
|]
```

### Plutus Intermediate Representation

[plutus intermediate representation]: #plutus-intermediate-representation

To run Pirouette on Plutus Intermediate Representation scripts, one has to use
the [pirouette-plutusir library].

[pirouette-plutusir library]: https://github.com/tweag/pirouette-plutusir

Transformations
---------------

_This part is empty and should be documented._ Transformations live in
[`Pirouette.Transformations`].

Symbolic Engine
---------------

The symbolic engine is split into three main parts: an SMT prover, as well as
all the administrative work to communicate with it, Pirouette's _[symbolic
evaluator]_, and Pirouette's _[symbolic prover]_. We describe these three
aspects in the following sub-sections.

### SMT prover

As is classic in symbolic engines, Pirouette relies on SMT provers to do the
hard work. These provers are used in two different ways. They help pruning
branches of execution that are actually unreachable, and they help deciding
whether the user's statement/questions actually hold.

Pirouette relies on [smtlib-backend] for the communication with its SMT prover
of choice, [Z3]. There are still a bunch of modules in Pirouette making the
interface between the rest of the engine and [smtlib-backends], mainly to
convert assumptions/constraints to the [SMT-LIB] language. These modules live in
[`Pirouette.SMT`].

[z3]: https://github.com/Z3Prover/z3
[smtlib-backends]: https://github.com/tweag/smtlib-backends
[smt-lib]: https://smtlib.cs.uiowa.edu/

### Symbolic Evaluator

[symbolic evaluator]: #symbolic-evaluator

#### The symbolic evaluation monad — `SymEval`

The heart of Pirouette's symbolic engine lives in [`Pirouette.Symbolic.Eval`].
This module defines the `SymEval` monad providing all the tooling to make
symbolic evaluation work. Here is the monad in question:

```haskell
newtype SymEval lang a = SymEval
  { symEval ::
      ReaderT
        (SymEvalEnv lang)
        (StateT (SymEvalSt lang) WeightedList)
        a
  }
```

Morally speaking, though, and forgetting the `lang` type parameters, this monad
simply represent functions of type:

```haskell
SymEvalEnv -> SymEvalSt -> [(a, SymEvalSt)]
```

taking an environment and a state and returning a list of state, as well as
potential return values. It returns a list because symbolic evaluation may
branch and explore different paths.

#### The key function — `symEvalOneStep`

[`symEvalOneStep`]: #the-key-function-symEvalOneStep

The key function in this module is `symEvalOneStep`, whose type is the
following:

```haskell
symEvalOneStep ::
  forall lang .
  SymEvalConstr lang =>
  TermMeta lang SymVar ->
  WriterT Any (SymEval lang) (TermMeta lang SymVar)
```

Once again, morally speaking, forgetting the `lang` type parameters and
replacing `TermMeta lang SymVar` by just `Term`, this function has type `Term ->
SymEval Term`. One can then think of this as a function of type:

```haskell
SymEvalEnv -> (Term, SymEvalSt) -> [(Term, SymEvalSt)]
```

Such a function takes a term in the input language and a symbolic evaluation
state. It tries to apply one step of beta-reduction to the term, which may yield
zero, one or several potential terms and updated states.

For an example, let us assume that our input term is the body of the `foldr`
function in [the example language], specialised for lists of `Integer`s (for
readability, we remove the type applications).

```haskell
match_List l
  e
  (\(x : Integer) (xs : List Integer) . f x (foldr f e xs))
```

and that our state specifies that:

- `e` is an integer, without giving its value,
- `f` is the function `\(x : Integer) (y : Integer) . x + y`, and
- `l` is a list of integers, without giving its value.

One step of the symbolic engine would then have to explore both branches of the
pattern matching, and therefore it would return two pairs `Term, SymEvalSt`:

1. In the first pair, the `Term` would be `e` itself and the state would be
   updated to account for the fact that we now know that `l = Nil`.
2. In the second pair, the `Term` would be `f x (foldr f e xs)` and the state
   would be updated to account for the fact the we now have two more variables,
   `x` and `xs`, that are an integer and a list of integers respectively, and an
   additional constraint, `l = Cons x xs`.

The whole symbolic execution consists in running this one step over and over
again until it is not possible to reduce the terms anymore. In the example
above, our first term/state is now blocked because there isn't much one can do
with an integer. The second term/state is not blocked because one can replace
`f` by its definition and continue unfolding from there.

#### The symbolic evaluation state — `SymEvalSt`

Defined in [`Pirouette.Symbolic.Eval.Types`], the symbolic state basically
contains the following:

1. A context of variables, that is a map from variable names to their types.
   This context is typically called Γ in literature, and `gamma` in the code.

2. A set of constraints linking variables together, for instance `l == Cons x
   xs`, `k != Nil` or `x = 7`. It is in fact not a set, but a complex
   union-find-based type.

3. Statistics on the execution, for instance the number of unfoldings that took
   place. Despite the name, those statistics can have an important impact on the
   behaviour of the engine because they are observed to decide whether to stop
   the execution or not.

as well as some extra fields necessary for administrative reasons. Those field
names are prefixed by `sest` in the code.

#### The symbolic evaluation environment — `SymEvalEnv`

Defined in [`Pirouette.Symbolic.Eval`], the symbolic environment contains the
following:

1. A set of unordered definitions in which to evaluate the term. For instance,
   if your term is `foldr @Integer @Integer (\(x : Integer) (y : Integer) . x +
   y) 0 l`, then `foldr` and `l` have to come from somewhere, and it will
   probably be the example language's standard library augmented with the
   definition of the list of integers `l`, and that would be the set of
   definitions in the environment.

2. Two “solvers” that are functions taking a problem and trying to solve it. The
   one of interest to us in the symbolic evaluation is `solvePathProblem ::
   CheckPathProblem lang -> Bool` which takes a “path problem” describing the
   logical formulas that have to hold for this path to be reachable and answers
   whether or not it is.

3. Options influencing the behaviour of the symbolic execution. Those control
   for instance the size of the pool of SMT solvers that Pirouette uses in the
   background. More importantly, the options contain a function `shouldStop ::
   StoppingCondition`, where `StoppingCondition` is a type alias for
   `SymEvalStatistics -> Bool`. This function inspects the statistics in the
   symbolic evaluation state and decides whether the symbolic evaluation should
   stop. This is a generalisation of the usual notion of “fuel”. Two trivial
   instances would be `\_ -> false` that never stops and `\stat ->
   sestConstructors stat > 50` that stops after 50 constructors unfoldings.

Those field names are prefixed by `see` in the code.

### Symbolic Prover

[symbolic prover]: #symbolic-prover

The symbolic prover is a wrapper around the [symbolic evaluator]. One can see
the symbolic evaluator as the library providing the generic tooling for symbolic
evaluation, which the symbolic prover uses to answer requests about Hoare
triples.

#### The key functions — `proveRaw` and `worker`

Defined in [`Pirouette.Symbolic.Prover`], the `proveRaw` and `worker` function
are the main part of the symbolic prover. Morally speaking, these functions take
as input a triple of terms, called the _antecedent_, the _body_ and the
_consequent_, of shapes `λr,xs. A(r,xs)`, `λxs. B(xs)` and `λr,xs. C(r,xs)`
respectively, where `r` is a symbolic argument for the _result_ and `xs` is a
list of symbolic arguments common to all three terms. The idea that `r` is the
result means that we will always consider `λxs. A(B(xs), xs)` and `λxs. C(B(xs),
xs)`. Assuming the body is of type `αs -> ρ`, then the antecedent and consequent
should be of type `ρ -> αs -> Bool`, that is they should be considered as two
predicates on the body's result and arguments. The prover attempts to check two
properties on the three terms `A`, `B` and `C`:

- First, the prover attempts to check whether the antecedent is consistent, that
  is whether there exists `xs` such that `A(B(xs), xs)` holds.

- Second, the prover attempts to check whether the antecedent implies the
  consequent, that is whether for all `xs`, `A(B(xs), xs) ⇒ C(B(xs), xs)`.

Concretely, `proveRaw` takes a `Problem` and does all the administrative work of
extracting the `xs` from the body, creating corresponding symbolic variables,
preparing the terms, and then calls `worker`, where all the actual work happens.

`worker` takes the three aforementioned terms as input and evaluates them all by
one step. We refer the reader to [`symEvalOneStep`] for what this means
precisely. If any of the three terms is stuck, that is if it is not possible to
evaluate them more, then `worker` attempts to see if the properties above holds.
It can do that without having fully evaluated the terms: for instance, it is
possible to check whether the antecedent is consistent without knowing anything
about the consequent. To some extent, it is even possible to check whether the
antecedent is consistent without knowing anything about the body.

If we manage to prove that the antecedent is inconsistent, or the antecedent
does imply the consequent, or the antecedent cannot imply the consequent, then
the computation stops. Otherwise, the `worker` starts again, evaluating the
terms by one step, etc.

[`Language.Pirouette.Example`]: ./src/Language/Pirouette/Example.hs
[`Language.Pirouette.Example.StdLib`]: ./src/Language/Pirouette/Example/StdLib.hs
[`Pirouette.SMT`]: ./src/Pirouette/SMT.hs
[`Pirouette.Symbolic.Eval`]: ./src/Pirouette/Symbolic/Eval.hs
[`Pirouette.Symbolic.Eval.Types`]: ./src/Pirouette/Symbolic/Eval/Types.hs
[`Pirouette.Symbolic.Prover`]: ./src/Pirouette/Symbolic/Prover.hs
[`Pirouette.Term.Syntax.Base`]: ./src/Pirouette/Term/Syntax/Base.hs
[`Pirouette.Transformations`]: ./src/Pirouette/Transformations.hs
