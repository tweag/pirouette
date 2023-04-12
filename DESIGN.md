Pirouette's Design
==================

This document gives an overview of Pirouette, and
pointers to get familiar with the code. As such, it contains three parts.

1. The [first part][languages] describes how Pirouette supports several input
   languages as well as two languages that are particularly relevant to us: [the
   example language] and Plutus IR – [Plutus intermediate
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

Pirouette can process any System F-like language. More precisely, users can come
and define their instance of `LanguageBuiltins`, which is Pirouette's way of
defining the constants, builtin terms and builtin types of a language. The
definition of the classes can be found in [`Pirouette.Term.Syntax.Base`].

Unless preprocessed in a way or another, Pirouette languages feature explicit
type anotations, no namespacing and the definitions of terms are considered to
be all mutually recursive. In fact, almost all of Pirouette works on the type
`PrtUnorderedDefs lang` which describes a set of “Pirouette unordered
definitions“ for a given `lang`uage — think of a Haskell module where order does
not matter and terms can reference one another freely.

For a simple instantiation of a language, you might want to check [the example
language]. For a more involved one, you might want to check [the support for
Plutus IR][plutus intermediate representation].

### The example language

[the example language]: #the-example-language

The example language is the only instance of a language included in Pirouette.
It is a simple functional language supporting higher-order types with explicit
type annotations, basic types (booleans, integers, strings) with their
associated operators, algebraic datatypes and pattern-matching. You will find
all the heavy work in [`Language.Pirouette.Example`]. The example language also
has a concrete syntax heavily inspired by Haskell. Consider for instance:

```haskell
addone : Integer -> Integer
addone x = x + 1

addtwo : Integer -> Integer
addtwo x = x + 2
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
It is now possible to define a `sum` function, a
list of integers – say `1`, `2`, `3` – and apply `sum` over them.

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

[transformations]: #transformations

_Warning: This section has been written by a non-expert based on information
gathered here and there. There might be missing, outdated, irrelevant or even
wrong information. We believe it should still give a good starting point to
anyone willing to understand Pirouette's transformations._

A transformation in Pirouette goes from internal representation to internal
representation. In general, transformations aim at simplifying the input term by
getting rid of some features, while keeping the semantics unchanged.

In a typical setting, an input term will go through several transformations
before reaching its final form that can be symbolically evaluated. In
particular, some transformations assume that they take place after another one;
additionally, transformations should preserve the invariant of previous
transformations. The dependencies between transformations are formalised in
Haskell's type system; we refer the reader to the upcoming Tweag blog post
“Type-safe data processing pipelines” for more information on this.

Transformations live in [`Pirouette.Transformations`].

### Conversion to prenex normal form

This transformation puts signatures into some kind of a normal form where type
arguments all go before the term arguments. This is required by monomorphisation.

### Removal of excessive arguments

When this transformation sees a destructor that is applied to more arguments than
there are branches (and the scrutinee), it moves the extra argument inside the
branches. Indeed, if this is the case, then the branches really return a
function, and the extra (aka excessive) arguments are really arguments to this
returned function. As an example, consider (with type applications omitted):

```haskell
match_Nat n
  (\b -> if b then 0 else 1)
  (\n b -> if b then n else 0)
  True
```

`match_Nat` takes the scrutinee and two branches, yet it has three parameters. So,
what this transformation does is pushing True inside branches, yielding:

```haskell
match_Nat n
  (if True then 0 else 1)
  (\n -> if True then n else 0)
```

### Monomorphisation

Monomorphisation removes polymorphism, which we need out of the way both for
some other transformations to be possible and to make the work of SMT solvers
easier. It is straightforward except for recursive aspects. For instance, it
transforms

```haskell
map (+ 1) [1, 2, 3]
```

into

```haskell
mapInt (+ 1) [1, 2, 3]
```

where `mapInt` only works with `Int`s.

It is not obvious whether the current algorithm terminates on arbitrary System F
programs, but it does in practice. The monomorphisation needs also to happen for
constructors and destructors and types, that is it needs to happen for anything
polymorphic.

We originally considered monomorphising only high-order functions, because SMT
solvers can usually work with first-order polymorphic functions; it is however
simpler to monomorphise everything.

### Eta expansion

Eta-expansion turns partially applied functions to fully applied ones under a
λ-abstraction. For instance, `map f` would become `λ xs. map f xs`. This
transformation is most useful to prepare for defunctionalisation. It is also a
straightforward transformation, although there has some technical details to
handle; for instance if there are functions as arguments.

### Defunctionalisation

This transformation removes all higher-order functions and replace them with
labels. It is required for higher-order functions such as `fold`, for instance.
The label in question denotes the body of a specific function as well as the
free variables it refers to. Such a transformation is easy in an untyped
setting, but it becomes hard when types are included, and in System F in
particular. In that case, one needs to create some record data type to embed
free variable types and have separate record types for different function
signatures, since it is otherwise impossible to write the `apply` function. The
constructor of this type describes which function is called and is basically the
aforementioned label. There is a data type as well as an `apply` function for
each function type among functions that need to be defunctionalised, as opposed
to a single of such function in the untyped case.

For a general introduction to defunctionalisation, we refer the user to
[Wikipedia](https://en.wikipedia.org/wiki/Defunctionalization).

### Elimination of mutually recursive functions

This transformation breaks mutually recursive function groups by inlining
non-recursive functions in the group in other definitions until reaching a
fixpoint, and putting the resulting definitions in the proper order. For
instance, given:

```haskell
f x = op1 (f (x-1)) (g x)
g x = h x + 2
h x = f (x - 3)
```

it produces:

```haskell
f x = op1 (f (x-1)) (f (x - 3) - 2)
h x = f (x - 3)
g x = h x + 2
```

This transformation does not always succeed. For example, it would fail on the
following:

```haskell
f x = f x + g x
g x = f x + g x
```

However, it works in practice on the subset of System F that we have encountered
so far.

Symbolic Engine
---------------

[symbolic engine]: #symbolic-engine

The symbolic engine is split into three main parts: an SMT prover, as well as
all the administrative work to communicate with it, Pirouette's _[symbolic
evaluator]_, and Pirouette's _[symbolic prover]_. We describe these three
aspects in the following sub-sections.

### SMT prover

As is classic in symbolic engines, Pirouette relies on SMT provers to do the
hard work. These provers are used in two different ways. They help pruning
branches of execution that are actually unreachable, and they help deciding
whether the user's statements/questions actually hold.

Pirouette relies on [smtlib-backends] for the communication with its SMT prover
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

Morally speaking, though, forgetting the `lang` type parameters and assuming
that `WeightedList`s are just lists, this monad simply represent functions of
type:

```haskell
SymEvalEnv -> SymEvalSt -> [(a, SymEvalSt)]
```

taking an environment and a [state][`SymEvalSt`] and returning a list of states,
as well as potential return values. It returns a list because symbolic
evaluation may branch and explore different paths.

#### The key function — `symEvalOneStep`

[`symEvalOneStep`]: #the-key-function--symEvalOneStep

The key function in this module is `symEvalOneStep`, whose type is the
following:

```haskell
symEvalOneStep ::
  forall lang .
  SymEvalConstr lang =>
  TermMeta lang SymVar ->
  WriterT Any (SymEval lang) (TermMeta lang SymVar)
```

Once again, morally speaking, forgetting the `WriterT Any` layer, the `lang`
type parameters and replacing `TermMeta lang SymVar` by just `Term`, this
function has type `Term -> SymEval Term`. One can then think of this as a
function of type:

```haskell
SymEvalEnv -> (Term, SymEvalSt) -> [(Term, SymEvalSt)]
```

Such a function takes a term in the input language and a symbolic evaluation
state. It tries to apply one step of beta-reduction to the term, which may yield
zero, one or several potential terms and updated states.

As an example, let us assume that our input term is the body of the `foldr`
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
pattern matching, and therefore it would return two pairs `(Term, SymEvalSt)`:

1. In the first pair, the `Term` would be `e` itself and the state would be
   updated to account for the fact that we now know that `l == Nil`.

2. In the second pair, the `Term` would be `f x (foldr f e xs)` and the state
   would be updated to account for the fact the we now have two more variables,
   `x` and `xs`, that are an integer and a list of integers respectively, and an
   additional constraint, `l == Cons x xs`.

The whole symbolic execution consists in running this one step over and over
again until it is not possible to reduce the terms anymore. In the example
above, our first term/state is now blocked because it reached a built-in value
-- an integer -- which cannot be reduced further. The second term/state is not
blocked because one can replace `f` by its definition and continue unfolding
from there. The `WriterT Any` layer actually comes into play here: its only goal
is to carry a boolean value tracking whether a step of evaluation was taken.
Technically, it is possible for anyone to write their wrapper around
`symEvalOneStep`; the default ones are breadth-first, and the way the `SymEval`
monad is design clearly encourages this kind of algorithm.

#### The symbolic evaluation state — `SymEvalSt`

[`SymEvalSt`]: #the-symbolic-evaluation-state--symevalst

 Defined in [`Pirouette.Symbolic.Eval.Types`], the symbolic state basically
contains the following:

1. A context of variables, that is a map from variable names to their types.
   This context is typically called Γ in literature, and `gamma` in the code.

2. A set of constraints linking variables together, for instance `l == Cons x
   xs`, `k != Nil` or `x == 7`. It is implemented with a [union-find]-based data
   structure.

3. Statistics on the execution, for instance the number of case analyses that took
   place. Despite the name, those statistics can have an important impact on the
   behaviour of the engine because they are observed to decide whether to stop
   the execution or not.

It also contains some extra fields necessary for administrative reasons. Those field
names are prefixed by `sest` in the code.

[union-find]: https://en.wikipedia.org/wiki/Disjoint-set_data_structure

#### The symbolic evaluation environment — `SymEvalEnv`

[`SymEvalEnv`]: #the-symbolic-evaluation-environment--symevalenv

Defined in [`Pirouette.Symbolic.Eval`], the symbolic environment contains the
following:

1. A set of definitions in which to evaluate the term. This is a value of type
   `PrtUnorderedDefs lang`, that is a set of mutually-recursive definitions. For
   instance, if your term is `foldr @Integer @Integer (\(x : Integer) (y :
   Integer) . x + y) 0 l`, then `foldr` and `l` have to come from somewhere, and
   it will probably be the example language's standard library augmented with
   the definition of the list of integers `l`, and that would be the set of
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
   sestConstructors stat > 50` that stops after 50 constructor unfoldings.

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

Concretely, `proveRaw` takes a `Problem`, does all the administrative work of
extracting the `xs` from the body, creating corresponding symbolic variables,
preparing the terms, and then calls `worker`, where all the actual work happens.

`worker` takes the three aforementioned terms as input and evaluates them all by
one step. We refer the reader to [`symEvalOneStep`] for what this means
precisely. If any of the three terms is stuck, that is if no more reductions are possible,
then `worker` attempts to see if the properties above hold.
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
