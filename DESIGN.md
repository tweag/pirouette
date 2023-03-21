Pirouette's Design
==================

Languages
---------

### Pirouette's genericity

Pirouette attempts to be generic in the input language by only assuming that it
is System F-like. Anyone can then come and define their instance of
`LanguageBuiltins`, which is Pirouette's way of defining the constants, builtin
terms and builtin types of a language. The definition of the classes can be
found in [`Pirouette.Term.Syntax.Base`]. For a simple, concrete instantiation of
a language, you might want to check [the example language]. For a more involved
one, you might want to check [the support for Plutus IR][plutus intermediate
representation].

[`Pirouette.Term.Syntax.Base`]: ./src/Pirouette/Term/Syntax/Base.hs

### The example language

[the example language]: #the-example-language

The example language is the only instance of a language included in Pirouette.
It is a simple functional language supporting higher-order types with explicit
type annotations, basic types (booleans, integers, strings) with their
associated operators, algebraic datatypes and pattern-matching. The definition
of the language is done by providing the `LanguageBuiltins` instance. You will
find all the heavy work in [`Language.Pirouette.Example`].

[`Language.Pirouette.Example`]: ./src/Language/Pirouette/Example.hs

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

The hardest part has been done. It is now simple to define a list of integers --
say `1`, `2`, `3` -- and sum over them.
```haskell
myList : List Integer
myList = Cons @Integer 1 (Cons @Integer 2 (Cons @Integer 3 (Nil @Integer)))

myListTotal : Integer
myListTotal =
  foldr
    @Integer
    @Integer
    (\(x : Integer) (y : Integer) . x + y)
    0
    myList
```

For more examples, check out the standard library for the example language in
[`Language.Pirouette.Example.StdLib`]. The standard library also comes with a
quasi-quoter of its own allowing you to leverage it in your code should you want
it:
```haskell
myProgram :: PrtUnorderedDefs Ex
myProgram = [progWithStdLib|
  totalSum : List Integer -> Integer
  totalSum =
    foldr
      @Integer
      @Integer
      (\(x : Integer) (y : Integer) . x + y)
      0
|]
```

[`Language.Pirouette.Example.StdLib`]: ./src/Language/Pirouette/Example/StdLib.hs

### Plutus Intermediate Representation

[plutus intermediate representation]: #plutus-intermediate-representation

To run Pirouette on Plutus Intermediate Representation scripts, one has to use
the [pirouette-plutusir library].

[pirouette-plutusir library]: https://github.com/tweag/pirouette-plutusir

Transformations
---------------

Evaluation
----------
