---
title: "Definitional lawfulness: proof by inspection testing"
keywords: [haskell, testing]
---

Can we prove `Monad` instances lawful using [*inspection-testing*][inspection]?

[inspection]: https://hackage.haskell.org/package/inspection-testing

In this very simple experiment, I've tried to make it work for the common
monads found in *base* and *transformers*.

Main takeaways:

- Associativity almost holds for all of the considered monads,
  with the main constraint being that the transformers must be applied
  to a concrete monad such as `Identity` rather than an abstract `m`.
- The identity laws were relaxed to hold "up to eta-expansion".
- `[]` cheats using rewrite rules.
- This is a job for CPP.

[The source code is available in this gist.](https://gist.github.com/Lysxia/ff7bfd2e3c64c5dd3f4201df06341282)

= Setup

Let's see how to use inspection testing through the first example of
the associativity law. It works similarly for the other two laws.

Here's the associativity law we are going to test. I prefer this
formulation since it makes the connection with monoids and categories obvious:

```
((f >=> g) >=> h)   =   (f >=> (g >=> h))
```

To use inspection testing, turn the two sides of the equation into functions:

```haskell
assoc1, assoc2 :: Monad m => (a -> m b) -> (b -> m c) -> (c -> m d) -> (a -> m d)
assoc1 f g h = (f  >=>  g) >=>  h
assoc2 f g h =  f  >=> (g  >=>  h)
```

These two functions are not the same if we don't know anything about `m` and
`(>=>)`. So choose a concrete monad `m`. For example, `Identity`:

```haskell
assoc1, assoc2 :: (a -> Identity b) -> (b -> Identity c) -> (c -> Identity d) -> (a -> Identity d)
assoc1 f g h = (f  >=>  g) >=>  h
assoc2 f g h =  f  >=> (g  >=>  h)
```

GHC will be able to inline the definition of `(>=>)` for `Identity` and
simplify both functions.

== The inspection test

Using the *inspection-testing* library, we can now assert that the simplified
functions in GHC Core are in fact equal:

```haskell
{-# LANGUAGE TemplateHaskell #-}

inspect $ 'assoc1 ==- 'assoc2
```

This test is executed at compile time.
The quoted identifiers `'assoc1` and `'assoc2` are the names of the functions
as values (different things from the functions themselves), that the function
`inspect` uses to look up their simplified definitions in GHC Core.
The `(==-)` operator asserts that they must be the same, while ignoring
coercions and type lambdas---constructs of the GHC Core language which will be
erased in later compilation stages.

== Copy-paste programming with CPP

These tests can be tedious to adapt for each monad.
The main change is the monad name; another concern is to use different function names
for each test case. The result is a fair amount of code duplication:

```haskell
assoc1Identity, assoc2Identity
  :: (a -> Identity b) -> (b -> Identity c) -> (c -> Identity d) -> (a -> Identity d)
assoc1Identity f g h = (f  >=>  g) >=>  h
assoc2Identity f g h =  f  >=> (g  >=>  h)
inspect $ 'assoc1Identity ==- 'assoc2Identity

assoc1IO, assoc2IO
  :: (a -> IO b) -> (b -> IO c) -> (c -> IO d) -> (a -> IO d)
assoc1IO f g h = (f  >=>  g) >=>  h
assoc2IO f g h =  f  >=> (g  >=>  h)
inspect $ 'assoc1IO ==- 'assoc2IO
```

The best way I found to handle the boilerplate is a CPP macro:

```haskell
{-# LANGUAGE CPP #-}

#define TEST_ASSOC(NAME,M,FFF) \
assoc1'NAME, assoc2'NAME :: (a -> M b) -> (b -> M c) -> (c -> M d) -> a -> M d ; \
assoc1'NAME = assoc1 ; \
assoc1'NAME = assoc2 ; \
inspect $ 'assoc1'NAME FFF 'assoc2'NAME
```

It can be used as follows:

```haskell
TEST_ASSOC(Identity,Identity,==-)
TEST_ASSOC(Maybe,Maybe,==-)
TEST_ASSOC(IO,IO,==-)
TEST_ASSOC(Select,Select,=/=)
```

Template Haskell is the other obvious candidate, but it is not as convenient:

- There's no syntax to parameterize quotes by function names; at best, they can be
  wrapped in a pattern or expression quote, but type declarations require raw
  names; I object to explicitly constructing the AST.
- The `inspect` function must execute after the two given functions
  are defined; these two steps cannot be done in a single splice.

= Associativity

The inspection tests pass for almost all of the monads mentioned above.
Three tests fail. One (`Writer`) could be fixed with a little tweak.
The other two (`Select` and `Product`) can probably be fixed, I'm not sure.

Nevertheless, thinking through why the other tests succeed can also be
an instructive exercise.

== Writer

The writer monad consists of pairs, where one component can be thought of
as a "log" produced by the computation. All we really need is a way to
concatenate logs, so logs can formally be elements of an arbitrary monoid:

```haskell
newtype Writer log a = Writer (a, log)

instance Monoid log => Monad (Writer log) where
  return a = Writer (a, mempty)
  Writer (a, log) >>= k =
    let Writer (b, log') = k a in
    (b, log <> log')
```

The writer monad does not pass any of the three inspection tests
out-of-the-box
(associativity, left identity, right identity)
because the order of composition using `(>=>)` is reflected after
inlining in the order of composition using `(<>)`,[^mappend]
which GHC cannot reassociate in general.

[^mappend]: `(<>)` is also called `mappend`, and at the level of Core there
  is an unfortunately visible difference, which is why the source code
  uses `mappend`.

A simple fix is to instantiate the monoid `w` to a concrete one
whose operations do get reassociated, such as `Endo e`.
While that makes the test less general technically, it can also be
argued that this is such a localized change that we should still be able to
derive from it a fair amount of confidence that the law holds in the general
case.

= Maybe

The fact that `Maybe` passes the test is a good illustration of
one extremely useful simplification rule applied by GHC:
the "case-of-case" transformation.

Expand both sides of the equation:

```
((f >=> g) >=> h)   =   (f >=> (g >=> h))
```

The left-hand side is a `case` expression whose
scrutinee is another `case` expression:

<figure id="figure-A">
<figcaption>Figure A</figcaption>
```haskell
\a ->
  case
    case f a of
      Nothing -> Nothing
      Just b -> g b
  of
    Nothing -> Nothing
    Just c -> h c
```
</figure>

The right-hand side is a `case` expression
containing a `case` expression in one of its branches:

<figure id="figure-B">
<figcaption>Figure B</figcaption>
```haskell
\a ->
  case f a of
    Nothing -> Nothing
    Just b ->
      case g b of
        Nothing -> Nothing
        Just c -> h c
```
</figure>

The code in the latter [Figure B](#figure-B) tends to execute faster.
One simple reason for that is that if `f a` evaluates to `Nothing`,
the whole expression will then immediately reduce to `Nothing`, whereas
[Figure A](#figure-A) will take one more step to reduce the inner
`case` before the outer `case`.
Computations nested in `case` scrutinees also tend to require additional
bookkeeping when compiled naively.

The key rule, named "case-of-case", stems from remarking that
eventually, a case expression reduces to one of its branches.
Therefore, when it is surrounded by some context---an outer `case`
expression---we might as well apply the context to the branches directly.
[Figure A](#figure-A) transforms into the following:

<figure id="figure-C">
<figcaption>Figure C</figcaption>
```haskell
\a ->
  case f a of
    Nothing ->
      case Nothing of
        Nothing -> Nothing
        Just c -> h c
    Just b ->
      case g b of
        Nothing -> Nothing
        Just c -> h c
```
</figure>

And the first branch reduces to `Nothing`.

This transformation is not always a good idea to apply,
because it duplicates the context, once for each branch of the inner `case`.
That rule pays off when some of these branches are constructors and when the
context is a `case`, so the transformation turns them into "case of
constructor" which can be simplified away.

== IO

The representation of `IO` in GHC Core looks like a strict state monad.

```haskell
data IO a = IO# (State# RealWorld -> (# a, State# RealWorld #))
```

However, the resemblance between `IO` and `State` is purely syntactic,
viewing Haskell programs only as terms to be rewritten, rather than
mathematical functions "from states to states".
The token that is being passed around as the "state" in `IO` has no meaning
other than as a gadget to maintain the evaluation order required by the
semantics of `IO`.
It is merely an elegant coincidence that the implementation of `IO` matches
perfectly the mechanics of the state monad.

== The continuation monad transformer

Out of all the examples considered in this experiment,
the continuation monad is the only example of a monad transformer applied
to an abstract monad `m`. All the other transformers are specialized to the
identity monad.

That is because the other monad transformers use the underlying monad's
`(>>=)` in their own definition of `(>>=)`, and that blocks simplification.
`ContT` is special: its `Monad (ContT r m)` instance does not even use a `Monad
m` instance. That allows it to compute where other monad transformers cannot.

This observation also suggests only using concrete monads as a strategy for
optimizations to take place. The main downside is the lack of modularity. Some
computations are common to many monads (e.g., traversals), and it also seems
desirable to not have to redefine and recompile them from scratch for every new
monad we come up with.

== The list monad

For the list monad, `(>>=)` is `flip concatMap`:

```haskell
concatMap :: (a -> [b]) -> [a] -> [b]
```

`concatMap` is a recursive function, and GHC does not inline those.
Given that, it may be surprising that it passes the inspection test.
This is thanks to bespoke rewrite rules in the standard library to
implement list fusion.

You can confirm that by defining your own copy of the list monad and see that
it fails the test.

Another idea was to disable rewrite rules (`-fno-enable-rewrite-rules`),
but this breaks even things unrelated to lists for mysterious reasons.

= Right identity: eta

`pure` to the right of `(>>=)` cancels out.

```
(u >>= pure) = u
```

The right-hand side is very easy to simplify: there is nothing to do.

The problem is that on the left-hand side, we need to do some work to
combine `u` and `pure`, and that almost always some of that work remains
visible after simplification. Sadly, the main culprit is laziness.

For example, in the `Reader` monad, `u >>= pure` reduces to the following:

```haskell
Reader (\r -> runReader u r)
```

If we ignore the coercions `Reader` and `runReader`, then we have:

```haskell
\r -> u r
```

That is the eta-expanded[^eta] form of `u`. In Haskell, where `u` might be
undefined but a lambda is not undefined, `\r -> u r` is not equivalent to `u`.
To me, the root of the issue is that we can use `seq` on everything, including
functions, and that allows us to distinguish `undefined` (blows up) from
`\x -> undefined x` (which is equivalent to `\x -> undefined`; does not blow up
until it's applied).
A perhaps nicer alternative is to put `seq` in a type class which can only be
implemented by data types, excluding various functions and computations.
That would add extra constraints on functions that do use strictness on abstract
types, such as `foldl'`. It's unclear whether that would be a flaw or a feature.

[^eta]: Paradoxically, it is sometimes called "eta-reduction" even if
  it makes the term look "bigger", because it also makes them look more "regular".

So `u` and `\r -> u r` are not always the same, but really because of a single
exception, when `u` is undefined. So they are still *kinda* the same.
Eta-expansion can only make an undefined term somewhat less undefined, but
arguably not in any meaningful way.

This suggests to relax the equality relation to allow terms
to be equal "up to eta-expansion":

```haskell
f = g    if    (\x -> f x) = (\x -> g x)
```

Furthermore, eta-expansion is an idempotent operation:

```haskell
\r -> (\r1 -> u r1) r = \r -> u r
```

So to compare two functions, we can expand both sides,
and if one side was already eta-expanded, it will reduce back to itself.

We can write the test case as follows:

```haskell
lid1, lid2 :: Reader r a -> Reader r a
lid1 x = eta x
lid2 x = eta (x >>= pure)

eta :: Reader r a -> Reader r a
eta (Reader u) = Reader (\r -> u r)

inspect $ 'lid1 ==- 'lid2
```

== Generalized eta

The notion of "eta-expansion" can be generalized to other types
than function types, notably for pairs:

```haskell
eta :: (a, b) -> (a, b)
eta xy = (fst x, snd y)
```

The situation is similar to functions:
`xy` may be undefined, but `eta xy` is never undefined.[^neg]

[^neg]: There is in fact a deeper analogy. Pairs can be seen as (dependent) functions
with domain `Bool`. Pairs and functions can also be viewed in terms of a more general
notion of "negative types", "codata".

This suggests the definition of a type class for generalized eta-expansion:

```haskell
class Eta a where
  -- Law: eta x = x   modulo laziness
  eta :: a -> a

instance Eta (a, b) where
  eta ~(x, y) = (x, y)   -- The lazy pattern is equivalent to using projections

instance Eta (Reader r a) where
  eta (Reader f) = Reader (\r -> f r)
```

The handling of type parameters here is somewhat arbitrary: one could also try
to eta-expand the components of the pair for instance.

Two more interesting cases are `ContT` and `IO`.

For `ContT`, we not only expand `u` to `\k -> u k`,
but we also expand the continuation to get `\k -> u (\x -> k x)`.

```haskell
instance Eta (ContT r m a) where
  eta (ContT u) = ContT (\k -> u (\x -> k x))
```

It is also possible, and necessary, to eta-expand `IO`, whatever that means.

```haskell
instance Eta (IO a) where
  eta u = IO (\s -> case IO f -> f s)

-- Note: eta is lazier than id.
--   eta (undefined :: IO a) /= (undefined :: IO a)
```

= Left identity: eta, but also sharing

`pure` on the left of `(>>=)` cancels out.

```
(pure x >>= k) = k x
```

The left identity has the same issue with eta-expansion that we just described for the
right identity. It also has another problem with sharing.

In the `Reader` monad for example, `(pure x >>= k)` first expands to---ignoring
the coercions for clarity:

```haskell
\r -> k x r
```

However, GHC also decides to extrude the `k x` because it doesn't depend on `r`:

```haskell
let u = k x in \r -> u r
```

The details go a little over my head, but I found a cunning workaround in the
magical function `GHC.Exts.inline` in the `Eta` instance for `Reader`:

```haskell
instance Eta (ReaderT e m a) where
  eta u = ReaderT (\x -> runReaderT (inline u) x)
```

= Definitional lawfulness

When these inspection tests pass, that is proof that the monad laws hold.

If we reduce what the compiler does to inlining and simplification, then
on the one hand, not all monads can be verified that way (e.g., lists that
don't cheat with rewrite rules);
on the other hand, when the proof works, it proves a property stronger
than "lawfulness".

Let's call it "definitional lawfulness": we say that the laws hold "by
definition", with trivial simplification steps only.
There is some subjectivity about what qualifies as a "trivial" simplification;
it boils down to how dumb the compiler/proof-checker can be.
Nevertheless, what makes definitional lawfulness interesting is that:

1. it is immediately inspection-testable and the test is actually a proof,
   unlike with random property testing (QuickCheck) for example;

2. if the compiler can recognize the monad laws by mere simplification, that very
   likely implies that it can simplify the overhead of more complex monadic
   expressions.

That implication is not obviously true, it's actually false in practice without some
manual help, but definitional lawfulness gets us some of the way there.
A sufficient condition is for inlining and simplification to be confluent
("the order of simplification does not matter"),
but inlining being limited by heuristics jeopardizes that property
because those heuristics depend on the order of simplifications.

Custom rewrite rules also make the story more complicated, which is
why I just consider it cheating, and prefer structures that enable fusion by
simplification, such as difference lists and other continuation-passing tricks.
