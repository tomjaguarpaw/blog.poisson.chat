---
title: A quick tour of generic-random
description: Advertisement for generic programming
---

Metaprogramming with Generics in Haskell allows us to derive many functions and
types directly from newly declared types. Here is a quick toy demonstration of
using [generic-random](https://hackage.haskell.org/package/generic-random) to
derive `arbitrary` from the
[QuickCheck](https://hackage.haskell.org/package/QuickCheck) library.
I won't go into any implementation details; to learn about generics in general,
[check out this tutorial](https://www.stackbuilders.com/tutorials/haskell/generics/)!

Starters
--------

Below is a type `MyType` with a simple, handwritten
[`Arbitrary`](https://hackage.haskell.org/package/QuickCheck-2.10.1/docs/Test-QuickCheck.html#t:Arbitrary)
instance.

```haskell
{-# LANGUAGE InstanceSigs, TypeApplications #-}
import Test.QuickCheck

data MyType
  = OneThing Int
  | TwoThings Double String

instance Arbitrary MyType where
  arbitrary :: Gen MyType
  arbitrary = oneof [
    OneThing <$> arbitrary @Int,
    TwoThings <$> arbitrary @Double <*> arbitrary @String]
```

(Also showing off the
[`InstanceSigs`](https://downloads.haskell.org/~ghc/latest/docs/html/users_guide/glasgow_exts.html#instance-signatures-type-signatures-in-instance-declarations)
and
[`TypeApplications`](https://downloads.haskell.org/~ghc/latest/docs/html/users_guide/glasgow_exts.html#visible-type-application)
extensions. These annotations are inferable here, but helpful!
Especially the former.)

We generate either `OneThing` or `TwoThings` with probability 1/2 each,
and use other existing `Arbitrary` instances to fill their respective fields.

Now, let us add a constructor to `MyType`:

```haskell
data MyType
  = OneThing Int
  | TwoThings Double String
  | ThreeThings (Maybe Integer) [()] (Bool -> Word)

instance Arbitrary MyType where
  arbitrary :: Gen MyType
  arbitrary = oneof [
    OneThing <$> arbitrary @Int,
    TwoThings <$> arbitrary @Double <*> arbitrary @String]
```

That compiles ~~therefore it's correct~~ but the new constructor is not
generated by `arbitrary` yet! Of course, we must also remember to update any
code involving the modified `MyType`.

```haskell
data MyType
  = OneThing Int
  | TwoThings Double String
  | ThreeThings (Maybe Integer) [()] (Bool -> Word)

instance Arbitrary MyType where
  arbitrary :: Gen MyType
  arbitrary = oneof [
    OneThing <$> arbitrary @Int,
    TwoThings <$> arbitrary @Double <*> arbitrary @String,
    ThreeThings <$> arbitrary <*> arbitrary <*> arbitrary]
    -- N.B.: QuickCheck can generate functions
```

(The lazy programmer gives up spelling out all the field types of `ThreeThings`.)

Main course
-----------

Typing `arbitrary` so often gets repetitive;
here enters
[generic-random](https://hackage.haskell.org/package/generic-random).

```haskell
-- In addition to the first LANGUAGE/import header
{-# LANGUAGE DeriveGeneric #-}
import GHC.Generics
import Generic.Random

data MyType
  = OneThing Int
  | TwoThings Double String
  | ThreeThings (Maybe Integer) [()] (Bool -> Word)
  deriving Generic

instance Arbitrary MyType where
  arbitrary :: Gen MyType
  arbitrary = genericArbitraryU
  -- Uniform distribution of MyType constructors
```

In contrast to the previous snippets, `genericArbitraryU` automatically
adapts to changes in the numbers of constructors and fields of `MyType`.

We may find `OneThing` a boring enough test case that we should generate it
less often, here with probability 1/9.

```haskell
instance Arbitrary MyType where
  arbitrary :: Gen MyType
  arbitrary = genericArbitrary (1 % 4 % 4 % ())
  -- 1/(1+4+4): OneThing
  -- 4/(1+4+4): TwoThings
  -- 4/(1+4+4): ThreeThings
```

Now, forgetting to update the distribution when the number of constructor
changes would result in a compile-time error. It's also possible to
statically enforce the correspondence between weights and constructor
names (the declaration order must match too).

```haskell
instance Arbitrary MyType where
  arbitrary :: Gen MyType
  arbitrary = genericArbitrary
    ((1 :: W "OneThing") %
     (4 :: W "TwoThings") %
     (4 :: W "ThreeThings") %
     ())
```

Suddenly, we realize `Nothing` is not a thing, so
`ThreeThings Nothing [()] fromInteger` is not really "three things".

To implement the requirement that no `Nothing` is generated, last year we
would have had to go back to the fully handwritten generator (with
[`frequency`](https://hackage.haskell.org/package/QuickCheck-2.10.1/docs/Test-QuickCheck.html#v:frequency)
instead of
[`oneof`](https://hackage.haskell.org/package/QuickCheck-2.10.1/docs/Test-QuickCheck.html#v:oneof)
to preserve the distribution).

```haskell
instance Arbitrary MyType where
  arbitrary :: Gen MyType
  arbitrary = frequency [
    (1, OneThing <$> arbitrary @Int),
    (4, TwoThings <$> arbitrary @Double <*> arbitrary @String),
    (4, ThreeThings <$> (Just <$> arbitrary) <*> arbitrary <*> arbitrary)]
```

But now, since generic-random-1.1, we can say: "for any field of type
`Maybe Integer`, use this generator; otherwise use `arbitrary`, as before".

```haskell
-- Heterogeneous list of generators, of length 1, with cons (:@).
custom :: GenList '[Maybe Integer]
custom = (Just <$> arbitrary) :@ Nil

instance Arbitrary MyType where
  arbitrary :: Gen MyType
  arbitrary = genericArbitraryG custom (1 % 4 % 4 % ())
```

If that is too heavy handed, we can also mention specific fields by name, when
they have one (there is an example at the end of
[this "tutorial module"](https://hackage.haskell.org/package/generic-random-1.1.0.1/docs/Generic-Random-Tutorial.html)).

We are reaching the end of this tour.
[A compilable version of that last snippet.](https://github.com/Lysxia/generic-random/blob/master/examples/tour.hs)

N.B.
----

Random generation for testing is a largely open topic. generic-random
implements a very simple and specific kind of random generators, and it is not
always applicable: depending on the type and distribution of constructors, it
may not terminate within a reasonable time, and many applications need
much more structured generators to achieve the best coverage.

Dessert (Conclusion)
--------------------

Other than just indulging in our laziness when writing code, automating
boilerplate-writing has benefits that may lighten the burden of maintenance:

- we can't get the boilerplate wrong if we don't write it,
  and the boilerplate may rewrite itself when types changes
  (e.g., we can't forget to generate a constructor; that is admittedly
  hyperbolic, only certain kinds of mistakes are actually prevented);

- not only that, it might not even be necessary to *know* how to write the
  boilerplate to get something working
  (here, a newcomer could get generators and play with the rest of QuickCheck
  without having to do any monadic programming with `Gen`, although more
  documentation seems necessary to put that into practice);

- we can optimize the boilerplate by changing the one piece of code that
  generates it, instead of the many places where it would be duplicated
  (e.g., `frequency` and `oneof` are the easiest things to use but call
  *recursive* functions on mostly static lists, which are thus not optimized
  away by GHC; a generic library can transparently use a more efficient
  implementation for all users to benefit).

Feel free to make a pull request or open an issue if you'd like to see some
new option in generic-random or any other improvement!

P.S.
----

generic-random changed a lot since its creation. The initial
implementation derived Boltzmann samplers, which are heavier in complexity
and dependencies; that can now be found in the
[boltzmann-samplers](https://hackage.haskell.org/package/boltzmann-samplers)
library (I'm slowly working on a `GHC.Generics` version instead of SYB).
The now simpler generic-random doesn't have as nice probabilistic guarantees
as for Boltzmann samplers, but it is actually not clear how a globally
uniform-ish distribution improves random testing and whether that is worth the
extra complexity. Even with a naive distribution of constructors:

- small types (i.e., with few inhabitants) are quickly covered;

- for large types, we still generate a good variety of test cases quickly;

- anyway, what is the uniform (or actually, "sizewise uniform" for Boltzmann
  samplers) distribution for `Double`? For functions with infinite domain?

Moreover, if you really need a uniform distribution, take a look at
[testing-feat](https://hackage.haskell.org/package/testing-feat)!
([So far I found it's much more efficient than Boltzmann samplers.](https://github.com/Lysxia/generic-random/issues/6))