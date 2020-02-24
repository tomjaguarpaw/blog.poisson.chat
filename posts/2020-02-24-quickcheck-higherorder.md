---
title: Testing higher-order properties with QuickCheck
keywords: ["haskell", "libraries", "testing"]
---

I have just released two libraries to enhance QuickCheck for testing
higher-order properties:
[*quickcheck-higherorder*](https://hackage.haskell.org/package/quickcheck-higherorder)
and [*test-fun*](https://hackage.haskell.org/package/test-fun).

This is a summary of their purpose and main features.
For more details, refer to the README and the implementations of the respective
packages.

= Context

This project started from [experiments](https://github.com/Lysxia/checkers-mtl)
to design
[laws for the *mtl* library](https://mail.haskell.org/pipermail/libraries/2019-October/030038.html).
What makes a good law? I still don't know the answer, but there is at least
one sure sign of a bad law: find a counterexample!
That's precisely what property-based testing is useful for.
As a byproduct, if you can't find a counterexample after looking for it,
that is some empirical evidence that the property is valid,
especially if you expect counterexamples to be easy to find.

Ideally we would write down a property, and get some feedback from running it.
Of course, complex applications will require extra effort for worthwhile results.
But I believe that, once we have our property, the cost of entry to just start
running test cases can be reduced to zero, and that many applications may
benefit from it.

QuickCheck already offers a smooth user experience for testing simple
"first-order properties". *quickcheck-higherorder* extends that experience
to *higher-order properties*.

= Summary

A *higher-order property* is a property quantifying over functions. For example:

```haskell
prop_bool :: (Bool -> Bool) -> Bool -> Property
prop_bool f x = f (f (f x)) === f x
```

Vanilla QuickCheck is sufficient to test such properties, provided you know
where to find the necessary utilities. Indeed, simply passing the above
property to the `quickCheck` runner results in a type error:

```haskell
main :: IO ()
main = quickCheck prop_bool  -- Type error!
```

`quickCheck` tries to convert `prop_bool` to a `Property`, but that
requires `Bool -> Bool` to be an instance of `Show`,
which is of course absurd.[^bool]

[^bool]: You could hack something in this case because `Bool` is a small type,
  but that does not scale to arbitrary types.

Instead, functions must be wrapped in the `Fun` type:

```haskell
prop_bool' :: Fun Bool Bool -> Bool -> Property
prop_bool' (Fn f) x = f (f (f x)) === f x

main :: IO ()
main = quickCheck prop_bool'  -- OK!
```

Compounded over many properties, this `Fun`/`Fn` boilerplate is repetitive.
It becomes especially cumbersome when the functions are contained inside
other data types.

*quickcheck-higherorder* moves that cruft out of sight.
The `quickCheck'` runner replaces the original `quickCheck`,
and infers that `(->)` should be replaced with `Fun`.

```haskell
-- The first version
prop_bool :: (Bool -> Bool) -> Bool -> Property
prop_bool f x = f (f (f x)) === f x

main :: IO ()
main = quickCheck' prop_bool  -- OK!
```

== Data and its representation

The general idea behind this is to distinguish the *data* that your application
manipulates, from its *representation* that QuickCheck manipulates. The data
can take any form, whatever is most convenient for the application, but its
representation must be concrete enough so QuickCheck can randomly generate it,
shrink it, and print it in the case of failure.

Vanilla QuickCheck handles the simplest case, where the data is identical to
its representation, and gives up as soon as the representation has a different
type, requiring us to manually modify the property to make the representation
of its input data explicit.
This is certainly not a problem that can generally be automated away,
but the UX here still has room for improvement.
*quickcheck-higherorder* provides a new way to associate data to its
representation, via a type class `Constructible`, which `quickCheck'` uses
implicitly.

```haskell
class (Arbitrary (Repr a), Show (Repr a)) => Constructible a where
  type Repr a :: Type
  fromRepr :: Repr a -> a
```

Notably, we no longer require `a` itself to be an instance of
`Arbitrary` and `Show`. Instead, we put those constraints on an associated type
`Repr a`, which is thus inferred implicitly whenever values of type `a`
are quantified over.

== Testable equality

Aiming to make properties higher-level, more declarative,
the `prop_bool` property above can also be written like this:

```haskell
prop_bool :: (Bool -> Bool) -> Equation (Bool -> Bool)
prop_bool f = (f . f . f) :=: f
```

Where `(:=:)` is a simple constructor. That defers the choice
of how to interpret the equation to the caller of `prop_bool`,
leaving the above specification free of such operational details.

Behind the scenes, this exercises a new type class for
testable equality,[^checkers] `TestEq`, turning equality
into a first-class concept even for higher-order data
(the main examples being functions and infinite lists).

[^checkers]: This also exists in *checkers* as
  [`EqProp`](https://hackage.haskell.org/package/checkers-0.5.2/docs/Test-QuickCheck-Checkers.html#v:-61--45--61-).

```haskell
class TestEq a where
  (=?) :: a -> a -> Property
```

For more details, see
[the README of *quickcheck-higherorder*](https://hackage.haskell.org/package/quickcheck-higherorder#readme).

== Testable higher-order functions

QuickCheck offers a `Fun` type to express properties of arbitrary
functions.[^koen] However, `Fun` is limited to first-order functions.
An example of type that cannot be represented is `Cont`.

[^koen]: *Shrinking and showing functions (functional pearl)*,
  by Koen Claessen, in Haskell Symposium 2012.

The library *test-fun* implements a generalization of `Fun` which can represent
higher-order functions. Any order!

It's a very simple idea at its core, but it took quite a few iterations
to get the design right. The end result is a lot of fun.
The implementation exhibits the following characteristics,
which are not obvious a priori:

- like in QuickCheck's version, the type of those *testable functions* is a
  single GADT, i.e., a closed type, whereas an open design might seem more
  natural to account for user-defined types of inputs;

- the core functions to apply, shrink, and print testable functions
  impose no constraints on their domains;

- *test-fun* doesn't explicitly make use of randomness, in fact, it doesn't
  even depend on QuickCheck! The library is parameterized by a functor `gen`,
  and almost all of the code only depends on it being an `Applicative` functor.
  There is (basically) just one function (`cogenFun`) with a `Monad` constraint
  and with a random generator as an argument.

As a consequence, *test-fun* can be reused entirely to work with Hedgehog.
However, unlike with QuickCheck, some significant plumbing is required, which
is [work in progress](https://github.com/Lysxia/hedgehog-higherorder).
*test-fun* cannot just be specialized to Hedgehog's `Gen` monad; it will only
work with QuickCheck's `Gen`,[^lazy] so we currently have to break into
Hedgehog's internals to build a compatible version of the "right" `Gen`.

[^lazy]: It must be lazy, in the right way. A random monad built
  on top of lazy `State` is no good either.
  As of now, QuickCheck's `Gen` is the only monad I know which is useful
  for *test-fun*.

*test-fun* implements core functionality for the internals of libraries like
*quickcheck-higherorder*.
Users are thus expected to only depend directly on
*quickcheck-higherorder* (or the WIP *hedgehog-higherorder* linked above).

=== Generators as traversals

*test-fun* only requires an `Applicative` constraint in most cases,
because intuitively a testable function has a fixed "shape":
we represent a function by a big table mapping every input to an output.
To generate a random function, we can generate one output independently for
each input, collect them together using `(<*>)`, and build a table purely using
`(<$>)`.

However this view of "functions as tables" does not extend to higher-order
functions, which may only make finite observations of their infinite inputs.
A more general approach is to represent functions as decision
trees over their inputs. "Function as tables" is the special case where those
trees are *maximal*, such that there is a one-to-one correspondence between
leaves and inputs. However, maximal trees don't always exist. Then a random
generator must preemptively terminate trees, and that requires stronger
constraints such as `Monad` (intermediate ones like `Alternative` or
`Selective` might be worth considering too).

For more details, see
[the README of *test-fun*](https://hackage.haskell.org/package/test-fun#readme).

= Conclusion

These libraries are already used extensively in my project
[*checkers-mtl*](https://github.com/Lysxia/checkers-mtl),
which is where most of the code originated from.

One future direction on my mind is to port this to Coq,
as part of the [QuickChick](https://github.com/QuickChick/QuickChick) project.
I'm curious about the challenges involved in making the implementation
provably total, and in formalizing the correctness of testing higher-order
properties.

I'm always looking for opportunities to make testing as easy as possible.
I'd love to hear use cases for these libraries you can come up with!
