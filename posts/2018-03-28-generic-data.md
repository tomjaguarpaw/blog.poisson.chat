---
title: An old and a new library for generic deriving
---

I have just released
[*generic-data*](https://hackage.haskell.org/package/generic-data-0.1.0.0), a
library for metaprogramming in Haskell using GHC Generics.

One motivation was to refine [the deriving technique I previously wrote
about](http://blog.poisson.chat/posts/2018-03-03-deriving-show-hkt.html)
for various types such as "functor-functor"-style records, generalizing it to
more classes and types while avoiding the hack using incoherent instances.
[This is what the result looks like
now](https://github.com/Lysxia/generic-data/blob/cda5305b8295bc918cf0ebe43057c5feb79b5d57/test/record.hs).

Among other things, *generic-data* has generic implementations of the type
classes found in the standard library *base*. In that respect, it is basically
a *base*-compatible clone of the library *generic-deriving*.

In this post, I want to talk about how it takes advantage of existing
infrastructure in the `GHC.Generics` module to condense some of these generic
implementations to one-liners. ([Here they are, as spoilers or
TL;DR](https://github.com/Lysxia/generic-data/blob/master/src/Generic/Data/Internal/Prelude.hs#L22).)
This is what makes *base* a "library for generic deriving",
or more of one than it may seem at first.

Quick example: a generic `Eq`
=============================

Let's say we want to derive instances of `Eq` with GHC Generics.

```haskell
class Eq a where
  (==) :: a -> a -> Bool
```

A generic implementation `geq` would use the `Generic a` instance to convert
(via `from`) the arguments of type `a` to a uniform *representation* of a type
named `Rep a`, and then calls a function `eqRep` from some class `GEq` of
representations that can be compared for equality.

```haskell
geq :: (Generic a, GEq (Rep a)) => a -> a -> Bool
geq a b = eqRep (from a) (from b)

class GEq r where
  eqRep :: r p -> r p -> Bool
  -- p is a phantom parameter, for reasons not relevant to this post.
```

There would be instances of `GEq` for the "building blocks" of those
representations: `M1`, `(:+:)`, `(:*:)`, `K1`, `U1`, `V1`. That's all
it takes to derive `Eq` generically, although one still needs to define
`GEq` and write these instances.

You may have noticed that `GEq` looks quite like `Eq`, and that similarity
actually extends to their instances. Indeed, we can instead directly use `Eq`
instead to compare representations, and that's how we get this one-liner.

```haskell
-- The phantom parameter makes this implementation a bit pesky.
geq' :: forall a. (Generic a, Eq (Rep a ())) => a -> a -> Bool
geq' a b = from a == (from b :: Rep a ())
```

Generically equivalent instances
================================

Some classes have what I'd call *generically equivalent instances*, which can
be derived with GHC Generics by using instances of the *same* type class
for the "building blocks" of generic representations: `M1`, `(:+:)`,
etc., as opposed to the more general approach of going through a separate
"`G`-prefixed" class. In *base*, classes with generically equivalent instances
include `Eq`, `Ord`, which aren't too exciting, but also `Semigroup` and
`Monoid` (for single-constructor types, i.e., products), for which there isn't
a special deriving mechanism built into GHC.

With `Generic1` type constructors (which many types are not!) we can also
derive in that way `Eq1`, `Ord1`, `Functor`, `Foldable`, `Traversable`, and for
single-constructor types again, `Applicative` and `Alternative`.

As counterexamples, classes which do not have structurally generic instances
include `Read`, `Show`, `Enum`, and `Bounded`, because they depend on
information that needs more work to recover from the generic representations
(number, names, arities of constructors).

However, `Semigroup` and `Monoid` instances are currently missing in the
`GHC.Generics` module. Another idea to work around that was that `Applicative`
also defines monoids if you ignore the phantom parameter. But there is again a
crucially missing `Applicative` instance for `K1`.
[In fact, I've just submitted these instances to
*base*](https://phabricator.haskell.org/D4447), so that won't be a problem
in a few months.
There are also missing `Eq1` and `Ord1` instances, although I haven't gotten
around to implement them in *base*, and they are going to become much less
useful once GHC has quantified constraints anyway.
*generic-data* provides those missing instances as orphans.

Other implementations
=====================

Other implementations of standard type classes can be found in various places,
but you have to know where to look.

- [*semigroups*](https://hackage.haskell.org/package/semigroups-0.18.4/docs/Data-Semigroup-Generic.html)
  defines generic `Semigroup` and `Monoid` via `GSemigroup` and `GMonoid` type
  classes.

- [*transformers-compat*](https://hackage.haskell.org/package/transformers-compat-0.6.0.6/docs/Data-Functor-Classes-Generic.html)
  defines generic `Eq1`, `Ord1`, `Read1` and `Show1` also via separate
  `G`-prefixed classes, and I've shown they are unnecessary for the former two.
  This implementation is arguably impossible to find if you don't know it's
  there.

- [*one-liner-instances*](https://hackage.haskell.org/package/one-liner-instances)
  defines generic instances for many classes (`Semigroup`, `Monoid`, and
  numeric ones like `Num`) using a single class from its parent
  [*one-liner*](https://hackage.haskell.org/package/one-liner) (that's a whole
  other story). It is a more general approach than generically equivalent
  instances, but also requires more dependencies.

It's definitely not necessary to depend on *generic-data* to derive generically
equivalent instances; it may take less effort to just copy the one-liners you need
from it. However, *generic-data* will make it possible to tweak the generic
instances so they can be adapted to fancier types, bringing us ever closer to
fully superseding the ad-hoc deriving strategies in GHC with generic deriving.
