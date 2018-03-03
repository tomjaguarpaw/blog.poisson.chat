---
title: Deriving Show for higher-kinded types
---

In [a previous post](http://blog.poisson.chat/posts/2017-10-21-making-a-show.html),
I used *reflection* to resolve constraints from derived `Show` instances.
But this method is still quite cumbersome because every constraint must be handled
separately, and there can be as many of them as there are fields in our types.

Recently the problem of deriving `Show` was brought up on this month's
[Hask Anything thread on reddit](https://www.reddit.com/r/haskell/comments/80xmpi/monthly_hask_anything_march_2018/dv0gk27/),
and I found a better solution.

We want to derive `Show` for the following record type
([a functor functor](https://www.benjamin.pizza/posts/2017-12-15-functor-functors.html)):

```haskell
data Bar f = Bar
  { bar1 :: f String
  , bar2 :: f Int }
```

If we try to derive it simply...

```haskell
deriving instance Show (Bar f)
```

... GHC first generates some code that looks roughly like this[^1]...

```haskell
instance Show (Bar f) where
  show (Bar b1 b2) = "Bar (" ++ show b1 ++ ") (" ++ show b2 ++ ")"
```

... in particular, it applies `show` to each field; this requires
the constraints `Show (f String)` and `Show (f Int)`, and they
cannot be satisfied. Compilation fails.

We could add these constraints to the instance context. This works, but this
solution doesn't scale well to larger records with many types of fields.

```haskell
deriving instance (Show (f String), Show (f Int)) => Show (Bar f)
```

What we really mean here is that there is an instance
`Show a => Show (f a)`, parametric in `a`, and indeed the
[quantified constraints](https://ghc.haskell.org/trac/ghc/wiki/QuantifiedConstraints)
proposal will soon solve this problem.

However, here is a solution without quantified constraints, that can be used
with currently released versions of GHC.

**The goal** is to define an instance...

```haskell
instance Show1 f => Show (Bar f) where
  show = (???)  -- To do
```

... where `Show1` is the closest approximation of the quantified constraint
`forall a. Show a => Show (f a)` we have at the moment.
A function `show1` is available to render a value of type `f a` using a
`Show1 f` constraint[^2].


```haskell
show1 :: (Show1 f, Show a) => a -> String
```

**The idea** is that `deriving` produces the code we want for the most part, and
the result depends only on the "head" of the instance, `Bar` here, so that the
following declaration generates the same instance body (sketched above)
for any `X` and `Y`.

```haskell
deriving instance X => Show (Bar Y)
```

These unknowns `X` and `Y` may be different from `Show1 f` and `f` respectively;
we can still use that instance to then define the final instance
`Show1 f => Show (Bar f)` as follows...

```haskell
instance Show1 f => Show (Bar f) where
  show bar = show (convert bar)
```

... under the following conditions:

1. the constraint `X` is entailed by the context `Show1 f`;
   we might as well be as general as possible, so `X = Show1 f`;

2. we can convert a `Bar f` to a `Bar Y`, i.e., there is a
   function `convert :: Bar f -> Bar Y`.

The function `convert` should not modify the information contained in the
record fields. This requirement is well met by
[`coerce`](https://hackage.haskell.org/package/base-4.10.1.0/docs/Data-Coerce.html#v:coerce).
It literally does not touch its argument; it is a function between types
that have the same runtime representation, and at runtime it behaves
like the identity function.
For `Bar f` to be coercible to `Bar Y`, the arguments `f` and `Y` must have
the same representation. We can't modify the abstract `f`. Instead, we must
pick `Y` to be a newtype:

```haskell
newtype Showing f a = Showing { unwrap :: f a }
```

Looking at the derived instance, we thus have `show (b1 :: Showing f String)`
and `show (b2 :: Showing f Int)`, and we expect the result to be equivalent to
`show1 (unwrap b1 :: f String)` and `show1 (unwrap b2 :: f Int)`. This tells us
exactly how to implement `Show` for `Showing`.

```haskell
instance (Show1 f, Show a) => Show (Showing f a) where
  show = show1 . unwrap
```

Note that this instance is not at all what the compiler would derive. In
particular, the `Showing` constructor is not rendered. The `Showing` type is not
as much a proper data type as it is a trick to transform a `Show` constraint
to a `Show1` constraint.

We can now ask GHC to derive the following instance
(more about `INCOHERENT` below):

```haskell
deriving instance {-# INCOHERENT #-} Show1 f => Show (Bar (Showing f))
```

From that, we obtain the desired instance:

```haskell
instance Show1 f => Show (Bar f) where
  show = show . (coerce :: Bar f -> Bar (Showing f))
```

And that's it!

Here is [a condensed version of the code in this
post](http://lpaste.net/363089).

---

Little wrinkles
---------------

=== Just one function

The `show . (coerce :: _)` pattern with an explicit type annotation can be
condensed further into a single definition:

```haskell
showing
  :: forall h f
  .  (Coercible (h f) (h (Showing f)), Show (h (Showing f)))
  => h f -> String
showing = show . (coerce :: h f -> h (Showing f))
```

We can now refactor the last instance:

```haskell
instance Show1 f => Show (Bar f) where
  show = showing
```

=== Overlapping instances

The two instances `Show (Bar (Showing f))` and `Show (Bar f)` overlap.
Without any annotation, that is not allowed.
Marking the former as `OVERLAPPING` helps (or equivalently, the latter as
`OVERLAPPABLE`), but then the latter instance will only be picked when `f`
is instantiated to not unify with the first. This means that functions that are
polymorphic in `f` may incur a constraint `Show (Bar f)`, rather than the
simpler `Show1 f`. Instead, marking the former instance as `INCOHERENT` allows
the compiler to ignore the overlap and just pick whichever instance is most
convenient (usually the latter): `Showing` is only an internal type for the
purposes of deriving `Show`, and shouldn't be used elsewhere, so it is okay to
assume that `f` does not ever unify with `Showing g`.

[^1]:
  The derived code actually defines
  [`showsPrec`](https://hackage.haskell.org/package/base-4.10.1.0/docs/Prelude.html#t:Show)
  first to deal with precedence levels, and then `show` just wraps it.

[^2]:
  Actually there is
  [`showsPrec1`](https://hackage.haskell.org/package/base-4.10.1.0/docs/Data-Functor-Classes.html#v:showsPrec1)
  to replace/implement `showsPrec`.
