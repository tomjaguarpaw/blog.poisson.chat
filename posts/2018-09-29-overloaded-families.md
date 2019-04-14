---
title: Overloaded type families
keywords: [haskell, haskell-tricks, libraries, type families]
---

Overloading
===========

Overloading is to give the same name to different implementations.
In Haskell, type classes enable overloading of terms. For example, the two
functions `map` and `(.)` are generalized by the concept of "functors":

```haskell
class Functor f where
  fmap :: (a -> b) -> (f a -> f b)

instance Functor [] where
  fmap :: (a -> b) -> ([a] -> [b])
  fmap = map

instance Functor ((->) r) where
  fmap :: (a -> b) -> ((r -> a) -> (r -> b))
  fmap = (.)
```

What about type families?
=========================

We can also define a type-level `fmap` simply as:

```haskell
type family FMap (m :: a -> b) (x :: f a) :: f b
```
(Enable the extensions `TypeFamilies` and also
[`TypeInType`](https://downloads.haskell.org/~ghc/latest/docs/html/users_guide/glasgow_exts.html#kind-polymorphism-and-type-in-type).)

"Type class instances of `Functor`" become simply "type family instances of
`FMap`". For lists:

```haskell
-- FMap :: (a -> b) -> ([a] -> [b])
type instance FMap m '[] = '[]
type instance FMap m (v ': vs) = m v ': FMap m vs
```

And `FMap` for type constructors (`r -> a`) can be defined using
[`Data.Functor.Compose`](https://hackage.haskell.org/package/base-4.11.1.0/docs/Data-Functor-Compose.html).
Compare this to the instance `Functor ((->) r)` above:

```haskell
-- FMap :: (a -> b) -> ((r -> a) -> (r -> b))
type instance FMap m n = Compose m n
```

Whereas at the term level, functions can be defined by pattern-matching
on their arguments, at the type level, type families can be defined by
pattern-matching not only on their arguments but also their kinds.
Notice that in the last type family instance above, we actually don't
inspect `m` and `n`, but the type family will check whether the kind
of `n` is an arrow `r -> a` in order to use that instance.

We can similarly write a lazy instance of `FMap` for `Proxy`:

```haskell
-- FMap :: (a -> b) -> Proxy a -> Proxy b
type instance FMap m p = 'Proxy
```

The resulting mechanism resembles type classes, but the ergonomics are not
quite the same. One difference is that there is no type class constraint on
`FMap`, because constraints are not a thing at that level. Whereas wrongly
applying `fmap` may cause a "missing instance" error, incorrect usage of `FMap`
just gives us a stuck term, and we may somehow have to look for our mistake in
a huge type-level expression dumped by the compiler. That gap might be filled by
recent work on ["constrained type families"](https://arxiv.org/abs/1706.09715).

Nevertheless, it's quite cool that overloading at the type level Just Works™.

Here, this is a simple type family to keep it simple, but it applies to
first-class families too. Thanks to [*isovector* for pointing
out](https://github.com/Lysxia/first-class-families/pull/1#issuecomment-420716814)
this feature to me!
