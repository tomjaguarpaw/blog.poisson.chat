---
title: "Note to myself: a theory of injective arrows"
keywords: [haskell, bidirectional]
---

This post starts off from work that I have yet to publish so it won't make any
sense.

When programming bidirectionally with monadic profunctors, we assume that there
is a "round-tripping" property on values of type ``p u u``, such that: if
``m :: p u u`` is a round-trip, and ``f :: u -> p v v`` is such that ``f u`` is
a round-trip for all ``u``, and ``f`` is an *injective arrow* with *sagittal
inverse* ``f' :: v -> Maybe u``, then ``(f' =: m) >>= f`` is a round-trip.

In practice, free use of ``(>>=)`` and ``(=:)`` makes the code looks very
nice, but this leaves open the problem of ensuring that ``f`` is an
injective arrow, and that it is being used with its sagittal inverse ``f'``.
The *Invertible Syntax Descriptions* paper has a similar problem with
*partial isomorphisms*, which they address with a small combinator library.
Can we do something similar here?

The focus of this post is thus combinators that preserve round-tripping
properties entirely such that, if one starts with a set of primitive
round-trips, and only uses these combinators, then the result must be
a round-trip.

\begin{code}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}

module Injective.Arrows where

import Control.Applicative
import Control.Arrow (Arrow, Kleisli)
import Control.Monad
import Profunctor.Monad
\end{code}

Combinators for injective arrows
================================

A type for injective arrows and their inverses seems like a natural starting
point. It shall be made opaque to users, whereas we liberally
deconstruct it to define our combinators.

\begin{code}
-- Most (all?) of the time, v ~ v'
data IArrow p u v v' = IArrow
  { arrow :: u -> p v v'
  , inverse :: v -> Maybe u
  }
\end{code}

Then, instead of ``(f' =: m) >>= f``, one should write ``m >>=+ f``,
but now ``f`` carries its inverse at all times.

\begin{code}
(>>=+)
  :: (Cofunctor p, First p ~ Kleisli Maybe, Monad1 p)
  => p u u -> IArrow p u v v' -> p v v'
m >>=+ IArrow f f' = withMonad ((f' =: m) >>= f)
\end{code}

Lifting Kleisli arrows
----------------------

Any Kleisli arrow maps to an injective arrow by adding its input
to the output.

\begin{code}
liftArr
  :: (Cofunctor p, First p ~ Kleisli Maybe, Functor1 p)
  => (u -> p v v') -> IArrow p u (u, v) (u, v')
liftArr k = IArrow
  (\u -> withFunctor ((,) u <$> snd =. k u))
  (\(u, _) -> return u)
\end{code}

As a special case of this, noting that ``p v v`` is isomorphic to
``() -> p v v``:

\begin{code}
constArr :: p v v' -> IArrow p () v v'
constArr m = IArrow (\() -> m) (\_ -> return ())
\end{code}

This is useful to write the equivalent of ``(>>)``.

\begin{code}
(>>+)
  :: (Cofunctor p, First p ~ Kleisli Maybe, Monad1 p)
  => p () () -> p v v' -> p v v'
m >>+ n = m >>=+ constArr n

-- m >> n = m >>= \_ -> n
\end{code}

Category
--------

Categories look nice. I can imagine `(>>>)` being useful.

\begin{code}
iarrow0 :: forall p u. Monad1 p => IArrow p u u u
iarrow0 = IArrow
  (\u -> withMonad (return u))
  return

(>>>)
  :: (Cofunctor p, First p ~ Kleisli Maybe, Monad1 p)
  => IArrow p u v v -> IArrow p v w' w -> IArrow p u w' w
IArrow a1 i1 >>> IArrow a2 i2 = IArrow
  (\u -> withMonad ((i2 =: a1 u) >>= a2))
  (i1 <=< i2)
\end{code}

Constructors
------------

This convenient pattern adapts applicative style to monadic profunctors.

\begin{code}
(<.>)
  :: (Cofunctor p, Arrow (First p), Applicative1 p)
  => p x a -> p y b -> p (x, y) (a, b)
mfst <.> msnd = withApplicative
  ((,) <$> fst =. mfst <*> snd =. msnd)
\end{code}

This pattern for products can be generalized to other constructors with some
generic programming.

Arrow-like
----------

The ``Arrow`` interface gives some inspiration for a few more constructs
involving products.

\begin{code}
second
  :: (Cofunctor p, Arrow (First p), Functor1 p)
  => IArrow p u v v -> IArrow p (b, u) (b, v) (b, v)
second (IArrow a i) = IArrow
  (\(b, u) -> withFunctor ((fmap ((,) b) . (=.) snd) (a u)))
  (\(b, v) -> fmap ((,) b) (i v))

(***)
  :: (Cofunctor p, Arrow (First p), Applicative1 p)
  => IArrow p u1 v1 v1 -> IArrow p u2 v2 v2
  -> IArrow p (u1, u2) (v1, v2) (v1, v2)
IArrow a1 i1 *** IArrow a2 i2 = IArrow
  (\(u1, u2) -> a1 u1 <.> a2 u2)
  (\(v1, v2) -> liftA2 (,) (i1 v1) (i2 v2))

(&&&)
  :: (Cofunctor p, Arrow (First p), Applicative1 p)
  => IArrow p u v1 v1 -> IArrow p u v2 v2
  -> IArrow p u (v1, v2) (v1, v2)
IArrow a1 i1 &&& IArrow a2 _ = IArrow
  (\u -> a1 u <.> a2 u)
  (\(v1, _) -> i1 v1)  -- Broken symmetry
\end{code}

Pattern matching
----------------

Dually to the above construct for product types, there is also one for
sums. Actually, there are two viable approaches. The one that
mirrors ``(<.>)`` best is to use ``Alternative``.

\begin{code}
(<||>)
  :: (Cofunctor p, First p ~ Kleisli Maybe, Alternative1 p)
  => p x a -> p y b -> p (Either x y) (Either a b)
ma <||> mb = withAlternative
  (   Left  <$> fromLeft  =: ma
  <|> Right <$> fromRight =: mb)

fromLeft :: Either a b -> Maybe a
fromLeft (Left x) = Just x ; fromLeft (Right _) = Nothing

fromRight :: Either a b -> Maybe b
fromRight (Right y) = Just y ; fromRight (Left _) = Nothing
\end{code}

Or we can pattern-match on an explicit parameter,
this looks like the dual to ``(***)``, i.e., ``(+++)``.

\begin{code}
(<?>)
  :: (Cofunctor p, First p ~ Kleisli Maybe, Functor1 p)
  => (a -> p x u) -> (b -> p y v)
  -> (Either a b -> p (Either x y) (Either u v))
(mu <?> mv) ab = withFunctor $ case ab of
  Left  a -> Left  <$> fromLeft  =: mu a
  Right b -> Right <$> fromRight =: mv b
\end{code}

We can wrap ``(<?>)`` for injective arrows.

\begin{code}
(+++)
  :: (Cofunctor p, First p ~ Kleisli Maybe, Functor1 p)
  => IArrow p a x u -> IArrow p b y v
  -> IArrow p (Either a b) (Either x y) (Either u v)
IArrow a i +++ IArrow b j = IArrow
  (a <?> b)
  (\xy -> case xy of
    Left  x -> Left  <$> i x
    Right y -> Right <$> j y)
\end{code}

Conclusion
----------

These combinators work with generic sums and products with ``(,)`` and ``Either``.
We need at least some way to restructure them to user-defined types.
Moreover, in this post I kept the profunctor presentation of bidirectional
programs, but in practice the input and output types will always be the same
in ``p u u``.

We end up with something that overlaps greatly with *Invertible Syntax
Descriptions*, the main addition being a monadic extension with the
``IArrow`` type.

This still feel unsatisfactory compared to the unbridled power of ``Monad``,
but it is at odds with the strongest guarantees one may require in
some situations.

- How much expressiveness are we giving up?

- Are there more interesting and useful constructs?

- How can we improve the syntax when using these combinators?
  I'm starting to think about a way to exploit Haskell's ``RebindableSyntax``
  extension in a very non-standard way, though it might lead nowhere.

I hope this will become clearer once I try to (re)write various bidirectional
programs using them.
