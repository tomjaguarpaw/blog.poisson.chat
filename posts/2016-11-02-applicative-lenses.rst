---
title: Applicative Lenses
---

This is written in Literate Haskell.

\begin{code}
module Applicative.Lenses where

import Control.Applicative
import Control.Monad
import Data.Functor
import Data.Monoid

import Bidirectional.Serialization.Two (Codec(..)) -- 2016-10-13
import Bidirectional.Serialization.Classes
\end{code}

I'm trying to figure out a relationship between the abstractions I previously
brought up and lenses.

\begin{code}
data Lens s t a b = Lens
  { get :: s -> a
  , put :: b -> s -> t
  }

type Lens' s a = Lens s s a a

idL :: Lens' s s
idL = Lens id const

unitL :: Lens' s ()
unitL = ignorePut

ignorePut :: Lens s s () b
ignorePut = Lens (const ()) (const id)
\end{code}

There is a similarity to codecs. We import the definition of ``Codec`` from
`2016-10-13`_.

.. _2016-10-13: 2016-10-13-more-bidirectional-serialization.html

Straightforward representation
==============================

Define the following wrapper types for ``get`` and ``put``.

\begin{code}
type MLensR = (->)
type MLensW s = Const (Endo s)
  -- Applicative but not Monad.

lensR :: (s -> a) -> MLensR s a
lensR = id

unMLensR :: MLensR s a -> s -> a
unMLensR = id

lensW :: (s -> s) -> MLensW s a
lensW = Const . Endo

unMLensW :: MLensW s a -> s -> s
unMLensW = appEndo . getConst

type MLens s = Codec (MLensR s) (MLensW s)
\end{code}

Then ``MLens s a a`` is isomorphic to ``Lens' s a``.
The isomorphism can in fact be generalized between
``MLens s b a`` and ``Lens s s a b``.

\begin{code}
fromLens' :: Lens' s a -> MLens s a a
fromLens' = fromLens

toLens' :: MLens s a a -> Lens' s a
toLens' = toLens

fromLens :: Lens s s a b -> MLens s b a
fromLens (Lens get put) = Codec
  (lensR get)
  (lensW . put)

toLens :: MLens s b a -> Lens s s a b
toLens (Codec parse produce) = Lens
  (unMLensR parse)
  (unMLensW . produce)
\end{code}

Based on that construction, we now have an ``Applicative`` interface for
composing lenses "horizontally", combining their views together.

\begin{code}
pairP
  :: (Profunctor p, Applicative (p (b, b')))
  => p b a -> p b' a' -> p (b, b') (a, a')
pairP p p' = (,)
  <$> fst =. p
  <*> snd =. p'

pair :: MLens s b a -> MLens s b' a' -> MLens s (b, b') (a, a')
pair = pairP

pairLens :: Lens s s a b -> Lens s s a' b' -> Lens s s (a, a') (b, b')
pairLens l l' = toLens $ pair (fromLens l) (fromLens l')
\end{code}

However, their good behavior is not guaranteed.

\begin{code}
oops :: Lens' s a -> Lens' s (a, a)
oops l = pairLens l l

-- PutGet fails.
oopsFails = get l (put l a s) /= a
  where
    l = oops idL
    a = (True, False)
    s = False
\end{code}

The problem here is that the lenses *overlap*, so the views may not be modified
independently.

Conversely, ``pairLens l l'`` is well-behaved if
``l :: Lens s a`` and ``l' :: Lens s a'`` are well-behaved
and **non-overlapping**, i.e., if for all ``s``, ``a`` and ``a'``,
putting one view does not affect the other:

.. code:: haskell

  get l (put l' a' s) == get l s
  get l' (put l a s) == get l' s

We actually only need one equality to hold to ensure the good behavior
of ``pairLens l l'``, but determining which one (here, the second) relies on a
careful examination of the order of updates in ``pair``.

Detecting conflicts
===================

Given two lenses ``l :: Lens s a`` and ``l' :: Lens s a'``, possibly
overlapping, and some source ``s``, we say that a pair ``(a, a')``
is a **consistent update** of ``s`` through ``l`` and ``l'`` if:

.. code:: haskell

  get l (put l' a' s) == get l s
  get l' (put l a s) == get l' s

Two lenses are non-overlapping if and only if all updates through
them are consistent.

For more flexibility, we shall allow ourselves to create partial lenses,
which allow updates of overlapping views as long as they are consistent
(actually, with a generalized definition of consistency).

We can "record observations" in order to forbid inconsistent modifications
as in *Applicative Bidirectional Programming with Lenses*\ [#abpl]_, using a
more elaborate ``MLensW2`` type.

.. [#abpl]

  *Applicative Bidirectional Programming with Lenses*, K. Matsuda, M. Wang.
  https://kar.kent.ac.uk/49084

\begin{code}
newtype MLensW2 s a = MLensW2
  { runMLensW2 :: s -> (s -> Bool) -> Maybe (s, s -> Bool, a)
  }

instance Functor (MLensW2 s) where
  fmap = liftA

instance Applicative (MLensW2 s) where
  pure a = MLensW2 $ \s p -> Just (s, p, a)
  (<*>) = ap

instance Monad (MLensW2 s) where
  MLensW2 x_ >>= f = MLensW2 $ \s p -> do
    (s', p', x) <- x_ s p
    (s'', p'', y) <- runMLensW2 (f x) s' p'
    return (s'', p'', y)
\end{code}

``MLensW2`` is a composition of ``State (s, s -> Bool)`` and ``Maybe``.

``sourceW`` fetches the ``s`` component of the state.

\begin{code}
sourceW :: MLensW2 s s
sourceW = MLensW2 $ \s p -> pure (s, p, s)
\end{code}

``putW`` updates the source through a partial lens.
``putW`` is unsafe to use alone in general, with the risk of defining
ill-behaved lenses. However, careful and fine grained use of ``putW`` can help
optimize composite lenses by avoiding redundant checks.

\begin{code}
-- PLens' defined below.
putW :: PLens' s a -> a -> MLensW2 s ()
putW l a = MLensW2 $ \s p -> do
  s' <- put l a s
  pure (s', p, ())
\end{code}

``assertW`` checks that the updated source is consistent with previous
observations and modifications.

\begin{code}
assertW :: MLensW2 s ()
assertW = MLensW2 $ \s p ->
  guard (p s) $> (s, p, ())
\end{code}

``matchW`` adds a another consistency constraint preventing a view of the
source to be modified.

\begin{code}
matchW :: Eq w => (s -> w) -> w -> MLensW2 s ()
matchW get w = MLensW2 $ \s p ->
  pure (s, \s' -> p s' && get s' == w, ())
\end{code}

We have an isomorphism between ``MLens2`` and lenses with a partial ``put``.

\begin{code}
type MLens2 s = Codec (MLensR s) (MLensW2 s)
type PLens' s a = Lens s (Maybe s) a a

fromLens2 :: Eq a => PLens' s a -> MLens2 s a a
fromLens2 l = Codec
  (get l)
  (\a -> putW l a *> assertW *> matchW (get l) a $> a)

toLens2 :: MLens2 s b a -> Lens s (Maybe s) a b
toLens2 (Codec get produce) = Lens get put
  where
    put b s = fmap fst3 (runMLensW2 (produce b) s (const True))

fst3 :: (a, b, c) -> a
fst3 (s, _, _) = s
\end{code}

We can also observe values in the source/state, without writing anything.
Modifying a previously observed value is an error.

\begin{code}
observe :: Eq w => (s -> w) -> MLens2 s () w
observe parse = Codec parse produce
  where
    produce () = observeW parse

observeW :: Eq w => (s -> w) -> MLensW2 s w
observeW get = do
  s <- sourceW
  let w = get s
  matchW get w
  pure w
\end{code}

A functor from lenses to functions serves as "vertical" composition.

\begin{code}
lift :: Lens' s a -> MLens2 z s s -> MLens2 z a a
lift l (Codec parse produce) = Codec
  (get l . parse)
  (\a -> do
    z <- sourceW
    let s = parse z
    produce (put l a s)
    pure a
  )

-- A generalized version, though less efficient.
lift_ :: Lens s t a b -> MLens2 z t s -> MLens2 z b a
lift_ l (Codec parse produce) = Codec
  (get l . parse)
  (\b -> do
    z <- sourceW
    let s = parse z
    s <- produce (put l b s)
    pure (get l s)
  )
\end{code}
