---
title: Typeclasses for bidirectional serialization
---

This is written in Literate Haskell.

\begin{code}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE RankNTypes #-}

module Bidirectional.Serialization.Classes
  ( Parsing (..)
  , Printing (..)
  , Profunctor (..)
  , Functor (..)
  , Applicative (..)
  , Alternative (..)
  , Monad (..)
  , Functor1 (..)
  , Applicative1 (..)
  , Alternative1 (..)
  , Monad1 (..)
  , MonadPlus1 (..)
  , Dict (..)
  , (=.)
  , replicatePA
  , traversePA
  ) where

import Control.Applicative
import Control.Monad
import Data.Constraint -- constraints
import Data.Profunctor -- profunctors
\end{code}

This merges previous developments I made about bidirectional serialization,
to improve *Pickler Combinators*, the codec package, and *Invertible Syntax
Descriptions*.

Two types and their instances
=============================

The main trick, as originally performed by codec, is to distinguish the
covariant occurence of ``a`` in ``Parser a`` and the contravariant one in
``Printer a``. Thus we parameterize our interface over a type
``p :: * -> * -> *``.

It can be instantiated with a parsing context ``get :: * -> *`` at
``Parsing get``. A ``Parsing get b a`` is a parser ``get a`` of
values of type ``a``. (``b`` is ignored in this direction.)

\begin{code}
newtype Parsing get b a = Parsing { parsing :: get a }
  deriving (Functor, Applicative, Alternative, Monad)
\end{code}

It can also be instantiated with a printing context ``put :: * -> *`` at
``Printing put``. A ``Printing put b a`` is a printer ``b -> put a``, which
takes a value of type ``b``, from which it extracts, prints and returns a value
of type ``a``.

\begin{code}
newtype Printing put b a = Printing { printing :: b -> put a }

instance Functor put => Functor (Printing put b) where
  fmap f (Printing put) = Printing (fmap f . put)

instance Applicative put => Applicative (Printing put b) where
  pure x = Printing (\_ -> pure x)
  Printing f <*> Printing x = Printing (liftA2 (<*>) f x)

instance Alternative put => Alternative (Printing put b) where
  empty = Printing (\_ -> empty)
  Printing a <|> Printing a' = Printing (liftA2 (<|>) a a')

instance Monad put => Monad (Printing put b) where
  Printing a_ >>= f = Printing (\b -> a_ b >>= \a -> printing (f a) b)
\end{code}

Thus ``Parsing`` and ``Printing`` are a form of monad transformers,
though they don't have the right kind to be instances of ``MonadTrans``.

The types of parsers and printers ``get`` and ``put`` are provided by users.
They should at least be instances of ``Profunctor`` and ``Applicative``; they
may also be ``Alternative`` or ``Monad``.

This interface is thus flexible and works with parsers of various expressive
powers.

Mapping over two type parameters
--------------------------------

Another valuable typeclass is ``Profunctor``.

``rmap`` is basically a synonym of ``fmap``, mapping over the second (right)
parameter of ``p :: * -> * -> *``. ``lmap`` maps over the first (left) one, but
flips the arrows.

.. code:: haskell

  rmap :: Profunctor p => (a -> a') -> p b a -> p b a'
  lmap :: Profunctor p => (b' -> b) -> p b a -> p b' a

For ``Parsing``, ``lmap`` does not modify its argument, only its type.

\begin{code}
instance Functor get => Profunctor (Parsing get) where
  lmap _ (Parsing get) = Parsing get
  rmap = fmap
\end{code}

For ``Printing``, ``lmap`` is function composition.

\begin{code}
instance Functor put => Profunctor (Printing put) where
  lmap f (Printing put) = Printing (put . f)
  rmap = fmap
\end{code}

A cool looking synonym
++++++++++++++++++++++

\begin{code}
(=.) :: Profunctor p => (b' -> b) -> p b a -> p b' a
(=.) = lmap

infixr 7 =.
\end{code}

Typeclasses for two-parameter types
-----------------------------------

These express that ``p a`` is an instance of ``C (p a)`` for all ``a``.
They avoid an explosion of constraints when instances for multiple
instantiations of ``a`` are required.

\begin{code}
class Functor1 p where
  functor1 :: forall a. Dict (Functor (p a))

  default functor1 :: Functor (p a) => Dict (Functor (p a))
  functor1 = Dict

class Applicative1 p where
  applicative1 :: forall a. Dict (Applicative (p a))

  default applicative1 :: Applicative (p a) => Dict (Applicative (p a))
  applicative1 = Dict

class Alternative1 p where
  alternative1 :: forall a. Dict (Alternative (p a))

  default alternative1 :: Alternative (p a) => Dict (Alternative (p a))
  alternative1 = Dict

class Monad1 p where
  monad1 :: forall a. Dict (Monad (p a))

  default monad1 :: Monad (p a) => Dict (Monad (p a))
  monad1 = Dict

class MonadPlus1 p where
  monadPlus1 :: forall a. Dict (MonadPlus (p a))

  default monadPlus1 :: MonadPlus (p a) => Dict (MonadPlus (p a))
  monadPlus1 = Dict
\end{code}

Of course, ``Parsing`` and ``Printing`` are instances.

\begin{code}
instance Functor get => Functor1 (Parsing get)
instance Applicative get => Applicative1 (Parsing get)
instance Alternative get => Alternative1 (Parsing get)
instance Monad get => Monad1 (Parsing get)

instance Functor put => Functor1 (Printing put)
instance Applicative put => Applicative1 (Printing put)
instance Alternative put => Alternative1 (Printing put)
instance Monad put => Monad1 (Printing put)
\end{code}

Pattern matching
----------------

This looks useful, not yet sure what for.

\begin{code}
instance Functor get => Choice (Parsing get) where
  left' (Parsing get) = Parsing (fmap Left get)
  right' (Parsing get) = Parsing (fmap Right get)

instance Applicative put => Choice (Printing put) where
  left' (Printing put) =
    Printing (either (fmap Left . put) (pure . Right))
  right' (Printing put) =
    Printing (either (pure . Left) (fmap Right . put))
\end{code}

Extra combinators
=================

Special variants of ``replicate`` and ``traverse`` must be defined
which handle the ``b`` type parameter correctly.
These combinators produce parsers and printers for lists of length
fixed by the first argument (``Int`` or ``[c]``).
Trying to print a list of different length is an error.

Replicate
---------

\begin{code}
replicatePA
  :: (Profunctor p, Applicative (p [b]))
  => Int -> p b a -> p [b] [a]
replicatePA 0 _ = pure []
replicatePA n p =
  (:)
    <$> head =. p
    <*> tail =. replicatePA (n - 1) p
\end{code}

Traverse
--------

\begin{code}
traversePA
  :: (Profunctor p, Applicative (p [b]))
  => (c -> p b a) -> [c] -> p [b] [a]
traversePA _ [] = pure []
traversePA f (c : cs) =
  (:)
    <$> head =. f c
    <*> tail =. traversePA f cs
\end{code}
