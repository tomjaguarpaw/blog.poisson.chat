---
title: Towards Monadic Bidirectional Serialization
---

This is written in Literate Haskell.

\begin{code}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE InstanceSigs #-}

module Bidirectional.Serialization where

import Control.Applicative

import Data.Bool (bool)
import Data.Binary (Binary(..), Get)
import Data.Binary.Get (runGet)
import Data.Binary.Put (runPut, PutM)
import Data.ByteString.Lazy (ByteString)
import Data.Profunctor

-- Intentional synonyms of undefined.

(...) :: omittedForBrevity
(...) = (...)

(???) :: can'tSolveThis
(???) = (???)
\end{code}

Recently I came across the *codec_* package. It is a library to write a
serializer and a deserializer as a single bidirectional artefact.

.. _codec: https://hackage.haskell.org/package/codec

It extends the functional pearl *Pickler Combinators*, an earlier
elementary solution by Andrew J. Kennedy (2004).

I've been trying to push further the ideas of these two.

The basics: Pickler Combinators
===============================

In this section I summarize the Pickler Combinators paper.

The ``UP`` *(un)pickler* type ("``PU``" in the pearl) consists of an
Unpickler (deserializer) and a Pickler (serializer).
The two components are parameterized over contexts ``r`` and ``w`` for unpickling
(reading) and pickling (writing) respectively.

\begin{code}
data UP r w a = UP
  { unpickle :: r a
  , pickle :: a -> w ()
  }
\end{code}

The types ``Get`` and ``PutM`` from the binary package are examples of contexts for
``UP``. The ``Binary`` typeclass implies an (un)pickler for every instance.

\begin{code}
type BinaryUP = UP Get PutM

binaryUP :: Binary a => BinaryUP a
binaryUP = UP get put

-- Deserialize
-- > runGet :: Get a -> ByteString -> a
binaryUnpickle :: BinaryUP a -> ByteString -> a
binaryUnpickle = runGet . unpickle

-- Serialize
-- > runPut :: PutM () -> ByteString
binaryPickle :: BinaryUP a -> a -> ByteString
binaryPickle up = runPut . pickle up
\end{code}

There are combinators, to (un)pickle products by concatenation:

\begin{code}
pairUP
  :: (Applicative r, Applicative w)
  => UP r w a -> UP r w b -> UP r w (a, b)
pairUP aUP bUP = UP
  { unpickle = liftA2 (,) (unpickle aUP) (unpickle bUP)
  , pickle = \(a, b) -> pickle aUP a *> pickle bUP b
  }

-- Infix synonym.
(>|)
  :: (Applicative r, Applicative w)
  => UP r w a -> UP r w b -> UP r w (a, b)
(>|) = pairUP
\end{code}

To (un)pickle sums:

\begin{code}
altUP
  :: Alternative r
  => UP r w a -> UP r w b -> UP r w (Either a b)
altUP aUP bUP = UP
  { unpickle =
      Left <$> unpickle aUP <|>
      Right <$> unpickle bUP
  , pickle = either (pickle aUP) (pickle bUP)
  }
\end{code}

The one above assumes that ``a`` and ``b`` have disjoint picklings,
so that they can be distinguished by an unpickler failing.
A more straightforward way to pickle sums is to precede their picklings with a
tag:

\begin{code}
eitherUP
  :: (Monad r, Applicative w)
  => UP r w Bool -> UP r w a -> UP r w b
  -> UP r w (Either a b)
eitherUP boolUP aUP bUP = UP
  { unpickle = unpickle boolUP >>= bool
      (Right <$> unpickle bUP)
      (Left <$> unpickle aUP)
  , pickle = either
      (\a -> pickle boolUP True *> pickle aUP a)
      (\b -> pickle boolUP False *> pickle bUP b)
  }
\end{code}

Finally, we can map over (un)picklers with isomorphisms (bijections):
in other words, ``UP`` is a functor between the category of types and
isomorphisms and the category of types and functions, ``Hask``.

\begin{code}
-- For (to, from) :: Iso a b, we assume:
--
-- > to . from = id :: b -> b
-- > from . to = id :: a -> a
type Iso a b = (a -> b, b -> a)

mapUP :: Functor r => Iso a b -> UP r w a -> UP r w b
mapUP (to, from) aUP = UP
  { unpickle = fmap to (unpickle aUP)
  , pickle = pickle aUP . from
  }
\end{code}

Using the above, we *can* program (un)picklers, but it is not as convenient
as it might seem.
Every operation involved must be invertible (obviously for ``mapUP``,
while ``pairUP``, ``altUP``, and ``eitherUP`` rely on pattern matching).
``UP`` definitions for large records are rather tedious as
one has to write explicitly how to construct and destruct every record.

\begin{code}
-- Assume for the sake of example that this type exists...
data Date

-- ... with an UP.
dateUP :: BinaryUP Date
dateUP = (...)

data User = User
  { userId :: Int
  , userName :: String
  , userCreated :: Date
  , userEmail :: String
  }

userUP :: BinaryUP User
userUP =
  mapUP
    ( (\(((userId, userName), userCreated), userEmail) ->
        User{..})
    , (\User{..} ->
        (((userId, userName), userCreated), userEmail))
    ) (binaryUP >| binaryUP >| dateUP >| binaryUP)
\end{code}

Half the definition of ``userUP`` is boilerplate
for restructuring a tuple into/out of a ``User``.

A possible improvement is to derive the isomorphism generically,
or with meta-programming.

However, we can design a much nicer interface by spending some effort to fit
common abstractions in Haskell: applicative functors and monads.

I found something that works but I can really see that it looks good *a posteriori*,
whereas I have trouble giving an *a priori* motivation to work in that direction.
One is that that functional programmers are already familiar with these
abstractions, and that we can reasonably expect the ``r`` and ``w`` context to be
instances of ``Applicative`` or even ``Monad``, so it might make sense that
a "product" of those inherits of such structure.

Applicative Codec
=================

``UP r w`` is not a Haskell ``Functor`` (endofunctor of ``Hask``), because
pickling is contravariant (of type ``a -> w ()``).

The Trick
---------

The codec package dissociates the types being *parsed*
(i.e., unpickled, deserialized) and *produced* (i.e., pickled, serialized).

\begin{code}
data Codec r w x a = Codec
  { parse :: r a
  , produce :: x -> w ()
  }
\end{code}

We easily get ``Functor``, ``Applicative`` and even ``Alternative``.

\begin{code}
instance Functor r => Functor (Codec r w x) where
  fmap f codec = codec { parse = fmap f (parse codec) }

instance (Applicative r, Applicative w)
  => Applicative (Codec r w x) where

  pure a = Codec (pure a) (\_ -> pure ())

  f <*> a = Codec
    { parse = parse f <*> parse a
    , produce = \x -> produce f x *> produce a x
    }

instance (Alternative r, Alternative w)
  => Alternative (Codec r w x) where

  empty = Codec empty (\_ -> empty)

  a <|> a' = Codec
    { parse = parse a <|> parse a'
    , produce = \x ->
        produce a x <|> produce a' x
    }
\end{code}

``UP r w a`` is isomorphic to ``Codec r w a a``;
we're indeed working with a generalization of (un)picklers.

\begin{code}
upToCodec :: UP r w a -> Codec r w a a
upToCodec (UP parse produce) = Codec parse produce

codecToUP :: Codec r w a a -> UP r w a
codecToUP (Codec unpickle pickle) = UP unpickle pickle
\end{code}

However if we work only with ``Codec r w a a``, we cannot use ``Applicative``,
because the context ``Codec r w a :: * -> *`` is related to the content ``a ::
*``.

To modify the context,
we note that ``Codec r w x a`` is contravariant with respect to ``x``.
In fact, we have a ``Profunctor``.

\begin{code}
instance Functor r => Profunctor (Codec r w) where

  lmap :: (y -> x) -> Codec r w x a -> Codec r w y a
  lmap from = liftA2 Codec parse ((. from) . produce)

  rmap :: (a -> b) -> Codec r w x a -> Codec r w x b
  rmap = fmap
\end{code}

In the ``produce`` direction, ``lmap`` makes the ``Codec`` accept a
larger structure, a ``y`` containing an ``x`` that can be extracted with
``from``.

As an aside, notice that

\begin{code}
-- dimap
--   :: (y -> x) -> (a -> b)
--   -> Codec r w x a -> Codec r w y b
-- dimap from to = lmap from . rmap to
\end{code}

generalizes, with ``(y -> x) ~ (b -> a)``,

\begin{code}
-- mapUP
--   :: (a -> b, b -> a)     -- Iso a b
--   -> UP r w a -> UP r w b
\end{code}

An example of ``from :: y -> x`` function is a field getter;
we can now easily define a ``Codec`` for a record.

Assume we have a ``Codec`` for each field of ``User``:

\begin{code}
type BinaryCodec a = Codec Get PutM a a

-- For Int, String, etc.
binaryCodec :: Binary a => BinaryCodec a
binaryCodec = Codec get put

dateCodec :: BinaryCodec Date
dateCodec = (...)
\end{code}

Define an infix synonym for niceness:

\begin{code}
(=.)
  :: Functor r
  => (y -> x) -> Codec r w x a -> Codec r w y a
(=.) = lmap
\end{code}

The following definition looks much nicer than the one using ``mapUP``.

\begin{code}
userCodec :: BinaryCodec User
userCodec = User
  <$> userId =. binaryCodec
  <*> userName =. binaryCodec
  <*> userCreated =. dateCodec
  <*> userEmail =. binaryCodec
\end{code}

We can move fields around, (de)serializing them in a different order, with one
less location to modify compared to an ``UP`` definition (the ``to`` component
being mostly implicit here), though it still looks unwieldly.

\begin{code}
userReversedCodec :: BinaryCodec User
userReversedCodec =
  (\email created name id ->
    User id name created email)
  <$> userEmail =. binaryCodec
  <*> userCreated =. dateCodec
  <*> userName =. binaryCodec
  <*> userId =. binaryCodec
\end{code}

Magic record construction
-------------------------

The codec package actually does not work in the way I just presented.
It provides an ``Applicative`` instance, but is missing the ``Profunctor``
instance, or more specifically an ``(=.)`` (``lmap``), to work with
``Applicative``.

In fact, codec takes another approach.
With some boilerplate generated via Template Haskell,
it allows to define ``Codec``s with a syntax very similar to the above.
It has the additional feature that permuting the fields does not require
rewriting the constructor as I did in ``userReversedCodec``.

   All you need to do is provide a de/serializer for every record field in any
   order you like, and you get a de/serializer for the whole structure.
   **The type system ensures that you provide every field exactly once.**

   -- `The codec package`_

.. _The codec package: codec_

Going monad
===========

After getting an ``Applicative``, one is naturally led to wonder whether
there is a ``Monad`` as well.

If we try to implement it, we realize ``Codec`` is unfortunately not endowed
with such a structure. ``parse`` is fine, but there is no way
to obtain a ``produce`` from the second operand.

\begin{code}
-- Failed
instance (Monad r, Applicative w)
  => Monad (Codec r w x) where
  a >>= f = Codec
    { parse = parse a >>= parse . f
    , produce = \x ->
        produce a x *>
        (???) -- Can't apply f
    }
\end{code}

From here on, I have gone through a succession of choices, that I haven't
considered in detail individually, but I'm seeing something promising at the
end.

Carry a projection
------------------

A simple fix is to make explicit the intent that in ``Codec r w x a``,
the ``x`` should contain an ``a``.

\begin{code}
data Codec0 r w x a = Codec0
  { parse0 :: r a
  , produce0 :: x -> w ()
  , project0 :: x -> a
  }

instance Functor (Codec0 r w x) where fmap = (...)
instance Applicative (Codec0 r w x) where
  pure = (...) ; (<*>) = (...)
-- No Alternative?
instance Profunctor (Codec0 r w) where dimap = (...)

instance (Monad r, Applicative w)
  => Monad (Codec0 r w x) where
  a >>= f = Codec0
    { parse0 = parse0 a >>= parse0 . f
    , produce0 = \x ->
        produce0 a x *>
        produce0 (f (project0 a x)) x
    , project0 = \x ->
        project0 (f (project0 a x)) x
    }
\end{code}

The issue with that definition is that there is a duplication of code between
``produce0 :: x -> w ()`` and ``project0 :: x -> a``, made evident if we
unroll a composition of ``(>>=)`` and ``lmap``:

\begin{code}
-- lmap g a >>= f
-- =
-- Codec0
--   { produce0 = \x ->
--       produce0 a (g x) *>
--       produce0 (f (project0 a (g x))) x
--   , ..
--   }
\end{code}

``(g x)`` occurs twice, and we would like to factor it,
but the compiler won't see it.

Factor the projection
---------------------

That duplication might be avoided by factoring ``project`` out of ``produce``:

\begin{code}
data Codec1 r w x a = Codec1
  { parse1 :: r a
  , produce1 :: a -> w ()
  , project1 :: x -> a
  }
\end{code}

But that is just ``UP`` with a new field, and we face again contravariance
with respect to ``a``, and lose so much niceness (though how much of an
inconvenience it causes is still unclear).

The Trick (bis)
---------------

I would try to apply again the trick that led from ``UP`` to ``Codec`` in the
first place, splitting the covariant and contravariant occurences of ``a``:

\begin{code}
-- (Maybe come up with another name?)
-- The ordering here is chosen to be compatible
-- with the Profunctor typeclass...
data Codec3 r w k x a = Codec3
  { parse3 :: r a
  , produce3 :: k -> w ()
  , project3 :: x -> k
  }

-- ... but I really have some diagram x -> k -> a in mind.
type Codec' r w x k = Codec3 r w k x

instance Functor (Codec3 r w k x) where fmap = (...)
instance Applicative (Codec3 r w k x) where
  pure = (...) ; (<*>) = (...)
instance Profunctor (Codec3 r w k) where dimap = (...)
\end{code}

``Monad`` is unfortunately still out of reach.
It now seems quite foolish, I erased the link that I made just earlier between
``x`` and ``a``.

Parameterized monad
-------------------

After spending some time with this puzzle, I would generalize the Haskell
``Monad`` as follows:

\begin{code}
bindCodec'
  :: (Monad r, Applicative w)
  => Codec' r w k a a
  -> (a -> Codec' r w b k b)
  -> Codec' r w b k b
bindCodec' = (...)
\end{code}
