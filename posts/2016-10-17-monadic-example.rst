---
title: Towards Monadic Bidirectional Serialization, a monadic example
---

This is written in Literate Haskell.

\begin{code}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Bidirectional.Serialization.Three where

import Control.Applicative
import Control.Monad (void, replicateM)
import Data.Int
import Data.Binary.Get (Get, getInt32be, getLazyByteString)
import Data.Binary.Put (Put, PutM, putInt32be, putLazyByteString)
import Data.ByteString.Lazy (ByteString)
import qualified Data.ByteString.Lazy as BS
import Data.Profunctor (Profunctor(..))

-- Intentional synonyms of undefined.

(...) :: omittedForBrevity
(...) = (...)

(???) :: can'tSolveThis
(???) = (???)
\end{code}

A simple (de)serialization problem
==================================

A common way to encode messages of variable lengths in binary is to prefix them
with their lengths. This is for example how the WeeChat Relay protocol
encodes `long integers`_, strings_, pointers_.

.. _long integers: https://weechat.org/files/doc/devel/weechat_relay_protocol.en.html#object_long_integer
.. _strings: https://weechat.org/files/doc/devel/weechat_relay_protocol.en.html#object_string
.. _pointers: https://weechat.org/files/doc/devel/weechat_relay_protocol.en.html#object_pointer

More particularly, strings are prefixed with their length on 4 bytes.

  ::

    ┌────┬────┬────┬────╥────┬────┬────┬────┬────┐
    │ 00 │ 00 │ 00 │ 05 ║ 68 │ 65 │ 6C │ 6C │ 6F │ ────► "hello"
    └────┴────┴────┴────╨────┴────┴────┴────┴────┘
     └─────────────────┘ └──────────────────────┘
           length         'h'  'e'  'l'  'l'  'o'

  -- String format in the WeeChat Relay protocol.

Naive (de)serializer
--------------------

A serializer and a deserializer are easily written using the binary
library.

\begin{code}
type Raw = ByteString

getInt32AsInt64 :: Get Int64
getInt32AsInt64 = fmap fromIntegral getInt32be

putInt32AsInt64 :: Int64 -> Put
putInt32AsInt64 = putInt32be . fromIntegral

getString :: Get Raw
getString =
  getInt32AsInt64 >>=
  getLazyByteString

putString :: Raw -> Put
putString bs =
  putInt32AsInt64 (BS.length bs) >>
  putLazyByteString bs
\end{code}

The binary library provides the following:

.. code:: haskell

  runGet :: Get a -> ByteString -> a
  runPut :: Put -> ByteString

Pickler Combinators
===================

The code above is quite repetitive due to the dual nature of (de)serialization.
Instead, we could have a single type containing both the ``Get`` and the
``Put``.
This is basically ``PU`` as in the *Pickler Combinators* paper, but it works in
contexts ``Get`` and ``PutM`` instead of using the more naive parser type
``String -> (a, String)``.

\begin{code}
-- type Put = PutM ()

data GetPut a = GetPut
  { get :: Get a
  , put :: a -> Put
  }
\end{code}

We may wrap the binary primitives for (de)serialization as a separate library:

\begin{code}
int32 :: GetPut Int32
int32 = GetPut getInt32be putInt32be

-- Bytestrings of fixed length.
byteString :: Int64 -> GetPut Raw
byteString n = GetPut
  { get = getLazyByteString n
  , put = \bs ->
      if BS.length bs == n
      then putLazyByteString bs
      else fail "Incorrect length."
  }
\end{code}

``GetPut`` supports a couple of operations. We can map over them
with a bijection:

\begin{code}
mapGetPut :: (a -> b) -> (b -> a) -> GetPut a -> GetPut b
mapGetPut to from gp = GetPut
  { get = to <$> get gp
  , put = put gp . from
  }
\end{code}

We can bind ``GetPut`` values in a monadic fashion, by providing an additional
mapping ``from :: b -> a``:

\begin{code}
bindGetPutWith
  :: (b -> a)
  -> GetPut a -> (a -> GetPut b) -> GetPut b
bindGetPutWith from a_ b_ = GetPut
  { get = get a_ >>= \a -> get (b_ a)
  , put = \b -> let a = from b in
      put a_ a >> put (b_ a) b
  }
\end{code}

Bidirectional (de)serializer
----------------------------

\begin{code}
int32AsInt64 :: GetPut Int64
int32AsInt64 = mapGetPut fromIntegral fromIntegral int32

-- A bytestring prefixed by its length on 4 bytes.
string :: GetPut Raw
string =
  bindGetPutWith BS.length
    int32AsInt64
    byteString
\end{code}

Invertible Syntax Descriptions
==============================

The paper *Invertible Syntax Descriptions* describes a typeclass-based
interface for (de)serializers in ``Applicative`` style.
The monadic ``bindGetPutWith`` above could be provided as a subclass.

.. code:: haskell

  class Syntax f => MonadicSyntax f where
    bindWith :: (b -> a) -> f a -> (a -> f b) -> f b

Common abstractions
===================

We can actually obtain ``mapGetPut`` and ``bindGetPutWith``
using ``Profunctor`` and ``Monad`` instances of a more general type.

\begin{code}
data GetPut' b a = GetPut'
  { get' :: Get a
  , put' :: b -> PutM a
  }

-- Functor Get, Functor PutM.
instance Functor (GetPut' b) where

  fmap f a = GetPut'
    { get' = fmap f (get' a)
    , put' = fmap f . put' a
    }

-- Applicative Get, Applicative PutM.
instance Applicative (GetPut' b) where

  pure x = GetPut' (pure x) (\_ -> pure x)

  f <*> x = GetPut'
    { get' = get' f <*> get' x
    , put' = liftA2 (<*>) (put' f) (put' x)
    }

-- Monad Get, Monad PutM.
instance Monad (GetPut' b) where

  x >>= f = GetPut'
    { get' = get' x >>= get' . f
    , put' = \b -> put' x b >>= \a -> put' (f a) b
    }

instance Profunctor GetPut' where

  lmap :: (b1 -> b0) -> GetPut' b0 a -> GetPut' b1 a
  lmap f a = GetPut'
    { get' = get' a
    , put' = put' a . f
    }

  rmap = fmap
\end{code}

Indeed, it generalizes ``GetPut``, with some modifications
to erase/preserve the value returned by a ``put``.

\begin{code}
type GetPut_ a = GetPut' a a

toGetPut :: GetPut_ a -> GetPut a
toGetPut (GetPut' get put) = GetPut get (void . put)

fromGetPut :: GetPut a -> GetPut_ a
fromGetPut (GetPut get put) = GetPut' get (\a -> a <$ put a)


-- Primitives

byteString' :: Int64 -> GetPut_ Raw
byteString' = fromGetPut . byteString

int32' :: GetPut_ Int32
int32' = fromGetPut int32
\end{code}

``Profunctor`` provides this generalization of ``mapGetPut``.

.. code:: haskell

  dimap :: Profunctor f
        => (b1 -> b0) -> (a0 -> a1) -> f b0 a0 -> f b1 a1
  dimap :: (b -> a) -> (a -> b) -> GetPut_ a -> GetPut_ b
  dimap f g = lmap f . rmap g

A more principled (de)serializer
--------------------------------

\begin{code}
int32AsInt64' :: GetPut_ Int64
int32AsInt64' = dimap fromIntegral fromIntegral int32'

string' :: GetPut_ Raw
string' =
  lmap BS.length int32AsInt64' >>=
  byteString'

-- With do notation
string'_ :: GetPut_ Raw
string'_ = do
  n <- lmap BS.length int32AsInt64'
  byteString' n
\end{code}

It looks a bit underwhelming. The programmer must still provide
the same three elements, a (de)serializer for the length (``int32AsInt64``),
a (de)serializer for the rest of the data (``byteString``), and a
mapping from the data back to the length (``length``).

The difference is that instead of an ad-hoc combinator ``bindGetPutWith``, they
now have access to a more familiar interface consisting of ``Profunctor`` and
``Monad`` instances, with increased flexibility.

A ``GetPut'`` can be seen as a ``Get`` (from the binary package), with
annotations (acting on the first type parameter ``b``) to handle the inverse
``Put`` at the same time. Trying to implement as close an interface to ``Get``
as possible may help make it simpler to migrate to ``GetPut'``: fewer changes
are necessary (some of them could even be derived automatically).

Splitting ``bindGetPutWith`` as a composition of ``lmap`` and ``(>>=)`` also
makes explicit the fact that the ``from`` parameter (in the definition of
``bindGetPutWith``) is only used to (co)map over the ``put'`` component.
Hopefully, this clarifies the shared structure between the serializer and the
deserializer, while isolating the additional mappings used by the
latter.

However, the usefulness of ``Monad`` and ``Applicative`` instances for this
(de)serializer type remains rather limited in some respects.
Indeed, manipulations on the contravariant type parameter ``b`` gets in the way
of composing actions using just ``Monad``.

Applicative and monadic combinators
===================================

Replicate
---------

Given a ``GetPut_ a``, parse a list of ``n`` elements.
Let us try to use ``replicateM`` for this task:

\begin{code}
-- Failed.
replicateGetPut0 :: forall a. Int -> GetPut_ a -> GetPut_ [a]
replicateGetPut0 n a = replicateM n ((???) :: GetPut' [a] a)
\end{code}

There is no way to fill the hole ``(???) :: GetPut' [a] a`` correctly
(the ``a`` parameter has type ``GetPut' a a``).
Indeed, its ``put'`` component should have type ``[a] -> PutM a``, i.e.,
it would serialize *one* element of the list.
Replicating such an action would only serialize the same element ``n`` times.
Sequencing ``n`` values of type ``GetPut' [a] a`` is also undesirable, because
the ``put`` component of each one accesses an element the list to be serialized
independently of all others, which cumulates to a complexity that is quadratic
in ``n``.

We can define a variant of ``replicateM`` by explicit recursion or by breaking
abstraction using the ``GetPut'`` constructor.
The definition is in any case quite ad-hoc to our application.

Explicit recursion
++++++++++++++++++

\begin{code}
-- The implementation turned out to be generalizable.
replicateGetPut :: Int -> GetPut_ a -> GetPut_ [a]
replicateGetPut = replicatePA

replicatePA
  :: (Profunctor f, Applicative (f [b]))
  => Int -> f b a -> f [b] [a]
replicatePA n _ | n <= 0 = pure []
replicatePA n a  =
  (:)
    <$> lmap head a
    <*> lmap tail (replicatePA (n-1) a)
\end{code}

The main body of this function is an applicative definition.
The notation used there is in fact quite useful for records; here we can
consider a non-empty list as a record too, this should give an idea
of how this notation can be used for larger records:

.. code:: haskell

  data [] a
    = (:) { head :: a, tail :: [] a }
    | []

Breaking abstraction
++++++++++++++++++++

\begin{code}
-- Also generalizable.
replicateGetPut_ :: Int -> GetPut_ a -> GetPut_ [a]
replicateGetPut_ = replicateGetPut_'

replicateGetPut_' :: Int -> GetPut' b a -> GetPut' [b] [a]
replicateGetPut_' n a = GetPut'
  { get' = replicateM n (get' a)
  , put' = \bs ->
      if length bs == n
      then traverse (put' a) bs
      else fail "Incorrect length."
  }
\end{code}

One benefit of this non-recursive definition might be that inlining it is more
likely to trigger optimizations.

Traverse
--------

Similarly, ``traverse`` cannot be used alone here.

.. code:: haskell

  traverse
    :: (Traversable t, Applicative f)
    => (c -> f a) -> t c -> f (t a)

A variant specific to ``GetPut`` needs to be defined.

\begin{code}
traverseGetPut :: (c -> GetPut_ a) -> [c] -> GetPut_ [a]
traverseGetPut = traversePA

traversePA
  :: (Profunctor f, Applicative (f [b]))
  => (c -> f b a)
  -> [c]
  -> f [b] [a]
traversePA f [] = pure []
traversePA f (c : cs) =
  (:)
    <$> lmap head (f c)
    <*> lmap tail (traversePA f cs)

traverseGetPut_ :: (c -> GetPut_ a) -> [c] -> GetPut_ [a]
traverseGetPut_ = traverseGetPut_'

traverseGetPut_' :: (c -> GetPut' b a) -> [c] -> GetPut' [b] [a]
traverseGetPut_' f cs = GetPut'
  { get' = traverse (get' . f) cs
  , put' = \bs ->
      if length bs == n
      then traverse (\(c, b) -> put' (f c) b) (zip cs bs)
      else fail "Incorrect length."
  } where
    n = length cs
\end{code}

Pattern matching and the usage of ``zip`` prevent us to
traverse any ``Traversable`` structure in ``GetPut'``.

Open issues
===========

Either, pattern matching, case analysis
---------------------------------------

\begin{code}
-- Alternative Get.
eitherGetPut
  :: GetPut' bl al -> GetPut' br ar
  -> GetPut' (Either bl br) (Either al ar)
eitherGetPut l r = GetPut'
  { get' = Left <$> get' l <|> Right <$> get' r
  , put' = either (fmap Left . put' l) (fmap Right . put' r)
  }
\end{code}

Maybe use prisms.

Nested structures
-----------------

Consider the concatenation of a bytestring (prefixed by its length as above)
and an integer to encode ``(Raw, Int32)``, and let us write this monadically.
[#better]_

.. [#better]
  A better example would have the second element depend on the first.

\begin{code}
rawAndInt32 :: GetPut_ (Raw, Int32)
rawAndInt32 = do
  n <- lmap (BS.length . fst) int32AsInt64'
  raw <- lmap fst (byteString' n)
  int <- lmap snd int32'
  return (raw, int)
\end{code}

The issue is that ``fst`` is written twice. With more complex accessors,
this duplication is inefficient as the same data is accessed twice.
A better definition would nest the part corresponding to the ``Raw``
component.

\begin{code}
rawAndInt32' :: GetPut_ (Raw, Int32)
rawAndInt32' = do
  raw <- lmap fst $ do
    n <- lmap BS.length int32AsInt64'
    byteString' n
  int <- lmap snd int32'
  return (raw, int)
\end{code}

However, if the second component ``Int32`` depended on ``n`` (for example, replace
``int32'`` with some ``f n``), that transformation would not be possible, as it
pulls ``n`` into a local scope.
Some boilerplate is necessary to reexpose it.

\begin{code}
rawAndInt32'' :: GetPut_ (Raw, Int32)
rawAndInt32'' = do
  (n, raw) <- lmap fst $ do
    n <- lmap BS.length int32AsInt64'
    raw <- byteString' n
    return (n, raw)
  int <- lmap snd (f n)
  return (raw, int)
  where
    f n = (...)
\end{code}

I wonder whether a more powerful ``Monad``-like structure could achieve the
syntactic simplicity of the first one, with the efficiency of the last one.
