---
title: Towards monadic bidirectional serialization, a step back
keywords: [haskell, bidirectional]
---

This is written in Literate Haskell.

\begin{code}
module Bidirectional.Serialization.Two where

import Control.Applicative
import Data.Profunctor
\end{code}

Last episode
============

I proposed to extend ``Codec`` as follows:

\begin{code}
data Codec_ r w x a = Codec_
  { parse_ :: r a
  , produce_ :: x -> w ()
  , project_ :: x -> a
  }
\end{code}

And so on. It was becoming quite sophisticated.

A step back
===========

Instead fix ``produce`` to carry the ``a`` type as well.
In a way, this merges ``produce_`` and ``project_`` in a single
field.

\begin{code}
data Codec r w x a = Codec
  { parse :: r a
  , produce :: x -> w a
  }

instance (Functor r, Functor w)
  => Functor (Codec r w x) where

  fmap f codec = Codec
    { parse = fmap f (parse codec)
    , produce = fmap f . produce codec
    }

instance (Applicative r, Applicative w)
  => Applicative (Codec r w x) where

  pure a = Codec (pure a) (\_ -> pure a)

  f <*> a = Codec
    { parse = parse f <*> parse a
    , produce = \x -> produce f x <*> produce a x
    }

-- We had lost this one for a moment
instance (Alternative r, Alternative w)
  => Alternative (Codec r w x) where

  empty = Codec empty (\_ -> empty)

  a <|> a' = Codec
    { parse = parse a <|> parse a'
    , produce = \x -> produce a x <|> produce a' x
    }

instance (Functor r, Functor w)
  => Profunctor (Codec r w) where

  lmap from codec = codec
    { produce = produce codec . from
    }

  rmap = fmap

-- Hurray!
instance (Monad r, Monad w)
  => Monad (Codec r w x) where

  a >>= f = Codec
    { parse = parse a >>= parse . f
    , produce = \x ->
        produce a x >>= \a -> produce (f a) x
    }
\end{code}

Note that constraints are now symmetrical, ``(Functor r, Functor w)`` and
``(Monad r, Monad w)``, instead of ``Functor r`` and
``(Monad r, Applicative w)``, respectively.

In hindsight, the fact that previously we only ever used an ``Applicative w``
was suspicious.
We were actually relying on ``w ()`` being a monoid.
We might as well turn ``w ()`` into a single variable ``m``.

\begin{code}
-- Simplified Codec_
-- The same instances can be implemented with
-- a Monoid m constraint instead of Applicative w.
data CodecM r m x a = CodecM
  { parseM :: r a
  , produceM :: x -> m
  }
\end{code}

Our ``Codec`` subsumes ``CodecM`` (and thus ``Codec_``) via the following
encoding:

\begin{code}
-- We have Monoid m => Applicative (Const m)
codecMToCodec :: CodecM r m x a -> Codec r (Const m) x a
codecMToCodec a = Codec
  { parse = parseM a
  , produce = Const . produceM a
  }

codecToCodecM :: Codec r (Const m) x a -> CodecM r m x a
codecToCodecM a = CodecM
  { parseM = parse a
  , produceM = getConst . produce a
  }
\end{code}
