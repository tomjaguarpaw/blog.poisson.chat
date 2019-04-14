---
title: Better invertible syntax descriptions
keywords: [haskell, bidirectional]
---

This is written in Literate Haskell.

\begin{code}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module Better.Invertible.Syntax where

import Control.Applicative
import Control.Monad
import Data.Monoid
-- partial-isomorphisms
import Control.Isomorphism.Partial (IsoFunctor)
import qualified Control.Isomorphism.Partial as Iso
-- invertible-syntax
import Text.Syntax.Classes (ProductFunctor, Syntax)
import qualified Text.Syntax.Classes as Syntax
\end{code}

The paper *Invertible Syntax Descriptions* [#isd]_ describes a
typeclass-based interface to define parsers and (pretty) printers
as a single polymorphic artefact.

.. [#isd]
  *Invertible Syntax Descrptions: Unifying Parsing and Pretty Printing*,
  T. Rendel, K. Ostermann. http://lambda-the-ultimate.org/node/4191

It proposes a common abstraction for parsers and printers that is
designed to mimic *standard typeclasses*, i.e., typeclasses of general
usefulness, including (but not restricted to) those in the standard library,
base.
Three newly introduced typeclasses ``IsoFunctor``, ``ProductFunctor``,
``Syntax.Alternative`` respectively correspond to ``Functor``, ``Applicative``,
``Alternative`` in some abstract sense.

A naive implementation of that interface as a proof of
concept is provided in the paper, with the following concrete types:

\begin{code}
newtype Parser a = Parser { runParser :: String -> (a, String) }
newtype Printer a = Printer { runPrinter :: a -> String }
\end{code}

Note that ``Parser`` is an ``Applicative`` (also a ``Monad``), while
``Printer a`` is a ``Monoid``
(actually deferring to ``String`` being a ``Monoid``).
More generally, parser combinator (e.g., parsec) and pretty-printer (e.g.,
pretty) libraries usually implement instances of such standard typeclasses.

However, the paper does not consider whether standard typeclasses could be
used to implement the newer ones, even though the latter were designed
based on the former.

As I will show here, instances of the three core typeclasses of the paper can
be derived from instances of standard typeclasses: ``Applicative``,
``Alternative``, ``MonadPlus`` (``Monad`` + ``Alternative``) for parsers,
``Monoid`` for printers.

This improves the usability of the new typeclasses, as less work and
boilerplate are necessary to implement instances for different parsers and
printers.

The only method requiring an implementation specific to each
parser and printer is ``token`` from the ``Syntax`` typeclass.

A standard implementation
=========================

To avoid overlapping instances, we define wrappers for parsers and printers.

Parsers
-------

\begin{code}
-- Parsing in a context p :: * -> *
newtype Parsing p a = Parsing { parsing :: p a }
  deriving (Functor, Applicative, Monad, Alternative, MonadPlus)
\end{code}

A parser ``p :: * -> *`` should be an instance of ``MonadPlus`` to
imply an ``IsoFunctor`` (i.e., a functor from partial isomorphisms to Hask).
The constraint could be relaxed to ``Functor`` at the cost of (unsafely)
assuming total isomorphisms in place of partial ones.

\begin{code}
instance MonadPlus p => IsoFunctor (Parsing p) where
  iso <$> Parsing p = Parsing (p >>= aFromMaybe . Iso.apply iso)

aFromMaybe :: Alternative f => Maybe a -> f a
aFromMaybe = maybe empty pure
\end{code}

``ProductFunctor`` and ``Syntax.Alternative`` reflect
``Applicative`` and ``Alternative`` respectively.
Below, the instance of ``Alternative`` abuses Haskell's scoping rules for
typeclass methods.
``empty`` and ``(<|>)`` on the right-hand sides refer to methods from
``Control.Applicative.Alternative``, and not to the variables
being defined with the same names on the left-hand sides.

\begin{code}
instance Applicative p => ProductFunctor (Parsing p) where
  Parsing a <*> Parsing b = Parsing (liftA2 (,) a b)

instance Alternative p => Syntax.Alternative (Parsing p) where
  empty = Parsing empty
  Parsing a <|> Parsing a' = Parsing (a <|> a')
\end{code}

The ``Syntax`` typeclass, more precisely, its ``token`` method (we may get
``pure`` from ``Applicative``), needs a implementation that is specific to the
underlying parser type. We may then lift it to ``Parsing``.

\begin{code}
instance (MonadPlus p, Syntax p) => Syntax (Parsing p) where
  pure = Parsing . pure
  token = Parsing Syntax.token
\end{code}

Printers
--------

We rely on a printer being a ``Monoid`` to implement
``ProductFunctor``.

\begin{code}
-- Printing a monoid q :: *
newtype Printing q a = Printing { printing :: a -> Maybe q }

instance IsoFunctor (Printing q) where
  iso <$> Printing q = Printing (Iso.unapply iso >=> q)

instance Monoid q => ProductFunctor (Printing q) where
  Printing f <*> Printing g = Printing (\(a, b) -> f a <> g b)

instance Syntax.Alternative (Printing q) where
  empty = Printing (\_ -> Nothing)
  Printing a <|> Printing a' = Printing (liftA2 (<|>) a a')
\end{code}

Again, a specialized implementation is required for ``token``,
but ``pure`` can be derived for a ``Monoid`` as well.

\begin{code}
purePrinting :: (Eq a, Monoid q) => a -> Printing q a
purePrinting a = Printing (\a' -> mempty <$ guard (a == a'))
\end{code}

Concluding remarks
==================

Another benefit these definitions is that they help characterize the
expressive power that is expected of parsers and printers implementing such
an interface.

In particular, the ``MonadPlus`` constraint to implement ``IsoFunctor``
is rather strong. The reduced expressiveness of a parser that is
only ``Applicative`` is often an acceptable drawback in exchange for
increased performance, but such parsers do not rightly fit in that
interface.

I also believe that it is a mistake to make ``Syntax`` a subclass
of ``Alternative``. Although it makes type signatures shorter, it is
unreasonable to require it for every parser, as error recovery is far from
being a universal capability.
