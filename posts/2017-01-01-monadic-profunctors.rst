---
title: Monadic profunctors for bidirectional programming
---

Introduction
============

Programmers deal with data in various forms, and often need ways to convert
back and forth between different representations. Such conversions are usually
expected to follow some inverse relationship, leading to partially overlapping
and redundant specifications. Multiple techniques have been investigated to
exploit that redundancy in order to define mappings between two representations
as a single *bidirectional transformation*.
These programs avoid code duplication; they are more concise and
more maintainable. Certain properties relating the unidirectional mappings that
are extracted from these artifacts can be established by construction,
lessening burden of correctness on the programmer.

Diverse languages have been created to program bidirectional transformations.
A popular approach in functional programming is the design of *combinator
libraries*, or ways to compose complex programs which inherit the good behavior
of their components. Such libraries form an *embedded domain specific language*,
and are generally simpler to implement and use than a wholly separate language.

TODO: Blabla

Unifying parsers and printers
=============================

This document is written in Literate Haskell.

\begin{code}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE InstanceSigs #-}
module Monadic.Profunctors where

import Data.Char
\end{code}

Let us first consider the problem of parsing and printing with a
straightforward approach.

Types
-----

Here are simple parser and printer types. A parser consumes a prefix of an
input string, converts it to a value of some type ``a``, returned alongside
the unconsumed suffix of the string. A printer simply converts a value into
a string.

\begin{code}
data Parser  a = Parser  (String -> (a, String))
data Printer a = Printer (a -> String)

runParser :: Parser a -> String -> (a, String)
runParser (Parser p) = p

runPrinter :: Printer a -> a -> String
runPrinter (Printer q) = q
\end{code}

We would like to be able to write both a parser and a printer as a single
enitity. So let us put them together in a pair, and call it an *invertible
parser*.

\begin{code}
data IParser0 a = IParser0 (Parser a) (Printer a)

asParser0 :: IParser0 a -> Parser a
asParser0 (IParser0 p _) = p

asPrinter0 :: IParser0 a -> Printer a
asPrinter0 (IParser0 _ q) = q
\end{code}

Elementary parsers
------------------

Let us define some elementary invertible parsers,
to parse/print a word made of digits and to consume/print whitespace.

\begin{code}
digits0 :: IParser0 String
digits0 = IParser0 p q
  where
    p = Parser $ \s -> span isDigit s
    q = Printer $ \digits -> digits

whitespace0 :: IParser0 ()
whitespace0 = IParser0 p q
  where
    p = Parser $ \s -> ((), dropWhile isSpace s)
    q = Printer $ \() -> " "
\end{code}

Parsers, like various other kinds of "computations", can generally be modelled
as applicative functors or monads, concretely represented in Haskell by the
type classes ``Applicative`` and ``Monad``. These abstractions provide a familiar
interface for functional programmers to compose computations.
Unfortunately, we will see that we cannot implement instances of ``Applicative``
or ``Monad`` for ``IParser0``.
However, it is still tempting to imitate these abstractions for invertible
parsers.

Functors
--------

Parsers are *functors*.
The ``mapParser`` higher-order function takes a function and applies it to the
result of a parser, producing a parser with a different output type. The
functor type class is part of Haskell's standard library ``base``.

\begin{code}
mapParser :: (a -> b) -> Parser a -> Parser b
mapParser f p = Parser $ \s ->
  let (a, s') = runParser p s
  in (f a, s')
\end{code}

Functors are represented in Haskell by the ``Functor`` type class in the standard
library.

.. code:: haskell

  class Functor m where
    fmap :: (a -> b) -> m a -> m b

\begin{code}
instance Functor Parser where
  fmap = mapParser
\end{code}

More precisely, the ``Functor`` type class represents *covariant functors*:
the input type ``a`` (resp. result type ``b``) of ``f :: a -> b`` corresponds to the
input type ``Parser a`` (resp. result type ``Parser b``)
of ``mapParser f :: Parser a -> Parser b``.

In contrast, ``Printer`` is a *contravariant functor*.

A contravariant functor reverses the direction of the lifted arrow:
the input type ``a`` (resp. result type ``b``) of ``f :: a -> b`` corresponds to
the result type ``Printer a`` (resp. input type ``Printer b``) of
``mapPrinter f :: Printer b -> Printer a``.

\begin{code}
mapPrinter :: (a -> b) -> Printer b -> Printer a
mapPrinter f q = Printer $ \a -> runPrinter q (f a)
\end{code}

Invertible parsers
++++++++++++++++++

To transform an ``IParser0``, which contains both a parser and a printer,  we
thus need to map both ways.
We say that ``IParser0`` is an *invariant functor*.

\begin{code}
class Invariant m where
  imap :: (a -> b) -> (b -> a) -> m a -> m b

instance Invariant IParser0 where
  imap :: (a -> b) -> (b -> a) -> IParser0 a -> IParser0 b
  imap f f' (IParser0 p q) = IParser0 (mapParser f p) (mapPrinter f' q)
\end{code}

``Parser`` and ``Printer`` independently turn out to also be instances,
simply ignoring one component or the other.

\begin{code}
instance Invariant Parser where
  imap f _ p = fmap f p

instance Invariant Printer where
  imap _ f' q = mapPrinter f' q
\end{code}

Demonstration: parsing an integer
+++++++++++++++++++++++++++++++++

We need to wrap ``digit0``, which only returns a string of digits.
We may map between that string and the corresponding number using
``read :: String -> Int`` and ``show :: Int -> String``.

\begin{code}
int0 :: IParser0 Int
int0 = imap read show digits0
\end{code}

Using the invertible parser:

.. code:: haskell

  > runParser (asParser0 int0) "42sixtimesnine"
  (42, "sixtimesnine")
  > runPrinter (asPrinter0 int0) 42
  "42"

Applicative functors
--------------------

Applicative functors allow to sequence computations and combine their
results.
``Functor`` is a superclass of ``Applicative``: every applicative functor is
a functor.

.. code:: haskell

  class Functor m => Applicative m where
    pure :: a -> m a
    (<*>) :: m (a -> b) -> m a -> m b

Our ``Parser`` is an instance of ``Applicative``.

``pure`` creates a parser that does nothing beyond producing a constant value.
The binary operator ``(<*>)`` ("ap") runs a parser producing a function ``f``,
followed by another producing a value ``a``, and returns the application
``f a``.

\begin{code}
instance Applicative Parser where
  pure a = Parser $ \s -> (a, s)

  -- "ap"
  pf <*> pa = Parser $ \s ->
    let (f, s') = runParser pf s
        (a, s'') = runParser pa s'
    in (f a, s'')
\end{code}

However, ``Printer`` is not an applicative functor, since it is not even an
instance of ``Functor``, being contravariant but not covariant.
Furthermore, even if we ignore the superclass constraint, a printer
``qf <*> qa :: Printer b`` would need to print a value (of type) ``b`` using
printers ``qf :: Printer (a -> b)`` and ``qa :: Printer a``, but there is no
general way to extract a function ``a -> b`` and a value ``a`` out of a value
``b``.

We can still apply the idea of sequencing operations to printers with a
different type class:

\begin{code}
class Invariant m => Monoidal m where
  pure' :: a -> m a

  -- "pair"
  (<.>) :: m a -> m b -> m (a, b)
\end{code}

``Printer`` is a ``Monoidal`` functor.

A pure printer just prints the empty string (essentially doing nothing).

Given two printers ``qa :: Printer a`` and ``qb :: Printer b``, we can construct
a printer for pairs of values ``qa <.> qb :: Printer (a, b)``, by
concatenating their printing results.

\begin{code}
instance Monoidal Printer where
  pure' :: a -> Printer a
  pure' _ = Printer $ \_ -> ""

  (<.>) :: Printer a -> Printer b -> Printer (a, b)
  qa <.> qb = Printer $ \(a, b) ->
    runPrinter qa a ++
    runPrinter qb b
\end{code}

Assuming that a type is a covariant ``Functor`` (e.g., ``Parser``), then ``(<*>)``
and ``(<.>)`` ("pair") are equivalent, in the sense that we can implement one
with the other. Below, ``(<$>)`` is an infix synonym for ``Functor``'s
``fmap``, quite frequent when programming in *applicative style*.

\begin{code}
(<.>*) :: Applicative m => m a -> m b -> m (a, b)
ma <.>* mb = (pair <$> ma) <*> mb
  where
    pair a b = (a, b)

(<*>.) :: (Functor m, Monoidal m) => m (a -> b) -> m a -> m b
ma <*>. mb = (\(f, a) -> f a) <$> (ma <.> mb)
\end{code}

Given two parsers ``pa :: Parser a`` and ``pb :: Parser b``, we can construct
a parser ``pa <.>* pb :: Parser (a, b)`` which runs both parsers successively
and collects their results in a pair.

Thus ``Parser`` is a ``Monoidal`` functor.

\begin{code}
instance Monoidal Parser where
  pure' :: a -> Parser a
  pure' = pure

  (<.>) :: Parser a -> Parser b -> Parser (a, b)
  (<.>) = (<.>*)
\end{code}

Invertible parsers
++++++++++++++++++

``IParser0`` is the product of two monoidal functors, which is monoidal as well.

\begin{code}
instance Monoidal IParser0 where
  pure' :: a -> IParser0 a
  pure' a = IParser0 (pure' a) (pure' a)

  (<.>) :: IParser0 a -> IParser0 b -> IParser0 (a, b)
  (IParser0 pa qa) <.> (IParser0 pb qb) = IParser0 (pa <.> pb) (qa <.> qb)
\end{code}

Demonstration: parsing a pair
+++++++++++++++++++++++++++++

Here is an invertible parser of a pair of numbers separated by whitespace.

We define the ``(.>)`` ("then") combinator which ignores the unit result of
its first operand, using ``imap`` to restructure the tuple produced by
``(<.>)``.

It is similar to ``(*>) :: Applicative m => m a -> m b -> m b`` from the
standard library. The restriction that the left argument returns a unit result
is necessary to avoid loss of information.

\begin{code}
-- "then"
(.>) :: Monoidal m => m () -> m a -> m a
mu .> ma = imap f f' (mu <.> ma)
  where
    f ((), m) = m
    f' m = ((), m)

pair0 :: IParser0 (Int, Int)
pair0 = int0 <.> (whitespace0 .> int0)
\end{code}

Using the invertible parser:

.. code:: haskell

  > runParser (asParser0 pair0) "2048   2187"
  ((2048, 2187), "")
  > runPrinter (asPrinter0 pair0) (2048, 2187)
  "2048 2187"

Monads
------

``Applicative`` or ``Monoidal`` sequence independent operations, thus their
expressiveness remains quite limited.

A generic kind of format we cannot parse with those is one where the input is
separated into a *header* and a *body*, with the header containing information
about the shape of the body.
For instance, consider strings that start with an integer ``n`` (the header),
followed by ``n`` more integers (the body).

For such a format, we need a *monadic* parser, and ``Parser`` is indeed a ``Monad``.
That means that it exposes the following operation: ``(>>=)`` ("bind") runs the
first parser, and passes the result to the second parameterized parser before
running it.

.. code:: haskell

  class Applicative m => Monad m where
    -- "bind"
    (>>=) :: m a -> (a -> m b) -> m b

\begin{code}
instance Monad Parser where
  (>>=) :: Parser a -> (a -> Parser b) -> Parser b
  pa >>= atopb = Parser $ \s ->
    let (a, s') = runParser pa s
    in runParser (atopb a) s'
\end{code}

Extending the header/body analogy, we can see that ``(>>=)`` also
does not fit printers. If ``qa :: Printer a`` is the printer of headers ``a``,
and ``atoqb :: a -> Printer b`` is the printer of bodies ``b`` parameterized
by headers, their composition needs to accept a type containing
the header, whereas ``(>>=)`` simply forgets the type of the header ``a`` in
the result.
We can join the results of two computations in a pair,
similarly to the way we reshaped ``Applicative`` into ``Monoidal``.

\begin{code}
class Monoidal m => Monadoidal m where
  -- "pairing bind"
  (>>+) :: m a -> (a -> m b) -> m (a, b)
\end{code}

Every ``Monad`` instance, including ``Parser``,
can be an instance of ``Monadoidal``.

\begin{code}
(>>+=) :: Monad m => m a -> (a -> m b) -> m (a, b)
ma >>+= atomb = ma >>= \a -> atomb a >>= \b -> pure (a, b)

instance Monadoidal Parser where
  (>>+) :: Parser a -> (a -> Parser b) -> Parser (a, b)
  (>>+) = (>>+=)
\end{code}

A ``Printer`` is an instance of ``Monadoidal``.

\begin{code}
instance Monadoidal Printer where
  (>>+) :: Printer a -> (a -> Printer b) -> Printer (a, b)
  qa >>+ atoqb = Printer $ \(a, b) ->
    runPrinter qa a ++
    runPrinter (atoqb a) b
\end{code}

Thus, so is ``IParser0``.

\begin{code}
instance Monadoidal IParser0 where
  (>>+) :: IParser0 a -> (a -> IParser0 b) -> IParser0 (a, b)
  pqa >>+ atopqb = IParser0 p q
    where
      p = asParser0 pqa >>+ (asParser0 . atopqb)
      q = asPrinter0 pqa >>+ (asPrinter0 . atopqb)
\end{code}

Demonstration: parsing a list
+++++++++++++++++++++++++++++

Here is an invertible parser of a list of integers, written as the length ``n``
followed by ``n`` integers.

Given the length, we can iterate a parser with the ``replicate0`` combinator
defined here.

\begin{code}
replicate0 :: Monadoidal m => Int -> m a -> m [a]
replicate0 0 pq = pure' []
replicate0 n pq = imap cons uncons (pq <.> replicate0 (n - 1) pq)
  where
    cons (a, as) = a : as
    uncons (a : as) = (a, as)
    uncons [] = error "Unexpected empty list"

intList0 :: IParser0 [Int]
intList0 = imap f f' (int0 >>+ \n -> replicate0 n (whitespace0 .> int0))
  where
    f (_, xs) = xs
    f' xs = (length xs, xs)
\end{code}

Using the invertible parser:

.. code:: haskell

  > runParser (asParser0 intList0) "3      0 1  2  "
  ([0, 1, 2], "  ")
  > runPrinter (asPrinter0 intList0) [0, 1, 2]
  "3 0 1 2"
