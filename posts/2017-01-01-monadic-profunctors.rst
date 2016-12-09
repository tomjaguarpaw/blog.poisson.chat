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
Familiarity with syntax in the ML family of functional languages
is assumed (e.g., type annotations, pattern matching, function application),
and we shall try to explain constructs which are specific to Haskell when
necessary.

\begin{code}
{-# LANGUAGE InstanceSigs #-}
module Monadic.Profunctors where

import Data.Char
import Data.Monoid
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
data Parser   a = Parser   (String -> (a, String))
data Printer0 a = Printer0 (a -> String)

runParser :: Parser a -> String -> (a, String)
runParser (Parser p_) = p_

runPrinter0 :: Printer0 a -> a -> String
runPrinter0 (Printer0 q_) = q_
\end{code}

We would like to be able to write both a parser and a printer as a single
enitity. So let us put them together in a pair, and call it an *invertible
parser*.

\begin{code}
data IParser0 a = IParser0 (Parser a) (Printer0 a)

asParser0 :: IParser0 a -> Parser a
asParser0 (IParser0 p _) = p

asPrinter0 :: IParser0 a -> Printer0 a
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
    q = Printer0 $ \digits -> digits

whitespace0 :: IParser0 ()
whitespace0 = IParser0 p q
  where
    p = Parser $ \s -> ((), dropWhile isSpace s)
    q = Printer0 $ \() -> " "
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
result of a parser, producing a parser with a different output type.

\begin{code}
mapParser :: (a -> b) -> Parser a -> Parser b
mapParser f p = Parser $ \s ->
  let (a, s') = runParser p s
  in (f a, s')
\end{code}

Functors are represented in Haskell by the ``Functor`` type class in the standard
library ``base``.

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

In contrast, ``Printer0`` is a *contravariant functor*.

A contravariant functor reverses the direction of the lifted arrow:
the input type ``a`` (resp. result type ``b``) of ``f :: a -> b`` corresponds to
the result type ``Printer0 a`` (resp. input type ``Printer0 b``) of
``mapPrinter0 f :: Printer0 b -> Printer0 a``.

\begin{code}
mapPrinter0 :: (a -> b) -> Printer0 b -> Printer0 a
mapPrinter0 f q = Printer0 $ \a -> runPrinter0 q (f a)
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
  imap f f' (IParser0 p q) = IParser0 (mapParser f p) (mapPrinter0 f' q)
\end{code}

``Parser`` and ``Printer0`` independently turn out to also be instances,
simply ignoring one component or the other.

\begin{code}
instance Invariant Parser where
  imap f _ p = fmap f p

instance Invariant Printer0 where
  imap _ f' q = mapPrinter0 f' q
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
  > runPrinter0 (asPrinter0 int0) 42
  "42"

Applicative functors
--------------------

Applicative functors make it possible to sequence computations and combine
their results.
``Functor`` is a superclass of ``Applicative``: every applicative functor is
a (covariant) functor.

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

However, ``Printer0`` is not an applicative functor, since it is not even a
covariant functor, but a contravariant one.
Furthermore, even if we ignore the superclass constraint, a printer
``qf <*> qa :: Printer0 b`` would need to print a value (of type) ``b`` using
printers ``qf :: Printer0 (a -> b)`` and ``qa :: Printer0 a``, but there is no
general way to extract a function ``a -> b`` and a value ``a`` out of a value
``b``.

Monoidal functors
+++++++++++++++++

We can still apply the idea of sequencing operations to printers with a
different type class:

\begin{code}
class Invariant m => Monoidal m where
  pure' :: a -> m a

  -- "pair"
  (<.>) :: m a -> m b -> m (a, b)
\end{code}

A pure printer just prints the empty string (essentially doing nothing).

Given two printers ``qa :: Printer0 a`` and ``qb :: Printer0 b``, we can construct
a printer for pairs of values ``qa <.> qb :: Printer0 (a, b)``, by
concatenating their printing results.

Thus ``Printer0`` is a monoidal functor.

\begin{code}
instance Monoidal Printer0 where
  pure' :: a -> Printer0 a
  pure' _ = Printer0 $ \_ -> ""

  (<.>) :: Printer0 a -> Printer0 b -> Printer0 (a, b)
  qa <.> qb = Printer0 $ \(a, b) ->
    runPrinter0 qa a ++
    runPrinter0 qb b
\end{code}

Assuming that a type is a covariant ``Functor`` (e.g., ``Parser``), then ``(<*>)``
and ``(<.>)`` ("pair") are equivalent, in the sense that we can implement one
with the other.

Below, ``(<$>)`` is an infix synonym for ``Functor``'s
``fmap``, quite frequent when programming in *applicative style*.
``(,)`` is the constructor of pairs used as a regular identifier.

\begin{code}
(<.>*) :: Applicative m => m a -> m b -> m (a, b)
ma <.>* mb = (,) <$> ma <*> mb

(<*>.) :: (Functor m, Monoidal m) => m (a -> b) -> m a -> m b
ma <*>. mb = (\(f, a) -> f a) <$> (ma <.> mb)

-- f <$> a = fmap f a
-- f <$> a <*> b = (f <$> a) <*> b  -- Associates like that
-- (,) a b = (a, b)
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

pairInt0 :: IParser0 (Int, Int)
pairInt0 = int0 <.> (whitespace0 .> int0)
\end{code}

Using the invertible parser:

.. code:: haskell

  > runParser (asParser0 pairInt0) "2048   2187"
  ((2048, 2187), "")
  > runPrinter0 (asPrinter0 pairInt0) (2048, 2187)
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
  pa >>= topb = Parser $ \s ->
    let (a, s') = runParser pa s
    in runParser (topb a) s'
\end{code}

Extending the header/body analogy, we can see that ``(>>=)`` also
does not fit printers. If ``qa :: Printer0 a`` is the printer of headers ``a``,
and ``toqb :: a -> Printer0 b`` is the printer of bodies ``b`` parameterized
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
ma >>+= tomb = ma >>= \a -> tomb a >>= \b -> pure (a, b)

instance Monadoidal Parser where
  (>>+) :: Parser a -> (a -> Parser b) -> Parser (a, b)
  (>>+) = (>>+=)
\end{code}

A ``Printer0`` is an instance of ``Monadoidal``.

\begin{code}
instance Monadoidal Printer0 where
  (>>+) :: Printer0 a -> (a -> Printer0 b) -> Printer0 (a, b)
  qa >>+ toqb = Printer0 $ \(a, b) ->
    runPrinter0 qa a ++
    runPrinter0 (toqb a) b
\end{code}

Thus, so is ``IParser0``.

\begin{code}
instance Monadoidal IParser0 where
  (>>+) :: IParser0 a -> (a -> IParser0 b) -> IParser0 (a, b)
  pqa >>+ topqb = IParser0 p q
    where
      p = asParser0 pqa >>+ (asParser0 . topqb)
      q = asPrinter0 pqa >>+ (asPrinter0 . topqb)
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
  > runPrinter0 (asPrinter0 intList0) [0, 1, 2]
  "3 0 1 2"

The approach outlined above leads to a type class hierarchy
``Invariant``/``Monoidal``/``Monadoidal`` which parallels a
well-established one ``Functor``/``Applicative``/``Monad``.

TODO: drawbacks? Tuples.

Invertible parsing as a profunctor
==================================

We study a different construction of invertible parsers, which is
actually an instance of ``Functor``/``Applicative``/``Monad``.

Recall the previously defined type of invertible parsers:

.. code:: haskell

  data IParser0 a = IParser0 (Parser a) (Printer0 a)

It is not an instance of ``Functor`` (thus neither of ``Applicative`` nor
``Monad``) due to ``Printer0 a`` being contravariant with respect to ``a``.

Let us reflect this difference in variance by generalizing the invertible
parser type, with a parameter ``x`` in negative occurences, and ``a`` in
positive occurences:

TODO: explain negative/positive. Basically contravariant/covariant.

\begin{code}
data IParser1 x a = IParser1 (Parser a) (Printer0 x)

asParser1 :: IParser1 x a -> Parser a
asParser1 (IParser1 p _) = p

asPrinter1 :: IParser1 x a -> Printer0 x
asPrinter1 (IParser1 _ q) = q
\end{code}

``IParser0 a`` is equivalent to ``IParser1 a a``.

\begin{code}
type IParser1' a = IParser1 a a

iparser0to1 :: IParser0 a -> IParser1' a
iparser0to1 (IParser0 p q) = IParser1 p q
\end{code}

Let us translate the elementary parsers ``digits0`` and ``whitespace0``.
The following sections will demonstrate a different way to compose them.

\begin{code}
digits1 :: IParser1' String
digits1 = iparser0to1 digits0

whitespace1 :: IParser1' ()
whitespace1 = iparser0to1 whitespace0
\end{code}

Profunctors
-----------

We can map over each parameter independently, the first "contravariantly",
the second "covariantly". We call such a type a *profunctor*.

\begin{code}
class Profunctor f where
  lmap :: (x -> y) -> f y a -> f x a
  rmap :: (a -> b) -> f x a -> f x b

instance Profunctor IParser1 where
  lmap g (IParser1 p q) = IParser1 p (mapPrinter0 g q)
  rmap f (IParser1 p q) = IParser1 (mapParser f p) q
\end{code}

Applying two functions at once results in a function with
a definition identical to ``imap`` (up to the order of arguments), but with a
more general type:

\begin{code}
dimap :: Profunctor f => (x -> y) -> (a -> b) -> f y a -> f x b
dimap g f = lmap g . rmap f
\end{code}

Demonstration
+++++++++++++

We can now define ``int1`` from ``digits1``, equivalent to ``int0``.

\begin{code}
int1 :: IParser1' Int
int1 = dimap show read digits1
\end{code}

Profunctors are functors
++++++++++++++++++++++++

A profunctor is a covariant functor with respect to its second argument:

\begin{code}
instance Functor (IParser1 x) where
  fmap = rmap
\end{code}

Applicative functors and monoids
--------------------------------

Invertible parsers can also be sequenced via an ``Applicative`` instance.
``Parser`` is already an instance of ``Applicative``. ``Printer0``
is not an instance of ``Applicative``, but we only need it to be a ``Monoid``.

``Printer0 x``, equivalent to the type of functions ``x -> String``, is a monoid
where the binary operation is the pointwise concatenation of strings.

\begin{code}
instance Monoid (Printer0 x) where
  -- Identity element
  mempty :: Printer0 x
  mempty = Printer0 $ \_ -> ""

  -- Associative operation
  mappend :: Printer0 x -> Printer0 x -> Printer0 x
  mappend p p' = Printer0 $ \x ->
    runPrinter0 p x ++
    runPrinter0 p' x
\end{code}

The binary operation of that monoid seems to be the only reasonable[#nonsense]_
implementation of the printer component of ``(<*>)`` for ``IParser1``, given its
type.

.. [#nonsense]

  Non reasonable implementations include ignoring the printer in one of the
  operands and doing nonsensical combinations of strings instead
  of a simple concatenation.

\begin{code}
instance Applicative (IParser1 x) where
  pure a = IParser1 (pure a) mempty

  (<*>) :: IParser1 x (a -> b) -> IParser1 x a -> IParser1 x b
  pqf <*> pqa = IParser1 pb qb
    where
      pb = asParser1 pqf <*> asParser1 pqa
      qb = asPrinter1 pqf <> asPrinter1 pqa
      -- (<>) = mappend
\end{code}

Partial printers
++++++++++++++++

The type of the binary operation
``(<>) :: Printer0 x -> Printer0 x -> Printer0 x`` seems surprising at first: what
use is printing the same value of type ``x`` twice?
The answer is that a ``Printer0 x`` does not necessarily print a complete
representation of ``x``.
It may be a *partial printer* of ``x``.

For instance, given a printer ``q :: Printer0 x``, we can construct
``(mapPrinter0 fst q) :: Printer0 (x, y)``
printing only the first component of a given pair.
We can similarly obtain a printer for the second component, and finally
combine them.

\begin{code}
pairPrinter0 :: Printer0 x -> Printer0 y -> Printer0 (x, y)
pairPrinter0 qx qy = mapPrinter0 fst qx <> mapPrinter0 snd qy
\end{code}

Applicative style sequences parsers concisely, allowing users
to provide their own functions to combine results. Here they are
simply put in a pair.

\begin{code}
pairParser :: Parser a -> Parser b -> Parser (a, b)
pairParser pa pb = (,) <$> pa <*> pb
\end{code}

Note that ``pairParser`` and ``pairPrinter0`` are equal to ``(<.>)``. The point
here is that ``Monoidal`` simply turns out to be a composition of more
elementary abstractions. We already mentioned that ``Monoidal`` and
``Applicative`` are equivalent for types which are covariant functors (e.g.,
``Parser``).
Above, ``pairPrinter0`` shows that a type which is both a contravariant functor
and a monoid is also a monoidal functor (the identity morphism ``pure'`` is
equal to ``\_ -> mempty``).

Below, ``pair`` combines these implications, applying ``lmap`` (renamed as the infix
operator ``(=.)`` for a record-like notation) to obtain two values

.. code:: haskell

  (fst =. pqa) :: f (x, y) a
  (snd =. pqb) :: f (x, y) b

under the same context ``f (x, y)`` which can then be combined with the
applicative product ``(<*>)``, using the products of parsers (``Applicative``)
and printers (``Monoid``) when ``f ~ IParser1``.

\begin{code}
(=.) :: Profunctor f => (x -> y) -> f y a -> f x a
(=.) = lmap

-- Very general type
pair
  :: (Profunctor f, Applicative (f (x, y)))
  => f x a -> f y b -> f (x, y) (a, b)
pair pqa pqb =
  (,)
    <$> (fst =. pqa)
    <*> (snd =. pqb)
\end{code}

.. code:: haskell

  -- Specializes to a (<.>)-looking type
  pair1 :: IParser1' a -> IParser1' b -> IParser1' (a, b)

  -- Expanded type
  pair1 :: IParser1 a a -> IParser1 b b -> IParser1 (a, b) (a, b)

Applicative functors are in fact a generalization of monoids.
Indeed, the ``Const`` type (*constant type function*) turns monoids into
applicative functors.

\begin{code}
data Const w a = Const w

instance Functor (Const w) where
  fmap _ (Const w) = Const w

instance Monoid w => Applicative (Const w) where
  pure _ = Const mempty
  Const w <*> Const w' = Const (w <> w')
\end{code}

Thus, ``IParser1 x _`` is not an applicative functor by any fortuitous accident,
but because it is actually the product of two applicative
functors (``Parser _`` and ``Const (Printer0 x) _``, or perhaps
``x -> Const String _``).

Demonstration
+++++++++++++

We no longer need a new ``(.>)`` operator, we can now reuse ``Applicative``'s
``(*>)``.

With ``(=.)`` (i.e., ``lmap``), we apply the ``unit`` function to the
``whitespace1`` invertible parser, indicating that it produces/requires no
information.

\begin{code}
unit :: x -> ()
unit _ = ()

pairInt1 :: IParser1' (Int, Int)
pairInt1 =
  (,)
    <$> (fst =. int1)
    <*> (snd =.
          ((unit =. whitespace1) *> int1))
\end{code}

A monadic printer
-----------------

``Printer0 x`` is not a monad, we shall replace it with a type which is one.
Recall that ``Const`` creates an applicative functor out of a monoid,
but since its second type parameter is ignored, there is no way to
implement a monadic "bind" operator ``(>>=)``.

The writer monad
++++++++++++++++

The *writer monad* arises out of any monoid. Values are annotated
with a *log*, an element of some monoid ``w``. The ``Monoid`` structure
provides an empty log for pure values, and an operation to append logs
when combining values with ``(<*>)`` or ``(>>=)``.

\begin{code}
data Writer w a = Writer w a

-- The embedding must now have a restricted type,
-- as opposed to Const :: w -> Const w a.
write :: w -> Writer w ()
write w = Writer w ()

runWriter :: Writer w a -> w
runWriter (Writer w _) = w

instance Functor (Writer w) where
  fmap f (Writer w a) = Writer w (f a)

instance Monoid w => Applicative (Writer w) where
  pure a = Writer mempty a
  Writer wf f <*> Writer wa a = Writer (wf <> wa) (f a)

instance Monoid w => Monad (Writer w) where
  Writer wa a >>= toWb =
    let Writer wb b = toWb a
    in Writer (wa <> wb) b
\end{code}

The new printer
+++++++++++++++

The original ``Printer0`` can also be seen as the composition of the reader
(``x -> _``) and the constant (``Const String _``) functors: for any ``a``,
``Printer0 x a`` is equivalent to ``x -> Const String a``.

The new ``Printer`` owes its instances of ``Functor``/``Applicative``/``Monad``
to its being the composition of reader (``x -> _``) and writer
(``Writer String _``).

\begin{code}
data Printer x a = Printer (x -> Writer String a)

runPrinter :: Printer x a -> x -> String

-- Instances in the appendix:
-- Profunctor, Functor, Applicative, Monad.
\end{code}

Our final version ``IParser`` of invertible parsers is: a parser of ``a`` and a
printer of ``a`` contained in ``x``.
More precisely, as a printer, it accepts an argument ``x``, from which it
*extracts* a value ``a``, *prints* it, and *returns* it (so that it can be used
with ``(>>=)``).
An ``IParser x a`` is the product of two monads, and therefore it is a monad.


\begin{code}
data IParser x a = IParser (Parser a) (Printer x a)

asParser :: IParser x a -> Parser a
asPrinter :: IParser x a -> Printer x a

-- Instances in the appendix:
-- Profunctor, Functor, Applicative, Monad.

type IParser' a = IParser a a
\end{code}

Since ``whitespace1`` is always going to be used as ``(unit =. whitespace1)``,
we might as well include that in its translation to ``whitespace``.
Parametricity tells us from just its type that ``whitespace`` uses no
information from the input ``x`` so it might as well be ``()``, but
polymorphism makes it more convenient to use.

\begin{code}
iparser1to_ :: IParser1' a -> IParser' a
iparser1to_ (IParser1 p q) = IParser p q'
  where
    q' = Printer $ \a -> Writer (runPrinter0 q a) a

int :: IParser' Int
int = iparser1to_ int1

whitespace :: IParser x ()
whitespace = (unit =. iparser1to_ whitespace1)
\end{code}

Demonstration
+++++++++++++

Let us write again an invertible parser of lists.
We still need a special ``replicate1`` function.
``(:)`` is the constructor of lists used as a regular identifier.

In contrast with ``IParser0`` functions such as ``replicate0``,
we no longer need to construct/deconstruct intermediate tuples,
instead we can use normal constructors and accessors straightforwardly.

\begin{code}
replicate1
  :: (Profunctor f, Applicative (f [x]))
  => Int -> f x a -> f [x] [a]
replicate1 0 _ = pure []
replicate1 n pq =
  (:)
    <$> (head =. pq)
    <*> (tail =. replicate1 (n - 1) pq)
\end{code}

.. code:: haskell

  -- Specializes to
  replicate1 :: Int -> IParser' a -> IParser' [a]

Since ``IParser'`` is an instance of ``Monad``, we can use Haskell's do-notation,
which desugars to expressions using ``(>>=)``.

\begin{code}
intList1 :: IParser' [Int]
intList1 = do
  n <- length =. int
  replicate1 n (whitespace *> int)
\end{code}

----

Appendix
========

``Printer`` instances

\begin{code}
-- :: Printer x a -> x -> String
runPrinter q x = runWriter (runPrinter' q x)

runPrinter' :: Printer x a -> x -> Writer String a
runPrinter' (Printer q_) = q_

instance Profunctor Printer where
  lmap g (Printer q_) = Printer (q_ . g)
  rmap = fmap

instance Functor (Printer x) where
  fmap f (Printer q_) = Printer $ \x ->
    fmap f (q_ x)

instance Applicative (Printer x) where
  pure a = Printer $ \_ -> pure a
  Printer qf_ <*> Printer qa_ = Printer $ \x ->
    qf_ x <*> qa_ x

instance Monad (Printer x) where
  Printer qa_ >>= toqb = Printer $ \x ->
    let toWb a = runPrinter' (toqb a) x
    in qa_ x >>= toWb
\end{code}

``IParser`` instances

\begin{code}
asParser (IParser p _) = p
asPrinter (IParser _ q) = q

instance Profunctor IParser where
  lmap g (IParser p q) = IParser p (lmap g q)
  rmap = fmap

instance Functor (IParser x) where
  fmap f (IParser p q) = IParser (fmap f p) (fmap f q)

instance Applicative (IParser x) where
  pure a = IParser (pure a) (pure a)
  pqf <*> pqa = IParser pb qb
    where
      pb = asParser pqf <*> asParser pqa
      qb = asPrinter pqf <*> asPrinter pqa

instance Monad (IParser x) where
  pqa >>= topqb = IParser pb qb
    where
      pb = asParser pqa >>= (asParser . topqb)
      qb = asPrinter pqa >>= (asPrinter . topqb)
\end{code}
