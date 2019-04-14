---
title: Randomness in purely functional programs
keywords: [haskell, random]
---

\begin{code}
module Splittable.Generators where

import Control.Monad
import Data.Hashable
\end{code}

Monads of randomness
====================

In Haskell, the standard way to write programs with randomness, like other
effects, is to use a monad. The ``MonadRandom`` type class, from the
package[#MonadRandom]_ of the same name, is a monadic interface
to access a source of randomness.

.. [#MonadRandom]

  http://hackage.haskell.org/package/MonadRandom

Here is a simplified version. It consists of a single method to get a random
integer. More randomness can be obtained by just calling this multiple times.

\begin{code}
class Monad m => MonadRandom m where
  genInt :: m Int
\end{code}

A simple implementation wraps a pseudo-random number generator in
a state monad. Let us first leave the PRNG abstract.

\begin{code}
newtype StateGen g a = StateGen { runStateGen :: g -> (g, a) }
\end{code}

As a monad, it just threads the PRNG through the program.

\begin{code}
instance Monad (StateGen g) where
  return a = StateGen $ \g -> (g, a)
  m >>= f = StateGen $ \g ->
    let (g', a) = runStateGen m g in runStateGen (f a) g'

instance Functor (StateGen g) where fmap = liftM
instance Applicative (StateGen g) where pure = return ; (<*>) = ap
\end{code}

We assume that the PRNG provides a ``next`` function,
which outputs some random value and an updated state.

\begin{code}
class PRNG g where
  next :: g -> (g, Int)
\end{code}

Then ``genInt`` is trivially implemented by ``next``.

\begin{code}
instance PRNG g => MonadRandom (StateGen g) where
  genInt = StateGen next
\end{code}

This implementation has one issue: when we compose two random computations,
like with ``(>>=)``, we must run the first one to get the intermediate state
``g'``, before passing it to the second one, even if it didn't depend on the
former.

Surely, if I have two independent thunks ``(<thunk>, <thunk>)``, random or not,
and I end up needing only the second one, then I shouldn't need to pay for the
first one. This is just laziness.

Splittable PRNG
---------------

A ``next``-based sequential PRNG is definitely not compatible with laziness. What we need
is a *splittable* PRNG[#palka]_. It consists of one method to *split* the state,
and another to *extract* a random value from it.

.. [#palka]

  *Splittable Pseudorandom Random Number Generators using Cryptographic Hashing*,
  K. Claessen, M. Palka, Haskell Symposium 2013 (link__).

__ http://publications.lib.chalmers.se/publication/183348-splittable-pseudorandom-number-generators-using-cryptographic-hashing

\begin{code}
class SPRNG g where
  split :: g -> (g, g)
  extract :: g -> Int
\end{code}

Note that a SPRNG is also a sequential PRNG.

\begin{code}
snext :: SPRNG g => g -> (g, Int)
snext g = let (g', g0) = split g in (g', extract g0)
\end{code}

But a SPRNG can be encapsulated in a different way from ``StateGen``.
We do not have to thread a PRNG state anymore. We are left with a simple
function ``g -> a``, but the ``SPRNG`` constraint now moves into the ``Monad``
instance, to allow splitting the generator between two computations.

\begin{code}
data SplitGen g a = SplitGen { runSplitGen :: g -> a }

instance SPRNG g => Monad (SplitGen g) where
  return a = SplitGen $ \_ -> a
  m >>= f = SplitGen $ \g ->
    let (gm, gf) = split g in
    runSplitGen (f (runSplitGen m gm)) gf

instance SPRNG g => Functor (SplitGen g) where fmap = liftM
instance SPRNG g => Applicative (SplitGen g) where pure = return ; (<*>) = ap
\end{code}

Getting a random value is still straightforward.

\begin{code}
instance SPRNG g => MonadRandom (SplitGen g) where
  genInt = SplitGen extract
\end{code}

In QuickCheck[#QuickCheck]_, the ``Gen`` monad is thus based on a splittable
PRNG for efficient testing of non-strict properties.

.. [#QuickCheck]

  https://hackage.haskell.org/package/QuickCheck

Beyond monads
=============

In Haskell, we usually compose effectful computations *explicitly monadically*.
In particular, the explicitness is sometimes nice, but it also gets in the way
of clarity and simplicity. If I want to add the results of throwing two die,
I would like to write ``die + die``. A very nice compromise seems reachable
with *algebraic effects* [#AlgEff]_: effects are still tracked in types, but
effectful computations do not need special notation. Unfortunately I'm not sure
that technique applies to the method using splittable PRNGs.

.. [#AlgEff]

  Here are three languages with algebraic effects:

  - Eff: http://www.eff-lang.org/
  - Frank: https://arxiv.org/abs/1611.09259
  - Koka: https://github.com/koka-lang/koka

  The latter two were presented at POPL2017.

Anyway, let's try to do things manually to see how they could be improved. We
represent random values explicitly as functions ``g -> a``.

\begin{code}
then_ :: SPRNG g => (g -> a) -> (a -> g -> b) -> g -> b
(m `then_` f) g = f (m gm) gf
  where
    (gm, gf) = split g
\end{code}

Doing this explicitly is risky: we may forget to split, passing ``g`` to both
functions (``f (m g) g``); if we remember to split, we might still accidentally
pass ``gm`` or ``gf`` twice, breaking independence (``f (m gm) gm``).
We could prevent this kind of mistake with a *linear type system* allowing
us to express the constraint that a generator must be used at most once.

Even if it were properly checked, splitting and passing generators around
explicitly becomes boring work quickly, and ``SplitGen`` had precisely the
advantage of making this implicit, but a monadic style adds some amount of
overhead compared to simply applying pure functions.
This is what an ideal imaginary alternative might look like:

.. code:: haskell

  then_ :: ?g => (?g => a) -> (a -> (?g => b)) -> b
  m `then_` f = f m

It is similar to ``ImplicitParams``, but instead of simply passing the
implicit parameter ``?g`` when calling random functions in the body, ``?g``
should be split with each component passed to each call requiring a generator.

The compiler would have to treat these constraints about generators specially.
This certainly seems quite *ad hoc*. I have the idea that this may
not need to be a special case. In Haskell, users can already define certain
kinds of custom constraints and associated rules via type classes, and the
resolution of these constraints according to those rules automatically
generates code, so that the user doesn't need to write it. Could this be
generalized to obtain the aforementioned behavior for implicit splitting
generators?

Roughly, I would like to define new sorts of rules on constraints in a richer
language than Haskell's Prolog-like type classes, in order to finely control
the resolution process and the code generation derived from it (i.e., the
desugaring to dictionary passing).
At some level, this sounds very much like a static analogue of effect handlers:
typechecking code generates various kinds of constraints, and one might write
*handlers* to resolve them.

Appendix: Examples of PRNG
==========================

Pseudo-random number generator
------------------------------

I will not go into details about the formal requirements for such an object,
but here is a simple example of PRNG.
We assume a ``hash`` function given as a primitive.

.. code:: haskell

  hash :: Hashable a => a -> Int

The state consists of the initial seed and a counter.

\begin{code}
type Seed = Int

data G0 = G0 { seed0 :: Seed, counter0 :: Int }

newG0 :: Seed -> G0
newG0 seed = G0 seed 0
\end{code}

Then, ``next`` hashes the pair, yielding a pseudo-random value,
and increments the counter.

\begin{code}
instance PRNG G0 where
  next (G0 seed counter) = (G0 seed (counter + 1), hash (seed, counter))
\end{code}

Splittable PRNG
---------------

Rather than hashing the seed with a counter of how many times ``next``
was called, we will hash it with the information of how a generator
was obtained from ``split``. The seed can be associated with an
infinite binary tree of random values. A generator state is a
position in the tree, we start at the root.

\begin{code}
data G1 = G1 { seed1 :: Seed, path1 :: [Bool] }

newG1 :: Seed -> G1
newG1 seed = G1 seed []
\end{code}

Then ``split`` outputs two positions one level deeper in the tree. A position
in a binary tree is given by a list of booleans describing the path from the
root to that position. We hash the seed and the path to obtain a pseudo-random
value.

\begin{code}
instance SPRNG G1 where
  split (G1 seed path) = (G1 seed (False : path), G1 seed (True : path))
  extract (G1 seed path) = hash (seed, path)
\end{code}
