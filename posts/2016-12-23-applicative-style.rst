---
title: Applicative style programming with profunctors
---

Quite unusually, this post is not written in Literate Haskell.

Applicative style
=================

Applicative functors allow less expressiveness than monads,
but are more general: every monad is an applicative functor.

A commonly mentionned benefit of programming with applicative
functors is that they allow more optimizations to take place,
in particular because the applicative product ``(<*>)`` can
execute its two arguments "in parallel".

.. code:: haskell

  (<*>) :: Applicative f => f (a -> b) -> f a -> f b

In contrast, the monadic bind ``(>>=)`` expects an arbitrary function
as its second argument, which is quite opaque.
This forces a sequential execution, where the first operand must be evaluated
so that the second one can be applied to its result.

.. code:: haskell

  (>>=) :: Monad f => f a -> (a -> f b) -> f b

*Applicative style* relies on the ``Applicative`` and ``Alternative`` type
classes; the former is actually a superclass of the latter.

Can we use this style to program bidirectionally with profunctors?
In fact, my previous posts already show how to generalize ``Applicative``.
Here we shall focus on extending that generalization to work with
``Alternative``.

Outline of naive parsers and printers
-------------------------------------

A parser typically uses ``Alternative`` to parse a sum type, with one
branch for each constructor.

.. code:: haskell

  data Term
    = Var Int
    | Lambda Int Term
    | App Term Term

  parseTerm :: Parser Term
  parseTerm
    =   parseVar
    <|> parseLambda
    <|> parseApp

A printer decides the branch to take by pattern matching.

.. code:: haskell

  printTerm :: Term -> String
  printTerm t =
    case t of
      Var _ -> printVar t
      Lambda _ _ -> printLambda t
      App _ _ -> printApp t

Bidirectional programming
-------------------------

Let us imagine we have invertible parsers for each alternative,
merging ``parseVar`` and ``printVar``, etc.

.. code:: haskell

  data IParser x a

  var, lambda, app :: IParser Term Term

The final parser would look like this:

.. code:: haskell

  term :: IParser Term Term
  term
    =   isVar    =? var
    <|> isLambda =? lambda
    <|> isApp    =? app

with some yet unknown operator ``(=?)`` and functions ``isVar``, ``isLambda``,
``isApp``.

Filter
------

Each branch should *filter* the input term, such that if it doesn't have the
right constructor, then the current branch fails and control flows to the
next branch.

Filtering can obviously enough be done with a boolean predicate.

.. code:: haskell

  isVar (Var _) = True
  isVar _ = False

  ...

Then, we expect a signature similar to the standard ``filter`` on lists.
The naive solution is just to put this in a type class.

.. code:: haskell

  class Profunctor p => Filterable p where
    (=?) :: (x -> Bool) -> p x a -> p x a

But this lacks the elegance of previous "high-level" abstractions.

Instead, consider that ``Profunctor`` gives us ``lmap``.

.. code:: haskell

  lmap :: (y -> x) -> p x a -> p y a

The combination of ``lmap`` and ``(=?)`` (filter) is in fact equivalent to:

.. code:: haskell

  filterMap :: (y -> Maybe x) -> p x a -> p y a

The type of partial functions ``y -> Maybe x`` is essentially what the
Invertible Syntax Descriptions paper uses to work with its own redefinition of
``Alternative`` (removing the ``Applicative`` superclass constraint),
as one component of "partial isomorphisms".

``filterMap`` should satisfy some laws:

.. code:: haskell

  filterMap (f >=> g) = filterMap f . filterMap g
  filterMap pure = id

So ``filterMap`` actually represents a functor; its domain is the Kleisli
category associated with the ``Maybe`` monad.

Contravariant functors
======================

We shall generalize ``Profunctor``. Focusing on the first type parameter of
``p``, we have that ``p`` must be a contravariant functor, from some arbitrary
category associated with ``p``, here called ``First p``. In comparison,
``Profunctor`` specializes it to the ``Hask`` category of pure functions
(``First p = (->)``).

The ``Category`` type class can be found in ``Control.Category``, in ``base``.
The ``type`` syntax is allowed here by the ``TypeFamilies`` extension,
allowing one to write type-level functions to some extent.

.. code:: haskell

  class Category (First p) => Contravariant p where
    type First p :: * -> * -> *
    lmap :: First p y x -> p x a -> p y a

Maybe
-----

In the case of an applicative parser, its instance may use the
``Kleisli Maybe`` category to allow mappings to fail:

.. code:: haskell

  newtype Kleisli m y x = Kleisli (y -> m x)

  instance Monad m => Category (Kleisli m)

  instance Contravariant IParser where
    type First IParser = Kleisli Maybe
    lmap :: Kleisli Maybe y x -> IParser x a -> IParser y a
    lmap = (...)

A derived function can take care of unwrapping the ``Kleisli`` newtype in
Haskell.

.. code:: haskell

  filterMap
    :: (Contravariant p, First p ~ Kleisli m, Monad m)
    => (y -> m x) -> p x a -> p y a
  filterMap = lmap . Kleisli

Pure functions
--------------

Of course, there are profunctors which cannot fail, the obvious one being
the function type ``(->)``.

.. code:: haskell

  instance Contravariant (->) where
    type First (->) = (->)
    lmap :: (y -> x) -> (x -> a) -> (y -> a)
    lmap f g = g . f

However, ``Contravariant`` may seem like too big of a generalization. In
particular, we have lost the ability to map a pure function in general when the
domain ``First p`` is not ``(->)``.

Arrows
------

We can use the fact that pure functions can still be lifted
as Kleisli arrows.
One fitting structure is arrows, as found in ``Control.Arrow``, in ``base``,
it is situated somewhere between applicative functors and monads on the
abstraction ladder, but we are more particularly interested in one
method it provides: ``arr :: Arrow p => (y -> x) -> p y x``.

.. code:: haskell

  (=.)
    :: (Contravariant p, Arrow (First p))
    => (y -> x) -> p x a -> p y a
  (=.) = lmap . arr

There may be interesting non-arrow categories for bidirectional programming
with profunctors, but I can't think of any at the moment.

Using Kleisli arrows for the ``Maybe`` monad allows printers to fail for
certain inputs.
Monads are a very general notion, can we find uses for other effects?

State
-----

One situation where we may need to perform side-effects with ``lmap``
is when the data we are working on is represented in some indirect way,
e.g., with explicit pointers.

A more concrete example is *hash consing*: sharing values which are
structurally equal. Deconstructing a hash-consed value may require a lookup in
memory. Then we can imagine a hypothetical parser working in some hash consing
monad ``H``.

.. code:: haskell

  data HIParser x a

  instance Contravariant HIParser where
    type First HIParser = Kleisli (MaybeT H)
    lmap :: Kleisli (MaybeT H) y x -> HIParser x a -> HIParser y a

Unrolling the type definitions, the type of ``lmap`` is equivalent to
the following, with an arrow combining state and exception.

.. code:: haskell

  lmap :: (y -> H (Maybe x)) -> HIParser x a -> HIParser y a

I have written `a more complete example`_ of that in the new `repository`_
summarizing my current work as a Haskell package: ``profunctor-monad``.

The bodies of two equivalent parsers are copied below, the first one with a
monadic definition, the second one with a (primarily) applicative definition.

.. code:: haskell

  -- type p :: (* -> *) -> * -> * -> *
  -- A monad transformer with parsing/printing functionality (via ``IParser``).
  --
  -- type M :: * -> *
  -- A monad for hash consing and exceptions (for parse errors).
  --
  -- type P (p M) I = p M I I
  ppTree
    :: forall p
    .  (Monad1 (p M), IParser (p M), First (p M) ~ Kleisli M, PMonadTrans p)
    => P (p M) I
  ppTree = with @Monad @(p M) @TreeI $ uncons =: do
    c0 <- firstChar =. anyChar
    case c0 of
      '0' -> lift leaf
      '1' -> do
        i <- c1 =. ppTree
        j <- c2 =. ppTree
        lift (node i j)
      _ -> fail "Invalid character"
    where
      firstChar Leaf = '0'
      firstChar (Node _ _) = '1'
      c1 (Node i _) = i
      c2 (Node _ j) = j

  ppTree2
    :: forall p
    .  ( Alternative1 (p M), Monad1 (p M), PMonadTrans p
       , IParser (p M), First (p M) ~ Kleisli M)
    => P (p M) I
  ppTree2 =
    with @Alternative @(p M) @TreeI $
      uncons =:
        (   (guard . isLeaf) =: char '0' *> lift leaf
        <|> (guard . isNode) =: char '1' *> ppNode'
        )
    where
      ppNode' = with @Monad @(p M) @TreeI $ do
        i <- c1 =. ppTree2
        j <- c2 =. ppTree2
        lift (node i j)

      c1 (Node i _) = i
      c2 (Node _ j) = j

  -- Maybe helpful definitions below.

  -- Unique value identifier.
  data I :: *

  -- Shallow representation of a hash-consed tree.
  data TreeI = Leaf | Node I I

  -- Predicates.
  isLeaf, isNode :: TreeF a -> Bool

  -- Monadic smart constructors.
  leaf :: H I
  node :: I -> I -> H I

.. _a more complete example: https://github.com/Lysxia/profunctor-monad/blob/master/example/hashcons.hs
.. _repository: https://github.com/Lysxia/profunctor-monad
