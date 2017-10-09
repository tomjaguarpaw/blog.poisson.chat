---
title: Coupled reader and writer
---

Monadic profunctors work to compose invertible parsers and lenses in very
similar ways. Here I present a perspective unifying the two, and a spectrum
of transformations inbetween.

First, let me outline another example which got me on this track.

Zipper monad
============

\begin{code}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE FlexibleContexts #-}

module Reader.Writer.Profunctor where

import qualified Control.Monad.Reader as R
import Control.Monad.State
import Data.Profunctor
\end{code}

Zippers
-------

\begin{code}
data Tree a = Leaf | Node (Tree a) a (Tree a)
  deriving (Eq, Show)

isLeaf, isNode :: Tree a -> Bool

isLeaf Leaf = True
isLeaf _ = False

isNode (Node _ _ _) = True
isNode _ = False

data Cxt a = L a (Tree a) | R (Tree a) a

data Zipper a = Zipper [Cxt a] (Tree a)

toZipper :: Tree a -> Zipper a
toZipper = Zipper []

toTree :: Zipper a -> Tree a
toTree (Zipper [] t) = t
toTree (Zipper (L a r : cxt) l) = toTree (Zipper cxt (Node l a r))
toTree (Zipper (R l a : cxt) r) = toTree (Zipper cxt (Node l a r))
\end{code}

A zipper represents a "position" within a tree, allowing fast operations around
that position. If we're not at a leaf position, we can focus further down,
in the left or right subtree.

\begin{code}
unzipZ :: Zipper a -> (Zipper a, Zipper a)
unzipZ (Zipper cxt (Node l a r)) =
  (Zipper (L a r : cxt) l, Zipper (R l a : cxt) r)
unzipZ (Zipper _ Leaf) = error "Can't unzip leaf."
\end{code}

Or we can focus back up if we're not at the root.

\begin{code}
zipZ :: Zipper a -> Zipper a
zipZ (Zipper (L a r : cxt) l) = Zipper cxt (Node l a r)
zipZ (Zipper (R l a : cxt) r) = Zipper cxt (Node l a r)
zipZ (Zipper [] _) = error "Can't zip root."
\end{code}

We can navigate monadically in a tree using a ``Zipper`` as state.

\begin{code}
newtype ZipperM e x a = ZipperM (State (Zipper e) a)
  deriving (Functor, Applicative, Monad)
\end{code}

We can look where we are currently, whether it is a ``Node`` containing
a value or an empty ``Leaf``.

\begin{code}
look :: ZipperM e x (Maybe e)
look = ZipperM $ do
  Zipper _ t <- get
  pure $ case t of
    Leaf -> Nothing
    Node _ e _ -> Just e

\end{code}

And we can move around using monadic actions.

\begin{code}
moveLeft, moveRight, moveUp :: ZipperM e x ()
moveLeft  = ZipperM (modify (fst . unzipZ))
moveRight = ZipperM (modify (snd . unzipZ))
moveUp    = ZipperM (modify zipZ)
\end{code}

Here's a traversal of the right spine of a tree.

\begin{code}
traverseRightSpine :: ZipperM e x [e]
traverseRightSpine = do
  e' <- look
  case e' of
    Nothing -> pure []
    Just e ->
      moveRight *>
      ((e :) <$> traverseRightSpine)
\end{code}

We can run ``ZipperM`` actions to "read" trees to values.

\begin{code}
runZipperM :: ZipperM e x a -> Tree e -> a
runZipperM (ZipperM f) = evalState f . toZipper

aTree :: Tree Int
aTree = Node (Node Leaf 0 Leaf) 1 (Node (Node Leaf 2 Leaf) 2 Leaf)

xs :: [Int]
xs = runZipperM traverseRightSpine aTree
-- [1,2]
\end{code}

Let's use our profunctor technique to convert back values to trees.
In fact, we get a way to update trees with a value, but we
can also use this to generate trees from a single ``Leaf``.

\begin{code}
newtype ReZipperM e x a = ReZipperM (R.ReaderT x (State (Zipper e)) a)
  deriving (Functor, Applicative, Monad)

runReZipperM :: ReZipperM e x a -> x -> Tree e -> Tree e
runReZipperM (ReZipperM f) x t =
  toTree $ f `R.runReaderT` x `execState` toZipper t

-- ZipperM = State (Zipper e) a
-- ReZipperM = s -> State (Zipper e) a
\end{code}

\begin{code}
instance Profunctor (ZipperM e) where
  rmap = fmap
  lmap _ (ZipperM f) = ZipperM f

instance Profunctor (ReZipperM e) where
  rmap = fmap
  lmap f (ReZipperM g) = ReZipperM (R.withReaderT f g)

class Poke p where
  poke :: p e (Maybe e) (Maybe e)
  left :: p e x ()
  right :: p e x ()
  up :: p e x ()

instance Poke ZipperM where
  poke = look
  left = moveLeft
  right = moveRight
  up = moveUp

instance Poke ReZipperM where
  poke = ReZipperM $ do
    e_ <- R.ask
    modify $ \(Zipper cxt t) ->
      Zipper cxt $ case (e_, t) of
        (Nothing, _) -> Leaf
        (Just e, Leaf) -> Node Leaf e Leaf
        (Just e, Node l _ r) -> Node l e r
    pure e_
  left  = ReZipperM (modify (fst . unzipZ))
  right = ReZipperM (modify (snd . unzipZ))
  up    = ReZipperM (modify zipZ)
\end{code}

And here is the traversal again, but now polymorphic.

\begin{code}
rightSpine
  :: (Poke p, Profunctor (p e), Monad (p e [e]))
  => p e [e] [e]
rightSpine = do
  e' <- lmap safeHead poke
  case e' of
    Nothing -> pure []
    Just e -> fmap (e :) . lmap tail $ right *> rightSpine

safeHead :: [a] -> Maybe a
safeHead [] = Nothing
safeHead (a : _) = Just a

ys :: [Int]
ys = runZipperM rightSpine aTree

-- Write a new spine.
anotherTree :: Tree Int
anotherTree = runReZipperM rightSpine [4, 5, 6, 7] aTree

testTrees :: IO ()
testTrees = do
  print xs
  print ys  -- Should be equal.
  print aTree
  print anotherTree
\end{code}

We can use the same code to read from and write to trees.

Partial Sources and Coupling
============================

My bidirectional examples all have a common point: there is a **source** type
which is read from in one direction, and written to in another.
Parsers and printers read and write strings, a lens gets and puts views from
and into the source, and the zipper monads above read and write trees.

We can also compare the way a "reader" can correspond to a "writer". In order
to reuse the same code, the writer has to behave quite like the reader while
having only partial information about the source, since the writer is the
one producing it.

We can represent this information in a *poset of partial sources*
(i.e., "partially defined sources") ordered by definedness.
``s > t`` if ``s`` is "more defined" than ``t``.
There is a *bottom value* ``Bot`` smaller than any other corresponding to
the absence of information.
Another way to look at this is that these partial sources represent
sets of fully defined sources, ordered by inclusion: a value ``s`` is more
defined than ``t`` if ``s`` represents a subset of sources of ``t``;
``Bot`` represents the set of all sources.

Printers are associated with a poset of *prefixes*, which can be open- or
close-ended (depending on whether the last element is ``Bot`` or ``Nil``). A
close-ended prefix represents a single string (it is a "fully defined" value),
while an open-ended one represents all strings it is a prefix of.

\begin{code}
data Prefix
  = PrefixBot
  | PrefixCons Char Prefix
  | PrefixNil

prefixLEq :: Prefix -> Prefix -> Bool
prefixLEq PrefixBot _ = True
prefixLEq PrefixNil PrefixNil = True
prefixLEq (PrefixCons a p) (PrefixCons b q) =
  a == b && prefixLEq p q
prefixLEq _ _ = False
\end{code}

``ReZipperM`` has a poset of "tree prefixes".

\begin{code}
data TreePx e
  = TreePxBot
  | TreePxLeaf
  | TreePxNode (TreePx e) e (TreePx e)

treePxLEq :: Eq e => TreePx e -> TreePx e -> Bool
treePxLEq TreePxBot _ = True
treePxLEq TreePxLeaf TreePxLeaf = True
treePxLEq (TreePxNode l e r) (TreePxNode l' e' r') =
  e == e' && treePxLEq l l' && treePxLEq r r'
treePxLEq _ _ = False
\end{code}

Lenses can live with lots of different posets. Using the set of values
interpretation, the most general representation of partial sources of
type ``s`` is simply as subsets, or indicator functions ``s -> Bool``.
In the perspective presented here, lenses thus generalize the preceding two
examples.

\begin{code}
-- Power set of a.
type Partial s = s -> Bool
\end{code}

We say that a source ``s`` completes ``p :: Partial a`` if ``p s = True``,
i.e., ``s`` belongs to the set of values represented by the partial value
``p``.

A **reader** maps a fully defined source to a value:

\begin{code}
type Reader s a = s -> a
\end{code}

A **writer** maps a value and a partial source to a more defined
source. It may not be fully defined, in which case a domain-specific
completion method must be provided, e.g., using a default value to fill
undefined holes.

\begin{code}
type Writer s x = x -> Monotonic s

-- Makes a partial value more defined.
type Monotonic s = Partial s -> Partial s
\end{code}

Note that ``Monotonic Source`` is a monoid, hence "writer".

We say that ``r :: Reader source value`` and ``w :: Writer source value``
are **coupled** if if writing then reading results in the same value.

  For all ``v :: value``, ``p :: Partial source``, and ``s :: source``,
  if ``s`` completes ``w v p``, then ``r s = v``.

We may also consider the other identity, that reading a value from an initial
source and then writing it results in the same source, up to some completion,
but this is often too strong a requirement.
For instance, parsers can read many strings to the same AST, if they differ
only in whitespace for example, but one only needs a (pretty-)printer to write
each AST as a single source string, discarding other alternatives.

The type of readers is a monad, but the type of writers is not, because ``x``
is in negative position.

A **rewriter** is a writer with an extra function.
We can make this type a monad with respect to the last parameter,
which is the result type of the function.

\begin{code}
type Rewriter s x a = (x -> Monotonic s, x -> a)
\end{code}

We thus reformulate **coupling** between
``r :: Reader source value`` and ``(w, f) :: Rewriter source unvalue value``.

  For all ``x :: unvalue``, ``p :: Partial source``, and ``s :: source``,
  if ``s`` completes ``w x p``, then ``r s = f x``.

``pure`` actions are clearly coupled.
We can also check that coupling is *preserved* by ``lmap`` and ``(>>=)``.

.. code:: haskell

  pure :: a -> (Reader s a, Rewriter s x a)

  lmap
    :: (y -> x)
    -> (Reader s a, Rewriter s x a)
    -> (Reader s a, Rewriter s y a)

  (>>=)
    :: (Reader s a, Rewriter s x a)
    -> (a -> (Reader s b, Rewriter s x b))
    -> (Reader s b, Rewriter s x b)

Inconsistency
-------------

A rewriter may fail because it tries to write content which is inconsistent
with known information. That inconsistency can be represented by the greatest
value ``Top``, associated with no fully defined value.

\begin{code}
top :: Partial a
top _ = False
\end{code}

Cursor
------

``ZipperM`` and parsers, both hold a **cursor** to the location from
which values are read and to which they are written.
``ZipperM`` provides specialized actions to move the cursor around (``left``,
``right``, ``up``), while the parser implicitly moves the cursor forward as the
input is consumed.

This can be represented in our model as a state transformer on top
of ``Reader`` and ``Rewriter``, containing that cursor as state.

