---
title: Enumeration of multigraph DFS
---

This is written in Literate Haskell.[#source]_

.. [#source]

  https://bitbucket.org/lyxia/blog.poisson.chat/src/

\begin{code}
module Enumerating.DFS where

import Test.Feat.Enumerate
import Test.Feat.Access
\end{code}

A representation problem
========================

What is a good way to implement graphs?
The problem with standard methods, i.e., adjacency lists and matrices,
is that they are badly structured.

In contrast, trees can be defined inductively:
a (rooted) *tree* is a *vertex* linked via *edges* to some (or no)
smaller trees called its *children*.
This is a good representation because we can easily define operations on trees
recursively.

\begin{code}
data Tree = Vertex [Edge]
type Edge = Tree
\end{code}

To represent more general graphs, we can start with a tree like that,
and encode the remaining edges specially. One simple type of edge
is the *back edge*: linking a vertex to one of its ancestors.
Since there is only one way up, a back edge can simply be encoded as an integer
counting the number of generations separating the vertex from its ancestor.
This is just like de Bruijn indices in lambda terms, and here every vertex
is a binder.

\begin{code}
data TreeB = VertexB [EdgeB]
data EdgeB = TreeB TreeB | BackB Integer
\end{code}

DFS Trees
=========

From any undirected graph, we may restructure it as a tree with back edges
by performing a DFS. In fact, the above type naturally represents DFS of
undirected *multigraphs*, where a vertex can have many back edges
pointing to the same ancestor.
Different DFS can be obtained from the same multigraph,
depending on the chosen root, and the order in which edges are crossed.

Thanks to that inductive definition, we can enumerate such trees. We must
however be careful to avoid back edges pointing past the root of the tree.
This notion of well-formedness is formalized by generalizing it with a
*context*, which is the number of ancestors of the current root.

The ``testing-feat`` package[#testing-feat]_ defines a type ``Enumerate`` to efficiently
enumerate combinatorial species, i.e., sets of things classified by some
notion of size, such that there is finitely many things of a given size.

.. [#testing-feat]

  http://hackage.haskell.org/package/testing-feat

\begin{code}
type Species = Enumerate
\end{code}

We define inductively the combinatorial species of rooted multigraphs with a
context of ``n`` ancestors, with size measured as the number of edges.

\begin{code}
treeB :: Int -> Species TreeB
treeB n = VertexB <$> treeBChildren n
\end{code}

The root costs nothing, and we must then enumerate the species
of lists of children.
We distinguish two subspecies of which this is the sum: the species of no
children and the species of some children.

\begin{code}
treeBChildren :: Int -> Species [EdgeB]
treeBChildren n = noChildren <> someChildren n
\end{code}

The species of no children contains a single object of size 0: the empty list.
In ``treeB`` this corresponds to the graph with no vertices.

\begin{code}
noChildren :: Species [EdgeB]
noChildren = pure []
\end{code}

Making the children pay
-----------------------

The species of some children corresponds to non-empty lists.
They contain at least one element ``child``, followed by an arbitrary
list ``children``.
The first element will use one additional edge to connect to the root;
the ``pay`` combinator adds one to the size of each element in a species.

\begin{code}
someChildren :: Int -> Species [EdgeB]
someChildren n = pay
  (liftA2
    (\ child children -> child : children)
    (treeBChild n)
    (treeBChildren n))
\end{code}

Now, we may obtain a child by following an edge which belong to one of two types.
A tree edge ``(TreeB <$> treeB (n + 1))`` links the current root as the parent
of a new root, which thus has one more ancestor in addition to the previous
ones. A back edge links to one of the ``n`` ancestors.
The auxiliary ``backEdges n`` defines the species with ``n`` elements
``[BackB 0 .. BackB (n - 1)]`` all of size ``0``; the size
of the back edge was already ``pay``-d by ``someChildren``.

\begin{code}
treeBChild :: Int -> Species EdgeB
treeBChild n = (TreeB <$> treeB (n + 1)) <> backEdges n
  where
    backEdges n = fromParts [Finite (toInteger n) (BackB . fromInteger)]
\end{code}

This concludes the definition of ``treeB``. Let us enumerate these graphs
(with no implicit ancestors, i.e., with context ``n = 0``).

\begin{code}
count :: Species a -> [Integer]
count s = [cardinal | (cardinal, _) <- valuesWith s]
\end{code}

In a few seconds we get:

\begin{code}
oeisA258173 = count (treeB 0)

-- [1,1,3,12,58,321,1975,13265,96073,743753,6113769,53086314,
-- 484861924,4641853003,46441475253,484327870652,5252981412262...
\end{code}

See https://oeis.org/A258173.

At the time of writing, the conjecture that this class of graphs is
enumerated by this sequence is not mentioned in the OEIS.
I suspect this also is not too hard to prove.

March 2, 2017. Update:

  Thanks to Antti Karttunen for the proof[#proof]_ that
  these sequences are indeed the same.

.. [#proof]

  http://list.seqfan.eu/pipermail/seqfan/2017-March/017314.html
