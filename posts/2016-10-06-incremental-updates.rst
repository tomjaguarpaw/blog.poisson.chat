---
title: Incremental updates for efficient bidirectional transformations
keywords: [haskell, bidirectional]
---

\\[
\\newcommand{\\compose}{\\cdot}
\\DeclareMathOperator*{\\id}{id}
\\DeclareMathOperator*{\\get}{get}
\\DeclareMathOperator*{\\put}{put}
\\DeclareMathOperator*{\\edit}{edit}
\\DeclareMathOperator*{\\affect}{affect}
\\newcommand{\\apply}{\\,}
\\]

I'm taking a look at the paper with the same title. [#incremental]_

.. [#incremental]
  *Incremental Updates for Efficient Bidirectional Transformations.*
  Wang, M., Gibbons, J. and Wu, N. (ICFP'2011).
  Available at: http://dl.acm.org/citation.cfm?id=2034825.

Summary
=======

  The ultimate goal of our framework is to reduce an update of a
  (large) structure into one of a (small) delta (...).

Take a source term \\(s : S\\), and a view \\(v = \\get s : V\\).
We consider an edit \\(e : E_V \\) of the view, given by a function
\\(\\edit e : V \\to V\\) which performs the edit, as well as a function
\\(\\affect e : V \\to V\\) which computes a subterm of the view such that
the edit is contained in it, in the sense that applying
\\(\\edit e \\apply v\\) is equal to extracting \\(w = \\affect e \\apply v\\),
(leaving a hole \\(v / w\\)) then applying the edit on that subterm
\\(\\edit e \\apply w\\), and finally putting it back, leaving the context
surrounding the hole untouched:
\\[\\edit e \\apply v = v / w \\lessdot \\edit e \\apply w.\\]

Assuming some more niceness about the \\(\\get : S \\to V\\) function,
and a corresponding \\(\\put : V \\to S \\to S\\), we can construct
a *change-based* \\(\\put_E : E_V \\to S \\to S\\) which
exploits the locality of the edit, as given by \\(\\affect\\) to make as local
a change as possible to the source term, hopefully with improved performance
compared to a simple \\(\\put\\).

However, the paper mentions this in Section 5, bounding the action of an edit
to a subterm is sometimes ineffective.
For instance, considering a view which is a list, ``0 : 1 : 2 : 3 : []``,
deleting ``1`` results in the list ``0 : 2 : 3 : []``, and the smallest
affected subterm of the initial list is ``1 : 2 : 3 : []``, because only tails
(and individual elements) are subterms of a list.
The issue is that this hardly helps \\(\\put_E\\) perform well,
because as far as it can tell, almost the whole list has changed.

Section 5 mentions an ad-hoc extension of contexts for lists,
so that we can consider actual sublists as subterms:
\\[(l_1, l_2) \\lessdot l = l_1 \\cdot l \\cdot l_2.\\]

Parametricity
=============

The main construction of the paper stems from the observation that
many transformations are contained in a subterm of the view.
If it is a list, subterms are suffixes.
In a way, the \\(\\affect\\) function points to a subtree which
is an *upper-bound* of the locations where changes can take place.

The extension above is additionally motivated by the fact that
a suffix of the list argument is preserved by local operations such as
the deletion of an element.
Thus, we may try to generalize that with a notion of *lower-bounds*:
subtrees that are only moved by the edit, and left unchanged inside.

I would formalize that as follows.
Given a term \\(v : V\\) and a subterm \\(w \\preccurlyeq v\\),
we say that \\(e : E_V\\) is **parametric**
over \\(w\\) in \\(v\\) if:

1.  \\(w \\preccurlyeq \\edit e \\apply v\\),

2.  \\(
    \\forall w' : V,\\;
    \\edit e \\apply (v / w \\lessdot w') = (\\edit e \\apply v) / w \\lessdot w'.
    \\)

Examples
--------

The deletion of ``1`` in the list ``0 : 1 : 2 : 3 : []`` is parametric over
``2 : 3 : []``.

The transformation of an ``if`` expression:

::

    if x
    then y
    else z

to a ``case`` expression:

::

    case x of
      True -> y
      False -> z

is parametric over ``x``, ``y``, and ``z``.
Rules of a rewriting system are generally parametric.

Assuming some kind of continuity about \\(\\get\\),
perhaps similar to the *alignment* property discussed in the paper,
a parametric view transformation might be convertible to a parametric source
transformation.

For instance, on an AST as a view of textual source code,
the transformation above corresponds to substituting the tokens
of an ``if`` expression with those of a ``case`` expression, without
touching those of their bodies.

We can also consider swapping the ``case`` alternatives:

::

    case x of
      False -> z
      True -> y

which corresponds to a similar exchange of text in the source.

That mapping appears straightforward to establish by hand;
this suggests a general pattern to bidirectionalize \\(\\get\\) for parametric
edits.
