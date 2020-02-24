---
title: Canonical testing for polymorphic functions
keywords: [haskell, theory, testing, parametricity]
mathjax: true
---

Polymorphism is an essential aspect of reusable code: it describes
programs that can operate on many types of data. Parametric polymorphism,
which can be seen as a dual of encapsulation, also makes programming safer:
encapsulated data can only be accessed through a clearly defined interface, and
prevents accidental nonsensical operations.

If fewer mistakes are possible, then not only does the likeliness of writing
a correct program increase, but hopefully it also becomes easier to check
that the program is actually correct.
*Testing polymorphic properties*  [#TPP]_ cements that intuition: we only need
to test a polymorphic function on a very small subset of its domain.

.. [#TPP]

  `*Testing polymorphic properties*`__.
  Jean-Philippe Bernardy, Patrik Jansson, Koen Claessen.
  ESOP 2010.

__ http://publications.lib.chalmers.se/publication/99387-testing-polymorphic-properties

A particular aspect I would like to clarify is the optimality of the approach
presented in that paper: it seems to carve out a subset of test cases that is
the least redundant in a certain sense.

This blog post gives a formalization of the problem of testing and shows
some examples taking advantage of parametric polymorphism to solve it
efficiently.

Testing
=======

Let \\(\\forall \\alpha. T\\alpha\\to U\\alpha\\) be a parametric
function type. We will leave the quantifier implicit and just write
\\(T\\alpha\\to U\\alpha\\).

The goal of testing is to determine whether an implementation
\\(f : T\\alpha\\to U\\alpha\\)
matches a specification
\\(g : T\\alpha\\to U\\alpha\\),
such that \\(\\forall x. f~x = g~x\\); a straightforward
approach is to test that property with some inputs.
The formal definitions here are tailored to testing polymorphic functions
but they can easily be reformulated in different settings.

  A **test input** \\(x\\) for \\(T\\alpha\\to U\\alpha\\) is a value
  of type \\(T A\\) for some type \\(A\\). Alternatively, it
  is an inhabitant of the **domain** \\(\\exists \\alpha. T\\alpha\\).

In general, we cannot try all inputs: there are infinitely many types \\(A\\)
to instantiate \\(\\alpha\\) with, resulting in overwhelmingly many different
potential test cases.
The problem is thus to find a good set of test inputs.

  A **test set** \\(X\\) for \\(T\\alpha\\to U\\alpha\\) is a set of test
  inputs. Alternatively, it is a subset of \\(\\exists \\alpha. T\\alpha\\).

The main property to look for is that an implementation matches a specification
if and only if all tests pass. This is *completeness*.

  A test set \\(X\\) for \\(T \\alpha \\to U \\alpha\\) is **complete**
  when, for all functions \\(f, g : T \\alpha \\to U \\alpha\\),
  \\[(\\forall x\\in X. f~x = g~x) \\implies f = g.\\]

The whole domain of \\(T\\alpha \\to U\\alpha\\), i.e.,
\\(\\exists \\alpha. T \\alpha\\) defines a complete test set, but as we
mentioned earlier, it is rather wasteful. Here are some examples where we can
have much smaller complete test sets.

Examples
========

\\[\\alpha \\times \\alpha \\to \\alpha\\]

\\(f\\) can return either its first or second argument, independently of
their values. To test it, we only need to apply \\(f\\) to a pair of
distinguishable elements.

\\[X = \\left\\{ \
  (0, 1) : \\mathbb{N} \\times \\mathbb{N} \
\\right\\}\\]

----

\\[\\alpha \\times (\\alpha \\to \\alpha) \\to \\alpha\\]

\\(f\\) can only iterate its second argument on the first a fixed number
of times. A function that counts these iterations does the job.

\\[X = \\left\\{ \
  (0, \\lambda n. n+1) : \\mathbb{N} \\times (\\mathbb{N} \\to \\mathbb{N}) \
\\right\\}\\]

----

Let \\(\\alpha^\\star\\) be the type of lists of \\(\\alpha\\).

\\[\\alpha^\\star \\to \\alpha^\\star\\]

\\(f\\) can drop, duplicate, and move elements from the input list, depending
only on its length, but it can not invent new elements. For every given length,
we only need to apply \\(f\\) to a single list to fully determine its behavior
for all lists of that length.

\\[X = \\left\\{ \
    [~] \
  , [0] \
  , [0,1] \
  , [0,1,2] \
  , [0,1,2,3] \
  , \\dots : \\mathbb{N}^\\star
\\right\\}\\]

----

\\[\\alpha \\to \\alpha \\]

Only the identity function has that type. There's no need to test it.

\\[X = \\emptyset\\]

----

Let \\(\\mathbb{B}\\) be the type of booleans.

\\[\\alpha \\to \\mathbb{B}\\]

There's no way for that function to inspect its argument, so it must
be a constant function. We only need to apply it to one arbitrary
argument, say the unit \\(() : \\unicode{x1D7D9}\\), to obtain that constant.

\\[X = \\left\\{() : \\unicode{x1D7D9}\\right\\}\\]

----

\\[\\alpha \\times (\\alpha \\to \\mathbb{B}) \\to \\mathbb{B}\\]

\\(f\\) can only observe the first argument through the second one.
That type is isomorphic to \\(\\mathbb{B} \\to \\mathbb{B}\\).
We need two inputs to test \\(f\\).

\\[X = \\left\\{ \
    ((), (\\lambda(). \\mathrm{true})) \
  , ((), (\\lambda(). \\mathrm{false})) \
  : \\unicode{x1D7D9} \\times (\\unicode{x1D7D9} \\to \\mathbb{B}) \
\\right\\}\\]

----

Let \\(\\unicode{x1D7D8}\\) be the empty type.

\\[\\alpha + (\\alpha \\to \\unicode{x1D7D8}) \\to \\mathbb{B}\\]

\\(f\\) can only see whether its argument is a \\(\\mathrm{left}\\) or
\\(\\mathrm{right}\\). This example shows that test inputs may not instantiate
the type variable \\(\\alpha\\) identically.

\\[X = \\left\\{ \
  \\begin{aligned} \
    \\mathrm{left}~() & \
  : \\unicode{x1D7D9} + (\\unicode{x1D7D9} \\to \\unicode{x1D7D8}) \\\\ \
    \\mathrm{right}~(\\lambda z.z) & \
  : \\unicode{x1D7D8} + (\\unicode{x1D7D8} \\to \\unicode{x1D7D8}) \
  \\end{aligned} \
\\right\\}\\]

----

\\[\\alpha \\times (\\alpha \\to \\alpha + \\alpha) \\to \\alpha\\]

This type is isomorphic to

\\[\\begin{aligned} \
  & \\alpha \\times (\\alpha \\to (\\mathbb{B} \\times \\alpha)) \\to \\alpha \\\\ \
  & \\alpha \\times (\\alpha \\to \\alpha) \\times (\\alpha \\to \\mathbb{B}) \\to \\alpha \
\\end{aligned}\\]

Using \\(\\alpha\\) and \\(\\alpha \\to \\alpha\\),
we generate some values of type \\(\\alpha\\), and
with \\(\\alpha \\to \\mathbb{B}\\) we assign one boolean to each value.

\\[X = \\left\\{ \
  (0, \\lambda n. n+1, p) \
  : \\mathbb{N} \\times (\\mathbb{N} \\to \\mathbb{N}) \\times (\\mathbb{N} \\to \\mathbb{B}) \
  \\;\\middle|\\; p : \\mathbb{N} \\to \\mathbb{B} \
\\right\\}\\]

----

Extras
------

Some more examples to think about. For the first two, the presence of
multiple type variables does not seem to cause any major issue.

\\[\\begin{aligned} \
  & (\\alpha + \\beta) \\times (\\alpha \\to \\beta) \\to \\beta \\\\ \
  & (\\beta \\to \\alpha) \\times (\\alpha \\to \\beta) \\times \\alpha \\to \\beta \\\\ \
\\end{aligned}\\]
The last one contrasts with previous examples: it also has the shape
\\(T\\alpha \\to U\\alpha\\), but \\(U\\) is no longer covariant; this also
arises by currying examples whose domain is a product, but the output sum type
wrapping functions looks even more puzzling; I haven't given much thought about
this situation.

\\[\\alpha \\to (\\alpha \\to \\alpha) + ((\\alpha \\to \\mathbb{B}) \\to \\mathbb{B})\\]

----

Test sets
=========

There seem to be some common ideas in these examples. For instance, we want to
generate test cases which are just "big enough" to not forget operations done
by the function under test; this corresponds to the concept of initial algebras,
which is involved in *Testing Polymorphic Properties*.

Another idea, which I want to make more precise here, is that the test set
should be as small as possible.

We may ask that the complete test set \\(X\\) should be minimal for set
inclusion, but this isn't quite sufficient to characterize a good test set.
Indeed, consider the following type again:

\\[\\alpha^\\star \\to \\alpha^\\star\\]

Here is another complete test set, it differs from \\(X\\) above in lists of
length 3:

\\[Y = \\left\\{ \
    [~] \
  , [0] \
  , [0,1] \
  , [0,0,1] \
  , [0,1,1] \
  , [0,1,2,3] \
  , \\dots : \\mathbb{N}^\\star
\\right\\}\\]

None of the proper subsets of \\(Y\\) is complete, so it is minimal.
Yet, the test set \\(X\\) shown earlier seems more "efficient" since
it uses only one list of length 3, as opposed to two lists for \\(Y\\).

Subsumption
-----------

The problem of testing as presented at the beginning of this post consists in
distinguishing functions of a given type. To compare the effectiveness of test
inputs, we define **subsumption**. The tests \\([0,0,1]\\) and \\([0,1,1]\\)
are *subsumed* by \\([0,1,2]\\), meaning that the latter one discriminates
polymorphic functions on lists at least as well as the former two:

  A test input \\(x\\) **subsumes** \\(y\\) with respect to
  \\(T\\alpha \\to U\\alpha\\) if
  for all \\(f, g : T \\alpha \\to U \\alpha\\),
  \\[f~x = g~x \\implies f~y = g~y.\\]

Exercise: \\(x : T A\\) subsumes \\(y : T B\\) if and only if \\(f~x\\)
determines \\(f~y\\), i.e., there is a function
\\(\\iota\_{x,y} : U A \\to U B\\) such that for all
\\(f : T \\alpha \\to U \\alpha\\), we have
\\(f~y = \\iota\_{x,y}~(f~x)\\).

As a more general example[#iota]_,
\\(x = [0,\\dots,n-1] : (\\mathbb{N}_{<n})^\\star\\)
subsumes all lists of length \\(n\\) with respect to
\\(\\alpha^\\star \\to \\alpha^\\star\\).
Indeed, thanks to the free theorem for that type, for any list
\\(y : A^\\star\\) of length \\(n\\), we have:

\\[f~y = \\iota\_{x,y}~(f~[0,\\dots,n-1])\\]

where \\(\\iota\_{x,y} : (\\mathbb{N}_{<n})^\\star \\to A^\\star\\) maps every
index in a list to the corresponding element in \\(y\\); in Haskell we can
define it as:

.. code:: haskell

  iota_x :: [a] -> [Int] -> [a]
  iota_x y = fmap (y !!)

.. [#iota]

  The restriction on the type of \\(x\\), with elements in
  \\(\\mathbb{N}_{<n}\\), is so that \\(\\iota\_{x,y}\\) can be total.

Of course, we can lift subsumption into a relation on sets. Above, \\(X\\)
strongly subsumes \\(Y\\):

  A test set \\(X\\) **strongly subsumes** \\(Y\\) (with respect to
  \\(T \\alpha \\to U \\alpha\\)) if every element of \\(Y\\) is subsumed by an
  element of \\(X\\).

On a closer look, it is a bit weird: for instance, \\(Y\\) does not strongly
subsume the domain \\(\\exists\\alpha.\\alpha^\\star\\), even though it looks
much "smaller". This is why this subsumption is "strong".

A somewhat more natural but weaker notion of subsumption generalizes the
original definition (between single test inputs) directly:

  A test set \\(X\\) (**weakly**) **subsumes** \\(Y\\) (with respect to
  \\(T \\alpha \\to U \\alpha\\)) if,
  for all \\(f, g : T \\alpha \\to U \\alpha\\), we have that
  \\(\\forall x \\in X. f~x = g~x\\) implies \\(\\forall y \\in Y. f~y = g~y\\).

Complete test sets weakly subsume each other, so it is not a really useful
notion for our purposes. We can at least factor it out of the definition of
completeness:

  A *complete test set* for \\(T \\alpha \\to U \\alpha\\) is a test set which
  subsumes the domain \\(\\exists \\alpha. T \\alpha\\).

When \\(X\\) subsumes \\(Y\\), every test input \\(y \\in Y\\) is "covered" by
inputs in \\(X\\): the value a function takes at \\(y\\) is determined by
the values at inputs in \\(X\\), but not all of them.
Indeed, we can witness subsumption in a more fine-grained way.

  A **subsumption** \\(S\\) of \\(Y\\) by \\(X\\) (with respect to \\(T\\alpha
  \\to U\\alpha\\)) consists of a subset \\(S_y \\subseteq X\\) for each
  \\(y\\in Y\\), such that \\(S_y\\) subsumes \\(\\{y\\}\\). We denote
  subsumptions by \\(S : Y \\prec X\\).

Subsumptions subsume the previous definitions of subsumption.

1. A subsumption of \\(Y\\) by \\(X\\) exists if and only if \\(X\\) subsumes
   \\(Y\\). (If \\(X\\) subsumes \\(Y\\), then there is a trivial subsumption,
   \\(S_y = X\\).)
2. \\(X\\) strongly subsumes \\(Y\\) if and only if there exists a subsumption
   \\(S : Y \\prec X\\) where \\(S_y\\) is a singleton for all \\(y\\in Y\\),
   i.e., \\(S\\) is actually a function \\(Y \\to X\\).

Subsumptions with respect to a given function type form a category.
Let \\(R : Y \\prec X\\) and \\(S : Z \\prec Y\\) be two subsumptions involving
three test sets \\(X, Y, Z\\).
Their composition \\(RS : Z \\prec Y\\) is given by:

\\[{RS}_z = \\left\\{x \\;\\middle|\\; y \\in S_z, x \\in R_y\\right\\}\\]

Exercise: the composition of subsumptions is a subsumption; composition
is associative, and has identities.[#kleisli]_

.. [#kleisli]

  Viewing subsumptions \\(S : Y \\prec X\\) as functions
  \\(S : Y \\to \\mathcal{P}X\\), that is the Kleisli composition of the power
  set monad \\(\\mathcal{P}\\) (a common representation of non-determinism).
  Thus we have a subcategory of the Kleisli category for the power set monad.

A word about emptiness
++++++++++++++++++++++

For \\(\\alpha \\to \\alpha\\), the empty set is complete because there is only
one value of that type.

  A type \\(T\\alpha\\to U\\alpha\\) is **trivial** if it has at most
  one inhabitant, up to observational equivalence.

A related notion is that of test inputs which provide no information at all.

  A test input \\(x\\) is **isotropic** with respect to
  \\(T\\alpha\\to U\\alpha\\) if the empty set subsumes \\(\\{x\\}\\),
  i.e., \\(\\forall f, g : T\\alpha\\to U\\alpha. f~x = g~x\\).

\\((0,0)\\) is isotropic with respect to \\(\\alpha\\times\\alpha\\to\\alpha\\).
Trivial types are those whose inputs are all isotropic.

Canonical test sets
-------------------

Assume \\(T\\alpha \\to U\\alpha\\) is not trivial.

Ideally, a test set should have no redundancies. Here is one formulation,
which may need some improvement:

  A test set \\(X\\) is a **canonical test set** for \\(T \\alpha \\to U
  \\alpha\\) if every element of the domain \\(\\exists \\alpha. T \\alpha\\)
  is either isotropic or subsumed by only one element of \\(X\\).

Clearly enough, a canonical test set strongly subsumes every test set.
In the examples above, \\(X\\) is a canonical test set.
The test set \\(Y\\) for the list example is not canonical: \\([0,1,2]\\)
is subsumed by neither of \\([0,0,1]\\) or \\([0,1,1]\\) individually, although
the singleton \\(\\{[0,1,2]\\}\\) is subsumed by the pair
\\(\\{[0,0,1], [0,1,1]\\}\\).

I would like to find a characterization (or generalization) of canonical test
sets, justifying their "optimality" categorically. The idea of initial/terminal
objects seems relevant, however in the category described above, subsumptions
are far from unique: in the case of lists, we can easily construct two
subsumptions \\(S, S' : Y \\prec X\\), for example with
\\(S\_{[0,0,1]} = \\{[0,1,2]\\}\\) and \\(S'\_{[0,0,1]} = \\{[0,1,2],[0,1]\\}\\).

Going forward, it appears that we can also compare subsumptions between two
test sets, and this might give us a 2-category to work with.

Future plans
============

Two questions:

1. Does *Testing Polymorphic Properties* define canonical test sets?
   Most likely, yes.
2. What is the relation between "canonical test sets" and "canonical
   forms"[#deceq]_? At a high level, they are similar in that both seek to
   avoid redundancy, which is expressed in one case by subsumption, in the
   other by observational equivalence. Two consequences we expect to come from
   this work are: a more general algorithm to test polymorphic properties and a
   description of canonical forms in System F.

.. [#deceq]

  `*Deciding equivalence with sums and the empty type*`__. Gabriel Scherer. POPL 2017.

__ https://arxiv.org/abs/1610.01213
