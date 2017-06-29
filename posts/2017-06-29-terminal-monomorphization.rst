---
title: A terminal view of testing polymorphic functions
---

Parametricity restricts the behavior of a polymorphic function
\\(\\phi : \\forall \\alpha. T \\alpha \\to U \\alpha\\),
so that, picking one type \\(\\tau\\) and one input value \\(x : T \\tau\\)
and inspecting the result \\(\\phi~x : U\\tau\\) often tells us about what
happens on many other inputs.

To test polymorphic functions, Bernardy et al.[#tpp]_ (2010) have a
monomorphization technique using initial algebras (the "initial view"). They
also conjectured the existence of a dual method based on terminal coalgebras
(the "terminal view"), which I will show in this post.

Initial view
============

We assume that \\(T\\alpha\\) has the form
\\((F\\alpha \\to \\alpha)\\times(G\\alpha\\to X)\\),
for some functors \\(F\\) and \\(G\\) and a non-parametric type
\\(X\\) (i.e., in which \\(\\alpha\\) does not occur), and that \\(U\\) (the
result type) is also a functor. Then, to test a function of type
\\(\\forall\\alpha.(F\\alpha\\to\\alpha)\\times(G\\alpha\\to X)\\to U\\alpha\\),
it suffices to only try inputs where the first argument is the initial
\\(F\\)-algebra, \\(f_0 : F\\mu\\to\\mu\\) (and \\(\\mu\\) is the
"least fixed point" of the functor \\(F\\)). The second argument may
vary freely in the type \\(G\\mu\\to X\\).

.. [#tpp]

  `*Testing polymorphic properties*`__.
  Jean-Philippe Bernardy, Patrik Jansson, Koen Claessen.
  ESOP 2010.

__ http://publications.lib.chalmers.se/publication/99387-testing-polymorphic-properties

The intuition is that the first argument, of type \\(F\\alpha\\to\\alpha\\),
is used by the polymorphic function to *construct* values of abstract type
\\(\\alpha\\), while the second argument provides ways of "observing" these
constructed values. The initial algebra \\(f_0 : F\\mu\\to\\mu\\)
corresponds to an injective constructor, so that a tester can inspect values of
type \\(\\mu\\) in the output \\(U\\mu\\) to know exactly how they were
constructed by \\(\\phi\\). By parametricity, the polymorphic function
\\(\\phi\\) must construct its output "uniformly" over all types, so looking at
the result on one input allows us to deduce its behavior on many other inputs.

This effectively establishes an isomorphism:

\\[
(\\forall \\alpha. (F\\alpha\\to\\alpha)\\times(G\\alpha\\to X)\\to U\\alpha)
\\quad\\simeq\\quad
(G\\mu\\to X)\\to U\\mu
\\]

Testing a polymorphic function is equivalent to testing a corresponding
monomorphic function, which is more straightforward to do.

Definitions
-----------

Given
\\(\\phi :
\\forall\\alpha. (F\\alpha\\to\\alpha)\\times(G\\alpha\\to\\alpha)\\to U\\alpha.\\)
and the initial algebra \\(f_0 : F\\mu\\to\\mu\\),
the *monomorphization* of \\(\\phi\\) is defined by:

\\[
\\DeclareMathOperator\\mono{mono}
\\DeclareMathOperator\\poly{poly}
\\DeclareMathOperator\\id{id}
\\begin{aligned}
& \\mono{\\phi} : (G\\mu\\to\\mu)\\to U\\mu \\\\
& \\mono{\\phi}~g_0 = \\phi~(f_0, g_0)
\\end{aligned}\\]

To define the inverse, we recall the definition of the initial algebra
\\(f_0\\): every algebra \\(f : F\\alpha\\to\\alpha\\) induces a
*catamorphism* \\(\\eta\_{f} : \\mu\\to\\alpha\\),
which is the unique function making the following square commute:

\\[\\require{AMScd}
\\begin{CD}
F\\mu           @>{f_0}>>     \\mu \\\\
@V{F\\eta\_{f}}VV                @VV{\\eta\_{f}}V \\\\
F\\alpha          @>{f}>>     \\alpha
\\end{CD}\\]

Given a monomorphic \\(\\psi : (G\\mu\\to\\mu)\\to U\\mu\\),
its *polymorphization* is:

\\[
\\begin{aligned}
& \\poly{\\psi} : \\forall\\alpha. (F\\alpha\\to\\alpha)\\times(G\\alpha\\to\\alpha)\\to U\\alpha \\\\
& \\poly{\\psi}~(f, g) = U\\eta\_{f}~(\\psi~(g \\circ G\\eta\_{f}))
\\end{aligned}\\]

Monopoly theorem
----------------

**Polymorphization is the inverse of monomorphization.**

1. \\(\\poly\\) is a right-inverse for \\(\\mono\\):

   \\[\\mono\\circ\\poly = \\id\\]

   Unfolding the definitions, we need to check the following equation:

   \\[U\\eta\_{f_0}~(\\psi~(g_0\\circ G\\eta\_{f_0})) = \\psi~g_0\\]

   Indeed, the catamorphism \\(\\eta\_{f_0}\\) of the initial algebra
   must be the identity function. We may thus simplify the left hand side by
   functoriality of \\(U\\) and \\(G\\).

2. \\(\\poly\\) is a left-inverse for \\(\\mono\\):

   \\[\\poly \\circ \\mono = \\id\\]

   Equivalently,

   \\[U\\eta\_{f}~(\\phi~(f_0,g\\circ G\\eta\_{f})) = \\phi~(f, g)\\]

   That is a consequence of the free theorem of \\(\\phi\\),
   with the catamorphism \\(\\eta\_{f}\\) as a functional
   relation between \\(\\mu\\) and \\(\\alpha\\) (details omitted).

The form of \\(T\\alpha\\) as
\\((F\\alpha\\to\\alpha)\\times(G\\alpha\\to X)\\)
above may seem restrictive, but the paper also shows how a large class of types
can actually be transformed to make that result applicable.
Basically, the type \\(T\\alpha\\) may be a product of types of
the form \\(C_i\\alpha\\to D_i\\alpha\\) where \\(C_i, D_i\\)
are functors, and \\(D_i\\) is made of sums, products,
and fixpoints.

To motivate the dual approach, let's look at an example where that is not the
case.

Example
=======

Let \\(\\mathbb{B}\\) be the type of booleans, with constructors
\\(0,1 : \\mathbb{B}\\) and destructor
\\(\\mathrm{if}:\\forall\\beta.\\mathbb{B}\\to\\beta\\to\\beta\\to\\beta\\).
Our example will be:

\\[\\forall \\alpha. ((\\alpha\\to\\mathbb{B}) \\times
((\\alpha\\to\\mathbb{B})\\to\\mathbb{B})) \\to \\mathbb{B}\\]

Given arguments \\(f : \\alpha\\to\\mathbb{B}\\) and
\\(g : (\\alpha\\to\\mathbb{B})\\to\\mathbb{B}\\),
the result will be a boolean combination of applications of \\(f\\) and
\\(g\\). Since there is no \\(\\alpha\\) in the immediate context to apply
\\(f\\) to, we can only apply \\(g\\) at first. Here is a typical inhabitant
of the above type:

\\[\\phi = \\lambda(f, g).
g~(\\lambda a. \\mathrm{if}~(f~a)~0~1)\\]

The only way a polymorphic function \\(\\phi\\) of that type
can inspect a value of type \\(\\alpha\\) is to use the first
parameter. Hence, from the point of view of \\(\\phi\\), a value of type
\\(\\alpha\\) contains only as much information as a boolean.
To test \\(\\phi\\), it is actually sufficient to instantiate \\(\\alpha\\)
with \\(\\mathbb{B}\\) and set the first argument to the identity function
\\(f_0 = \\lambda x.x\\).

In fact, the above type is isomorphic to the following finite type:

\\[((\\mathbb{B}\\to\\mathbb{B})\\to\\mathbb{B})\\to\\mathbb{B}\\]

Terminal view
-------------

With the initial view, we examined how a polymorphic function uses
*constructors* of abstract type \\(\\alpha\\), represented by algebras
\\(F\\alpha\\to\\alpha\\).
With an initial algebra \\(f_0 : F\\mu\\to\\mu\\), the least fixed point
\\(\\mu\\) was as large as the sum of ways of constructing its inhabitants using
\\(f_0\\).

Here, we shall look at *destructors*: coalgebras
\\(\\alpha \\to F\\alpha\\). (Above, \\(F\\alpha=\\mathbb{B}\\).)
With a terminal coalgebra \\(f_1 : \\nu\\to F\\nu\\), the "greatest fixed point"
\\(\\nu\\) will be as large as the "product" of observations we can make about
an inhabitant using \\(f_1\\).

We now consider the following type, where \\(F\\) is a functor
and we'll see later what \\(U\\) can be:

\\[\\forall \\alpha. (\\alpha\\to F\\alpha)\\to U\\alpha\\]

What happens if we take the terminal coalgebra, \\(f_1:\\nu\\to F\\nu\\)?

By definition, every coalgebra \\(f : \\alpha\\to F\\alpha\\) induces an
*anamorphism* \\(\\epsilon\_{f} : \\alpha\\to\\nu\\), which is the unique
function with the commutative square:

\\[\\require{AMScd}
\\begin{CD}
\\alpha              @>{f}>>     F\\alpha \\\\
@V{\\epsilon\_{f}}VV                  @VV{F\\epsilon\_{f}}V \\\\
\\nu               @>{f_1}>>     F\\nu
\\end{CD}\\]

Under the extra assumption that \\(U\\) is a *contravariant functor*,
we show this isomorphism:

\\[
(\\forall\\alpha. (\\alpha\\to F\\alpha)\\to U\\alpha)
\\quad\\simeq\\quad
U\\nu
\\]

Definitions
-----------

The monomorphization of
\\(\\phi : \\forall\\alpha. (\\alpha\\to F\\alpha)\\to U\\alpha\\)
is defined by:

\\[
\\begin{aligned}
& \\mono\\phi : U\\nu \\\\
& \\mono\\phi = \\phi~f_1
\\end{aligned}
\\]

The polymorphization of \\(\\psi : U\\nu\\) is defined by:

\\[
\\begin{aligned}
& \\poly\\psi : \\forall\\alpha. (\\alpha\\to F\\alpha)\\to U\\alpha \\\\
& \\poly\\psi~f = U\\epsilon\_{f}~\\psi
\\end{aligned}
\\]

Note that the contravariant functor \\(U\\) lifts
\\(\\epsilon\_{f} : \\alpha\\to\\nu\\) to
\\(U\\epsilon\_{f} : U\\nu\\to U\\alpha\\).

Theorem
-------

**Polymorphization is the inverse of monomorphization.**

1. \\(\\poly\\) is a right-inverse for \\(\\mono\\):

   \\[\\mono\\circ\\poly = \\id\\]

   Equivalently,
   \\(U\\epsilon\_{f_1}~\\psi = \\psi\\).

   Indeed, the anamorphism \\(\\epsilon\_{f_1}\\) of the terminal coalgebra
   must be the identity function.

2. \\(\\poly\\) is a left-inverse for \\(\\mono\\):

   \\[\\poly \\circ \\mono = \\id\\]

   Equivalently,
   \\(U\\epsilon\_{f}~(\\phi~f_1) = \\phi~f\\).

   That is a consequence of the free theorem of \\(\\phi\\),
   with the catamorphism \\(\\epsilon\_{f}\\) as a functional
   relation between \\(\\nu\\) and \\(\\alpha\\) (details omitted).

Application
-----------

This technique actually applies to our example;
with \\(\\alpha\\to F\\alpha=\\alpha\\to\\mathbb{B}\\) and
\\(U\\alpha=((\\alpha\\to\\mathbb{B})\\to\\mathbb{B})\\to\\mathbb{B}\\),
we obtain the same monomorphization:

\\[\\begin{aligned}
\\nu &= \\mathbb{B} \\\\
f_1 &= \\lambda x. x
\\end{aligned}\\]

Notice that simple trick of pushing the extra argument type
\\((\\alpha\\to\\mathbb{B})\\to\\mathbb{B}\\) into the result type
\\(U\\alpha\\). This happens to work whenever the argument type is
covariant in \\(\\alpha\\) (this includes types like \\(\\alpha\\),
\\(X\\to\\alpha\\), \\(X\\), where \\(X\\) is non-parametric).

Dually, in the initial view, we separated the algebra \\(F\\alpha\\to\\alpha\\)
from an "observation function" \\(G\\alpha\\to X\\); we can simplify that
assumption by shoving that type (contravariant in \\(\\alpha\\), since \\(G\\)
is covariant) into the result type \\(U\\alpha\\), which remains covariant.

To summarize, we have two dual methods of monomorphizing polymorphic
functions, of type \\(\\forall\\alpha.T\\alpha\\to U\\alpha\\), in the
following situations:

- \\(\\forall\\alpha. (F\\alpha\\to\\alpha)\\to U\\alpha\\),
  where \\(F\\) and \\(U\\) are covariant---in particular, \\(U\\alpha\\) may
  be a function type whose arguments \\(G\\alpha\\to X\\) correspond to
  "observation functions";
- \\(\\forall\\alpha. (\\alpha\\to F\\alpha)\\to U\\alpha\\), where \\(F\\) is
  covariant and \\(U\\) is contravariant---\\(U\\alpha\\) may be a function
  type with "constructors" \\(Y\\to H\\alpha\\) as arguments for example.

Overlapping views
=================

There are cases where both techniques apply. We should get equivalent results
since monomorphizations are isomorphisms. For instance:

\\[\\forall\\alpha. (X\\to \\alpha) \\to (\\alpha\\to Y) \\to Z\\]

The initial view yields \\(\\alpha = X\\), with the first argument
set to the identity function; the second argument, which may vary freely, has
type \\(X\\to Y\\).

The terminal view yields \\(\\alpha = Y\\), with the second argument
set to the identity function; the first argument has type \\(X\\to Y\\).

Here is another example:

\\[\\forall\\alpha.
(\\alpha\\to\\alpha\\times X)\\to\\alpha\\to Y\\]

The coalgebra \\(\\alpha\\to\\alpha\\times X\\) views
\\(\\alpha\\) as an infinite stream of \\(X\\),
i.e., the type \\(X^\\omega\\).
We fix the first argument as the stream destructor
\\(X^\\omega \\to X^\\omega\\times X\\),
and the second argument may be any stream \\(X^\\omega\\).

Before taking the initial view, we rewrite that type a bit,
first by commutativity
\\(A \\to B \\to C \\simeq B \\to A \\to C\\)
and second by distributivity of exponentials over products
\\(A \\to B\\times C \\simeq (A\\to B)\\times(A\\to C)\\).

\\[\\begin{aligned}
& (\\alpha\\to\\alpha\\times X)\\to\\alpha\\to Y \\\\
\\quad\\simeq\\quad& \\alpha\\to(\\alpha\\to\\alpha\\times X)\\to Y \\\\
\\quad\\simeq\\quad& \\alpha\\to(\\alpha\\to\\alpha)\\to(\\alpha\\to X)\\to Y
\\end{aligned}\\]

The algebra \\(\\alpha \\times (\\alpha\\to\\alpha)\\) (isomorphic to
\\((\\unicode{x1D7D9} + \\alpha) \\to \\alpha\\)) views \\(\\alpha\\)
as a natural number. With \\(\\alpha = \\mathbb{N}\\), we fix the first two
arguments to the Peano constructors (zero and successor), and
the last argument varies over \\(\\mathbb{N}\\to X\\), which
is isomorphic to streams \\(X^\\omega\\).

Questions
=========

The initial view can be adapted to other types
\\(\\forall\\alpha.T\\alpha\\to U\\alpha\\)
when there is an embedding of \\(T\\alpha\\) in some
\\((F\\alpha\\to\\alpha)\\times C\\alpha\\) for a covariant \\(F\\) and
contravariant \\(C\\).

Dually, are there interesting types to embed in
\\((\\alpha\\to F\\alpha)\\times D\\alpha\\), for \\(F\\) and
\\(D\\) both covariant?

----

Is there a unified view that generalizes the above?

----

What can we do for a type like
\\(\\forall\\alpha.((\\alpha\\to\\alpha)\\to\\alpha)\\to\\alpha\\),
for which neither the initial nor terminal view are applicable?
