---
title: Parsing and unparsing with lenses
---

\\[
\\newcommand{\\compose}{\\cdot}
\\newcommand{\\Txt}{\\mathrm{Text}}
\\newcommand{\\Program}{\\mathrm{Program}}
\\DeclareMathOperator*{\\id}{id}
\\DeclareMathOperator*{\\parse}{parse}
\\DeclareMathOperator*{\\unparse}{unparse}
\\DeclareMathOperator*{\\get}{get}
\\DeclareMathOperator*{\\put}{put}
\\newcommand{\\Doc}{\\mathrm{Documentary}}
\\]

In this post I set the stage for my current work here at the University of Kent
on applying bidirectional programming to refactoring.

Whitespace-(un)aware refactoring
================================

  Code refactoring is the process of restructuring existing computer code (...)
  without changing its external behavior.

  -- Wikipedia on `Code refactoring`_

.. _Code refactoring: https://en.wikipedia.org/wiki/Code_refactoring

An important goal of refactoring is maintainability, i.e., to make code easier
to modify, in order to fix bugs, improve existing features and add new
ones.
Before one modifies code, one should first understand it, thus source code is
not only meant to be processed by compilers, but also to be read by humans.
Programmers ought to carefully lay out their code: they use indentation,
alignment, they can separate logical groups with empty lines and break long
lines.
They also add comments: to document an API, to describe complex algorithms or
the architecture of a program, to give meaning to variables in addition to
their name, to explain code when it looks suspicious.
Let us call **documentary structure** these elements that benefit the human
reader much more than the machine which processes the code, as suggested
by the title of *The documentary structure of source code* [#VanDeVanter]_.

.. [#VanDeVanter]
  *The documentary structure of source code*, Michael L. Van De Vanter, 2002.

Of course, certain refactoring tasks can be automated.
For example, there are code formatters to layout code, linters to detect
antipatterns and trivial simplifications.
Variables can be renamed safely with tools aware of their scopes, common
patterns can be factored into function calls or macro invocations.

Some of these tools can be schematized as follows: read and parse a program,
transform it, write it out.
These transformations often operate on the abstract syntax of a program, so
that they are ignorant of documentary structure at a formal level.
Since it plays a crucial role in readability, and ultimately, maintainability,
it is undesirable to indiscriminately discard it.
In practice, in order to address this concern, it would appear that tools
either implement ad-hoc solutions, or defer the issue to human users by showing
the update to be examined and fixed by hand. [#CitationNeeded]_

.. [#CitationNeeded]
  Citation needed.

  I need better examples up there, because auto-indenters and renamers actually
  have little to no trouble with comments and the *documentary structure* that
  is being discussed here.
  I am also ignorant of how the more sophisticated tools currently handle such
  structure in practice.

As argued by *The documentary structure of source code*, this documentary
structure consists, in fact, of a structure of its own that is "orthogonal"
to the **linguistic structure** traditionally understood by programming tools and
formalized by the abstract syntax of a program.

Documentary structure is visual, and is in a large part formed with natural
language via comments, which programmers use to clarify ideas that they cannot
express in actual code.
The article describes further some components of documentary structure
indicating that a systematic treatment of it:

1. will only ever be approximate at best;

2. requires a framework different from the current "compiler-oriented"
   approach of representing programs as decorated trees.

Of course, we would like such a framework to play well with current refactoring
methods, ideally leaving them unaware of the documentary structure, so that
the *concern* of it remains *separate*.

Parsing and pretty-printing
===========================

**Parsers** and **pretty-printers** (**unparsers**), being the interface of
compilers and related programs with source code, are the main components
dealing with documentary structure.

Parsers of programming languages are commonly obtained from a grammar-like
specification by a *parser generator*. Yacc and Bison generate parsers written
in C; Alex in Haskell; OCamlyacc and Menhir in OCaml.
Another approach that hax been taking off in functional programming
languages is that of *parser combinators*.
Parsers traditionally discard most documentary structure, keeping only source
code locations for error reporting.

Pretty-printers attract much less attention.
Two likely reasons are that decent results can be obtained with straightforward
tree traversals, and that generated code is rarely meant to be read or edited
by humans.
Still, pretty-printing can be useful to debug such code, to create code
templates, or as the output of complex refactoring tools (our main motivation).
Thus, there exist libraries streamlining the design of pretty-printers, notably
Wadler's *pretty-printing combinators* (originally written in Haskell;
since then it has been imported by other languages):
"documents" are concatenated using combinators that automatically break long
lines and insert proper indentation in particular.

We may require that a parser and a pretty-printer (not necessarily derived from
it):
\\[
\\begin{split}
\\parse &: \\Txt \\to \\Program \\\\
\\unparse &: \\Program \\to \\Txt
\\end{split}
\\]
satisfy that \\(\\unparse\\) is a right inverse of \\(\\parse\\):
\\[
\\parse \\compose \\unparse = \\id : \\Program \\to \\Program.
\\]

That is to say that pretty-printing produces valid source code,
which can be parsed back into the original program.

What would be nice to find is a way to also extract the documentary structure
separately from the actual program, so that we have an improved parser named
\\(\\get : \\Txt \\to \\Program \\times \\Doc\\), for some appropriately chosen
representation \\(\\Doc\\).
Then, possibly assuming the program does not change too much, we would like to
somehow merge back the documentary structure, with an improved unparser named
\\(\\put : \\Program \\times \\Doc \\to \\Txt\\).

Then two laws, if satisfied, make this pair of functions a **lens**.

The GetPut law implies that parsing captures all information about the source
code, so that it can be reconstructed by unparsing:
\\[
\\begin{equation}
\\begin{gathered}
  \\put \\compose \\get = \\id : \\Txt \\to \\Txt, \\\\
  \\textit{equivalently,} \\\\
  \\forall s : \\Txt,\\; \\put (\\get s) = s.
\\end{gathered}
\\end{equation}
\\]

The PutGet law is analogous to the right inverse property above.
It implies that updates of the program are reflected in the resulting source
code:
\\[
\\begin{gathered}
  \\begin{split}
  &\\forall & (p, d) &: \\Program \\times \\Doc, \\\\
  &\\exists & d' &: \\Doc,
  \\end{split} \\\\
  \\get (\\put (p, d)) = (p, d')
\\end{gathered}
\\]

These laws alone are not sufficient to characterize a "good" lens.
Indeed, imagine that we are given an simple parser and pretty-printer which
is a right inverse:

\\[
\\begin{split}
  \\parse &: \\Txt \\to \\Program \\\\
  \\unparse &: \\Program \\to \\Txt
\\end{split}
\\]

assuming

\\[
\\parse \\compose \\unparse = \\id : \\Program \\to \\Program.
\\]

We can define a *stupid* lens, with \\(\\Doc = \\Txt\\).
Keep the whole source file to represent the documentary structure:
\\[
\\get :
\\begin{split}
\\Txt &\\to \\Program \\times \\Doc \\\\
s &\\mapsto (\\parse s, s).
\\end{split}
\\]

Print it back if the program didn't change (ensuring PutGet),
otherwise use the provided pretty-printer (ensuring GetPut):
\\[
\\put :
\\begin{split}
  \\Program \\times \\Doc &\\to \\Txt \\\\
  (p, s) &\\mapsto
  \\begin{cases}
    s & \\text{if } \\parse s = p, \\\\
    \\unparse p & \\text{otherwise.}
  \\end{cases}
\\end{split}
\\]

That is indeed a lens, which does not preserve the documentary structure
of the source code in any useful way.

Formalizing documentary structure
---------------------------------

We need to express the idea that the documentary structure should not change
too wildly with ``put``. For that we need a method of comparing documentary
structures, which requires further study to formalize.

The usage of documentary structure shall be investigated to define it better
and to design data structures for it.
The investigation can be "theoretical", for example listing, interpreting and
classifying possible code layouts, comment locations, and other relevant
elements; or "practical", considering only those that appear in existing code
bases.

Reviewing existing refactoring tools is also necessary to assess the usefulness
of our ideas.
"Bidirectionality" of parsers and printers is for example not relevant to
certain code formatters which operate on streams of tokens, where comments can
cheaply be represented as just another token and changes in indentation is
dictated by keywords or predetermined sequences of tokens; nor to linters that
only need to flag antipatterns, leaving to the programmer the task of acting on
them, or not.
Yet, we believe the problem of documentary structure still arises in more
sophisticated transformations.
A closer look at how it is currently handled would allow us to anchor our
solutions to concrete issues.

Bidirectionalization
====================

Bringing in concepts (lenses) from the bidirectional programming literature
suggests related ideas that may be tied in the development of the
aforementioned "framework" of documentary structure.

Naturally, parsers and pretty-printers are related artifacts, and there has
been some work done to derive one from the other, modulo some annotations.
The one closest to me is **FliPpr**\ [#flippr]_, a language of pretty-printers
(based on Wadler's combinators) that can be inverted into parsers.  This brings
up the question of using FliPpr to create lenses as presented above.

.. [#flippr]
  *FliPpr: A Prettier Invertible Printing System*,
  Kazutaka Matsuda and Meng Wang, ESOP 2013.

Indeed, the duplication of code from a parser and a pretty-printer written
separately becomes even more flagrant when no information can be discarded by
the parser and when the pretty-printer should reproduce it faithfully.

For example, here is a simple FliPpr program to parse/print a list of words.
[#flipprsyntax]_

.. [#flipprsyntax]
  I made up a special syntax for regexes in FliPpr. The current actual encoding
  of regexes in strings requires escaping backslashes, hindering readability:
  ``"\\S+"``.

::

  data Words = Nil | Word String Words

  print_words Nil = nil
  print_words (Word w ws) =
    text (w @@ /\S+/) <> space <> print_words ws

  nil = text "" <+ space
  space = text " " <> nil

That FliPpr pretty-printer can be interpreted as a non-deterministic function
\\(\\mathrm{Words} \\to \\Txt\\), where the possible outcomes are all the text
strings that produce the same \\(\\mathrm{Words}\\) value when parsed.  A "main
branch" (on the left of the ``(<+)`` operator) indicates the "pretty" way of
printing the program.
For instance, the ``space`` printer: when interpreted *prettily*, it prints a
single space; when interpreted *non-deterministically*, it may print any number
of consecutive spaces.

A parser can be obtained, roughly, by inverting that non-deterministic
interpretation.
The existence of elements, here variable spacing, insignificant to the final
value is the cause of that non-determinism.

The following variant also stores the whitespace between words, modifying the
result ``Words`` type.

::

  data Words = Nil String | Word String String Words

  print_words (Nil s) = text (s @@ /\s*/)
  print_words (Word w s ws) =
    text (w @@ /\S+/) <> text (s @@ /\s+/) <> print_words ws

In a way, we rewrote the original pretty-printer to be deterministic.
The programmer can also choose to partially and selectively remove
non-determinism.
In other words, in the parser direction, they can still discard certain
entirely irrelevant or unwanted variations in source code, making the handling
of the remaining elements simpler.

The code of a "refactoring transformation" that operates on the parsed value
may ignore the additional fields, using default values when making new nodes.
This may be fine when these fields carry little to no information, but is much
more difficult to handle correctly when, for instance, comments are closely
related to each other or to pieces of code in ways that are not apparent
syntactically.

Deriving lenses
---------------

We can also try to automate a transformation of FliPpr programs hinted at
above by the ``print_words`` example,
such that any information discovered by parsing is automatically attached to
the closest node of the output program (usually an abstract syntax tree).

The surface language needs no changes; the FliPpr system will alter the type of
the result (AST) to make room for the "parsing information", but I believe that
change can be made invisible to the programmer to a good extent.

Like most automated systems, a downside of this method is its lack of
flexibility, as arbitrary choices need to be made systematically about the
representation of the "parsing data" containing the "documentary structure".

What makes this idea interesting is that it builds upon an existing system, and
thus requires minimal work on the part of programmers, in addition to what they
would have already spent writing a parser/printer, to get some kind of result
at least.
