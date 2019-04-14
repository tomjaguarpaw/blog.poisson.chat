---
title: Performance debugging in aeson
description: An example of optimizing Haskell programs
keywords: [haskell]
---

Making aeson run fast
=====================

Ideally, whether we are using Template Haskell or Generics, we would like
automatically derived code to be as fast as code we could have written
and optimized manually.
To understand what it takes to achieve such a result, I've recently
started to work on the performance of `aeson`_, a JSON library in Haskell.
In this blog post, I walk through the process of finding a simple performance
bug.

.. _aeson: https://hackage.haskell.org/package/aeson

Benchmarking
============

To get an idea of where to look, we need some benchmarks.
The aeson repository has `a few benchmarks`__ for encoders and decoders derived
using Template Haskell and Generics. Interestingly, without any handwritten
implementation for reference, this is still sufficient to reveal some issues:
if we get different performance out of the two derived implementations, then
there are optimizations to fit in the slower one.

.. __: https://github.com/bos/aeson/blob/master/benchmarks/AesonCompareAutoInstances.hs

During development, compiler optimizations are disabled to reduce compile
times. For benchmarking, we must remember to enable them again.
Using stack, here is a typical-looking sequence of commands to build and run a
benchmark:

.. code:: bash

  # Step 0: Check that stack.yaml doesn't disable optimizations
  # or override settings with the right options in the next commands

  # Rebuild with optimizations
  $ stack build

  $ cd benchmarks/

  # Install whatever the benchmark needs
  $ stack install criterion

  $ stack ghc -- AesonCompareAutoInstances -O2

  $ ./AesonCompareAutoInstances

Generics is usually not faster than Template Haskell. Indeed, the latter is a
straightforward way of generating arbitrary code, so it seems easier to
write optimized code. Consequently, it is surprising to see numbers which
contradict that intuition: benchmarks show Template Haskell to be slower than
Generics at encoding records directly as byte strings.

Let us illustrate what ``encode`` does. With the default options, it would
convert a record ``Record { x = 0, y = "lambda", z = True }`` to the string:

.. code::

  {"x":0,"y":"lambda","z":true}

For a big record of 25 fields in the benchmark above, this takes 3.6 μs for TH,
against 3.0 μs for Generics. For a smaller record of 5 fields, the relative
difference is even greater: 940 ns vs. 590 ns. (``SmallRecord.hs``, source_)

.. _source: https://gist.github.com/Lysxia/52576aa9a62defaf058247dd3e7eb147

The measured run times are summarized in the following table, in μs.

+-----------+------+-----+
| n. fields |    5 |  25 |
+===========+======+=====+
| orig. TH  | 0.94 | 3.6 |
+-----------+------+-----+
| generics  | 0.59 | 3.0 |
+-----------+------+-----+

Analyzing code
==============

We need to take a closer look at the functions ``thBigRecordEncode`` and
``gBigRecordEncode``. Instead of staring aimlessly at the library code behind
them[#thgenericsource]_,
we can ask GHC to output the Core terms it optimized.

.. [#thgenericsource]

  If anyone wants to try, their versions before the fix can be found at
  ``Data/Aeson/TH.hs`` (source__), ``Data/Aeson/Types/ToJSON.hs`` (source__).

.. __: https://github.com/bos/aeson/blob/f3495ecb2dc8b95e0e63837a33469d6b287dc25c/Data/Aeson/TH.hs
.. __: https://github.com/bos/aeson/blob/f3495ecb2dc8b95e0e63837a33469d6b287dc25c/Data/Aeson/Types/ToJSON.hs

GHC Core
--------

Core is the intermediate representation on which GHC performs optimizations.
It is a minimalistic functional language; the main
type representing it has only 10 constructors!

Straight from the `source code of GHC`__:

.. code:: haskell

  data Expr b
    = Var   Id
    | Lit   Literal
    | App   (Expr b) (Arg b)
    | Lam   b (Expr b)
    | Let   (Bind b) (Expr b)
    | Case  (Expr b) b Type [Alt b]
    | Cast  (Expr b) Coercion
    | Tick  (Tickish Id) (Expr b)
    | Type  Type
    | Coercion Coercion

.. __: https://github.com/ghc/ghc/blob/f337a208b1e1a53cbdfee8b49887858cc3a500f6/compiler/coreSyn/CoreSyn.hs#L273

For the purpose of understanding performance issues, we can ignore the last
four because they will ultimately be erased from run time. The remaining six
constructors are a familiar bunch common to most functional programming
languages: variables, literals, function applications, anonymous functions,
local definitions, and pattern matching.
So if you can already read Haskell, Core sounds pretty easy to pick up.
We'll see some output soon enough.

Reducing the test case
----------------------

To make the final output easier to navigate, I simplified the original
``AesonCompareAutoInstances.hs`` from the aeson repository to
``SmallRecord.hs`` (source_) with a single small record type[#sorry]_.

.. [#sorry]

  Confusingly still named ``BigRecord``!

.. code:: haskell

  data BigRecord = BigRecord
    { field01 :: !Int,
      field02 :: !Int,
      field03 :: !Int,
      field04 :: !Int,
      field05 :: !Int } deriving (Show, Eq, Generic)

Here is an example of encoding such a record as JSON:

.. code::

  > let bigRecord = BigRecord 1 2 3 4 5

  > ByteString.putStrLn (gBigRecordEncode bigRecord)

  {"field01":1,"field02":2,"field03":3,"field04":4,"field05":5}

Dump options
------------

The incantation to obtain optimized Core together with
the Template Haskell output is the following:

.. code::

  $ stack ghc -- SmallRecord -O2 -ddump-splices -ddump-simpl   \
                                 -dsuppress-all -ddump-to-file

Let us explain briefly the new options.

Template Haskell
++++++++++++++++

``-ddump-splices`` outputs the code fragments generated with Template Haskell.
Here, we are trying to figure out why the ``mkToEncoding`` splice at `line 61`_
is slow. It corresponds to the following output in
``SmallRecord.dump-splices``:

.. _line 61: https://gist.github.com/Lysxia/52576aa9a62defaf058247dd3e7eb147#file-smallrecord-hs-L61

.. code::

  (...)

    mkToEncoding opts ''BigRecord
  ======>
    \ value_aeD3
     -> case value_aeD3 of {
      BigRecord arg1_aeD4 arg2_aeD5 arg3_aeD6 arg4_aeD7 arg5_aeD8
       -> wrapObject
        (commaSep
         [((string "field01") >< (colon >< (toEncoding arg1_aeD4))),
          ((string "field02") >< (colon >< (toEncoding arg2_aeD5))),
          ((string "field03") >< (colon >< (toEncoding arg3_aeD6))),
          ((string "field04") >< (colon >< (toEncoding arg4_aeD7))),
          ((string "field05") >< (colon >< (toEncoding arg5_aeD8)))]) }

An object is a comma-separated list of fields (``commaSep``), surrounded by
braces (``wrapObject``). Each field is represented by its name and contents,
separated by a ``colon``. Doesn't it look fine?

Core dump
+++++++++

``-ddump-simpl`` outputs the optimized ("simplified") Core;
``-dsuppress-all`` hides a lot of type information that's irrelevant to us;
``-ddump-to-file``, as its name indicates, makes GHC write the output
to files (``SmallRecord.dump-splices``, ``SmallRecord.dump-simpl``)
instead of flooding standard output by default.

I pasted the core for ``thBigRecordEncode`` here_ and ``gBigRecordEncode``
`here below it`_, although we won't need to look past the first 12 lines.

.. _here: https://gist.github.com/Lysxia/73f6c083c32e1aacfed10782bd4cf265#file-thbigrecordencode
.. _here below it: https://gist.github.com/Lysxia/73f6c083c32e1aacfed10782bd4cf265#file-gbigrecordencode

Even with ``-dsuppress-all``, the Core output by GHC is quite an eyeful.
Both ``gBigRecordEncode`` and ``thBigRecordEncode`` take about 500 lines each!
We can see that all the low-level details of writing a ``ByteString`` got
inlined. Indeed, inlining is key to enable other compiler optimizations, and
one of the main methods to improve performance is ensuring inlining happens.

Spot the not inlined
--------------------

Conversely, values that don't get inlined are a common source of
inefficiency. We can just look for those, without paying much attention
to what the program is actually doing. User-defined values that aren't inlined
easily stand out if the source code has descriptive names, since Core reuses
them (a bit mangled sometimes) and they contrast with the short names that are
made up for fresh local variables.

Look, there's one non-inlined function just at the top of ``thBigRecordEncode``:

.. code:: haskell

  thBigRecordEncode
  thBigRecordEncode =
    \ x_agtJ ->
      toLazyByteString     -- <- not inlined
        (...
         )

Oh, sorry, that's a false positive. ``toLazyByteString`` is `marked`__
``NOINLINE`` in the bytestring library. Let's trust that it's there for a good
reason.
Furthermore, the Generic variant ``gBigRecordEncode`` begins identically,
so it seems unlikely to be the cause of the performance gap we observed
earlier.

.. __: https://hackage.haskell.org/package/bytestring-0.10.8.2/docs/src/Data.ByteString.Builder.html#toLazyByteString

Dig just a bit deeper, and here's another one:

.. code:: haskell

  thBigRecordEncode
  thBigRecordEncode =
    \ x_agtJ ->
      toLazyByteString
        (case x_agtJ
         of _ { BigRecord dt_dgnD dt1_dgnE dt2_dgnF dt3_dgnG dt4_dgnH ->
         let {
           e_aktT
           e_aktT =
             commaSep_$scommaSep            -- <- not inlined
               (...
                ) ...
              } ...
         })

``commaSep_$scommaSep`` is basically ``commaSep``, which appears in the Template
Haskell snippet from earlier. It inserts a comma between consecutive elements
of a list. Its definition is (source__):

.. code:: haskell

  commaSep :: [E.Encoding] -> E.Encoding
  commaSep [] = E.empty
  commaSep [x] = x
  commaSep (x : xs) = x E.>< E.comma E.>< commaSep xs

.. __: https://github.com/bos/aeson/blob/f3495ecb2dc8b95e0e63837a33469d6b287dc25c/Data/Aeson/TH.hs#L620

It is recursive, hence the compiler makes it non-inlineable. In this case, its
argument is essentially the list of record fields, so we know it would be safe
to unroll the definition of ``commaSep`` here.

Looking at Core here may seem somewhat overkill, as ``commaSep`` is one of
only six functions that appear in the Template Haskell splice, so it wouldn't
have taken too long to figure out the problem either way. But reading Core is a
reliable method: it could also reveal non-inlining of functions that are not
immediately visible in the source code.

Bug fixed
---------

Let us have the Template Haskell code unroll the insertion of commas; the
result now looks like this:

.. code::

  (...)

    mkToEncoding opts ''BigRecord
  ======>
    \ value_aeXm
     -> case value_aeXm of {
      BigRecord arg1_aeXn arg2_aeXo arg3_aeXp arg4_aeXq arg5_aeXr
       -> fromPairs
        ((pair "field01" (toEncoding arg1_aeXn))
         <>
          ((pair "field02" (toEncoding arg2_aeXo))
           <>
            ((pair "field03" (toEncoding arg3_aeXp))
             <>
              ((pair "field04" (toEncoding arg4_aeXq))
               <> (pair "field05" (toEncoding arg5_aeXr)))))) }

The monoid operation[#typeclass]_ ``(<>)`` takes care of inserting a comma
between its non-empty operands. With the recursive function out of the way, we
get the speed up we were looking for (see third line):

.. [#typeclass]

  Using type classes allows us to reuse almost the same
  implementation for ``mkToJSON``.


+-----------+------+-----+
| n. fields |    5 |  25 |
+===========+======+=====+
| orig. TH  | 0.94 | 3.6 |
+-----------+------+-----+
| generics  | 0.59 | 3.0 |
+-----------+------+-----+
| fixed TH  | 0.61 | 2.5 |
+-----------+------+-----+

For small records, TH now performs as well as Generics. But for large records,
TH performs better. This is because GHC fails to optimize Generics for large
types. That will be another story to tell.

Time for a `pull request`_.

.. _pull request: https://github.com/bos/aeson/pull/596
