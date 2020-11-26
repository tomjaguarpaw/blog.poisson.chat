---
title: "hs-to-coq and <code>Data.Sequence</code>"
keywords: ["haskell", "coq"]
---

In the past few weeks I've made some improvements to
[*hs-to-coq*](https://github.com/plclub/hs-to-coq/).
In particular, I wanted to verify the `Data.Sequence` module from the
*containers* library. I've managed to translate most of the module to Coq
so I can start proving stuff.

In this post, I will present some of the changes made in *hs-to-coq* to be able
to translate `Data.Sequence`.

*hs-to-coq* had already been used to verify `Data.Set` and `Data.IntSet`,
and their map analogues, which are the most commonly used modules of the
*containers* library.[^set-verify]
The main feature distinguishing `Data.Sequence` from those is polymorphic
recursion. There were a couple of smaller issues to solve beyond that, and some
usability improvements made in the process.

[^set-verify]: [Ready, Set, Verify!](https://arxiv.org/abs/1803.06960), IFCP 2018.

= Polymorphic recursion

As its name implies, `Data.Sequence` offers a data structure to represent
sequences. The type `Seq a` has a meaning similar to the type of lists `[a]`,
but `Seq a` supports faster operations such as indexing and concatenation
(logarithmic time instead of linear time). The implementation is actually in
`Data.Sequence.Internal`, while `Data.Sequence` reexports from it.

The type `Seq` is a thin wrapper around [the type `FingerTree`][fingertree]
which is where the fun happens.
`FingerTree` is what one might call an *irregular recursive type*.
In the type declaration of `FingerTree`,
the recursive occurrence of the `FingerTree` type constructor is applied
to an argument which is not the variable which appears in the left-hand side
of the definition. The right-hand side of the type declaration mentions
`FingerTree (Node a)`, rather than `FingerTree a` itself:

[fingertree]: https://github.com/haskell/containers/blob/648fdb95cb4cf406ed7364533de6314069e3ffa5/containers/src/Data/Sequence/Internal.hs#L996

```haskell
-- An irregular type. (Definitions of Digit and Node omitted.)
data FingerTree a
  = EmptyT
  | Single a
  | Deep Int (Digit a) (FingerTree (Node a)) (Digit a)

newtype Elem a = Elem a
newtype Seq a = Seq (FingerTree (Elem a))
```

*Regular recursive types*[^regular] are much more common. For example, the type of lists,
`List a` below, is indeed defined in terms of the same `List a` as it appears on the
left-hand side:

```haskell
-- A regular type
data List a = Nil | Cons a (List a)
```

[^regular]: I don't know whether *irregular*/*regular* is conventional
terminology, but my intuition to justify those names is that they generalize
regular expressions. A regular recursive type defines a set of trees which can
be recognized by a finite state machine (a [*tree automaton*][ta];
[Tree Automata, Techniques and Applications](https://gforge.inria.fr/frs/download.php/10994/tata.pdf)
is a comprehensive book on the topic).

[ta]: https://en.wikipedia.org/wiki/Tree_automaton

*hs-to-coq* has no trouble translating irregular recursive types such as
`FingerTree`; do the naive thing and it just works.
Problems start once we look at functions involving them.
For example, consider a naive recursive size function, `sizeFT`:

```haskell
sizeFT :: FingerTree a -> Int
sizeFT EmptyT = 0
sizeFT (Single _) = 1
sizeFT (Deep _ l m r) = sizeDigit l + sizeFT m + sizeDigit r
-- This is wrong.
```

We want to count the number of `a` in a given `FingerTree a`, but the function
above is wrong. In the recursive call, `m` has type `FingerTree (Node a)`, so
we are counting the number of `Node a` in the subtree `m`, when we should
actually count the number of `a` in every `Node a`, and sum them up.
The function above actually counts the sum of all "digits" in a `FingerTree`,
which isn't a meaningful quantity when trees are viewed as sequences.

While it may seem roundabout, probably the most straightforward way to fix this
function is to first define `foldMap`:[^foldmap]

[^foldmap]: [Link to source][foldmapsource] which looks a bit different for
[performance reasons][foldmapoptim].

[foldmapsource]: https://github.com/haskell/containers/blob/648fdb95cb4cf406ed7364533de6314069e3ffa5/containers/src/Data/Sequence/Internal.hs#L1027
[foldmapoptim]: https://github.com/haskell/containers/pull/510

```haskell
foldMapFT :: Monoid m => (a -> m) -> FingerTree a -> m
foldMapFT _ EmptyT = mempty
foldMapFT f (Single x) = f x
foldMapFT f (Deep _ l m r) = foldMap f l <> foldMapFT (foldMap f) m <> foldMap f r

sizeFT :: FingerTree a -> Int
sizeFT = getSum . foldMapFT (\_ -> Sum 1)  -- Data.Monoid.Sum
```

What makes `foldMapFT` unusual (and also `sizeFT` even though its behavior is
unexpected) is that its recursive occurrence has a different type than its
signature. On the left-hand side, `foldMapFT` is applied to `f :: a -> m`;
in its body on the right-hand side, it is applied to `foldMap f :: Node a -> m`.
This is what it means for `foldMapFT` to be *polymorphic recursive*: its own
definition relies on the polymorphism of `foldMapFT` in order to specialize it
to a different type than its type parameter `a`.

In Haskell, type parameters are often implicit; a lot of details are inferred,
so we don't think about them.
In Coq, type parameters are plain function parameters. Whenever we write
a lambda, if it is supposed to be polymorphic, it will take one or more extra
arguments. And now, because of polymorphic recursion, it matters where type
parameters are introduced relative to the fixpoint operator.

```coq
(* A polymorphic recursive foldMapFT *)
fix foldMapFT (a : Type) (m : Type) (_ : Monoid m) (f : a -> m) (t : FingerTree a) : m :=
  ...
  (* Here, foldMapFT : forall a m `(Monoid m), (a -> m) -> FingerTree a -> m *)

(* A non-polymorphic recursive foldMapFT, won't typecheck *)
fun (a : Type) (m : Type) (_ : Monoid m) =>
  fix foldMapFT (f : a -> m) (t : FingerTree a) : m :=
    ...
    (* Here, foldMapFT : (a -> m) -> FingerTree a -> m *)
```

In the body of the first function, `foldMapFT` is polymorphic.
In the body of the second function, `foldMapFT` is not polymorphic.

As you might have guessed, *hs-to-coq* picked the wrong version.
I created an edit to make the other choice:

```
polyrec foldMapFT
# Make foldMapFT polymorphic recursive
```

The funny thing is that *hs-to-coq* internally goes out of its way to factor
out the type parameters of recursive definitions, thus preventing polymorphic
recursion.
This new edit simply skips that step. One could consider just removing that
code path, but I didn't want that change to affect existing code. My gut
feeling is that it might still be useful. It's unlikely that there is one
single rule that will work for translating all definitions to Coq, so "hey it
works" is good enough for now, and things will improve as more counterexamples
show up.

= Decreasing arguments

In Coq, functions are total. To define a recursive function, one must provide
a *termination annotation* justifying that the function terminates.
There are a couple of variants, but the general idea is that some quantity must
"decrease" at every recursive call (and it cannot decrease indefinitely). The
most basic annotation (`struct`) names one of the arguments as "the decreasing
argument".

*hs-to-coq* already allowed more advanced annotations to be specified as edits,
but not this most basic variant---until I implemented it. It can be inferred in
simple situations, but at some point it is still necessary to make it explicit.

When we write a recursive function, we refer to its decreasing argument by its
name, but what really matters is its position in the list of arguments.
For example, here is a recursive function `f` with two arguments `x` and `y`:

```coq
fix f x y {struct y} := ...
```

The annotation `{struct y}` indicates that `y`, the second argument of `f`, is
the "decreasing argument". The function is well-defined only if all occurrences
of `f` in its body are applied to a second argument which is "smaller" than `y`
in a certain sense.
Otherwise the compiler throws an error.

That the argument is *named* is a problem when it comes to *hs-to-coq*: in
Haskell, some arguments don't have names because we immediately pattern-match on
them. When translated to Coq, all arguments are given generated names, and they
are renamed/decomposed in the body of every function.

```haskell
-- A recursive function whose second argument is decreasing,
-- [] or (x : xs) depending on the branch, but there is no variable to refer to it.
map :: (a -> b) -> [a] -> [b]
map f [] = []
map f (x : xs) = f x : map f xs
```

*hs-to-coq* now allows specifying the decreasing argument by its position in the
Haskell definition, i.e., ignoring type parameters.
To implement that feature, we have to be a little careful since type parameters
in Coq are parameters like any other, so they shift the positions of arguments.
That turned out to be a negligible concern because, in the code of *hs-to-coq*,
type parameters are kept separate from "value" parameters until a very late
phase.

```
termination f {struct 2}
# The second argument of f is decreasing
```

Another potential solution is to fix the name generation to be more predictable.
The arguments of top-level functions are numbered sequentially `arg_1__`,
`arg_2__`, etc., which may be fine, but local functions just keep counting from
wherever that left off (going up to `arg_38__` in one case). Maybe they should
also start counting from 1.

More complex termination annotations than `struct` involve arbitrary terms
mentioning those variables. For those, there is currently no workaround, one
must use those fragile names to refer to a function's arguments.

I initially expected that some functions in `Data.Sequence` would have to be
shown terminating based on the size of a tree as a decreasing measure, which
involves more sophisticated techniques than justifications based on depth.
In fact, only one function needs such sophistication ([`thin`][thin], an
internal function used by `liftA2`).
As mentioned earlier, the "size" of a `FingerTree` is actually a little tricky
to formalize, and that makes it even harder to use as part of such
a termination annotation.
Surprisingly, the naive and "wrong" version of `sizeFT` shown earlier also
works as a simpler decreasing measure for this function.

[thin]: https://github.com/haskell/containers/blob/648fdb95cb4cf406ed7364533de6314069e3ffa5/containers/src/Data/Sequence/Internal.hs#L845

= Missing pieces, unsupported features

With the above two changes, *hs-to-coq* is now able to process quite
a satisfactory fragment of `Data.Sequence.Internal`. A few parts are not
handled yet; they require either whole new features or more invasive edits than
I have experience with at the moment.

== Fancy mutual recursion

There remains another issue with the `thin` function we just mentioned:
it is mutually recursive with another function.
*hs-to-coq* currently does not support the combination of mutually recursive
functions with termination annotations other than the basic one (`struct`).

== Pattern synonyms

At the very beginning, *hs-to-coq* simply refused to process `Data.Sequence`
because *hs-to-coq* doesn't handle pattern synonyms.
Now it at least skips pattern synonyms with a warning instead of failing.
One still has to manually add edits to ignore declarations that use pattern
synonyms, since it's not too easy to tell whether that's the case without
a more involved analysis than is currently done.

== Partial functions

The remaining bits are partial functions, internally use partial functions,
or are defined by recursion on `Int` and I haven't looked into how to do it
yet.

= Soft improvements

Some changes that aren't strictly necessary to get the job done,
but made my life a little easier.

== Order of declarations

In Haskell, declarations can be written in any order (except when Template
Haskell is involved) and they can refer to each other just fine.

In Coq, declarations must be ordered because of the restrictions on recursion.
Type classes further complicate this story because of their implicitness:
we cannot know whether an instance is used in an expression without type
checking, and *hs-to-coq* currently stops at renaming.

For now, we have a "best guess" implementation using a "stable topological
sort", trying to preserve an *a priori* order as much as possible, putting
instances before top-level values, and otherwise ordering value declarations as
they appear in the Haskell source.
Of course that doesn't always work, so there are edits to create artificial
dependencies between declarations.

It took me a while to notice something wrong with the implementation:
independent definitions were sorted in reverse order, which is the opposite of
what a "stable sort" should do. The sort algorithm itself was fine: the obvious
dependencies were satisfied. And you expect to have things to fix by hand
because of the underspecified nature of the problem at that point. So any
single discrepancy was easily dismissed as "just what the algorithm does". But
after getting annoyed enough that nothing was where I expected it to be, I went
to investigate. The culprit was GHC[^ghc]: renaming produces a list of declarations
in reverse order! This is usually not a problem since the order of declarations
should not matter in Haskell[^ast], but in our case we have to sort the declarations
in source order before applying the stable topological sort.
That ensures that the order in our Coq output is similar to the order in the
Haskell input.

[^ghc]: Tested with GHC 8.4

[^ast]: And the AST is annotated with source locations so we don't get lost.

== Module aliases

In edits files, identifiers must be fully qualified. This prevents ambiguities
since edits don't belong to any one module.

Module names can get quite long. It was tedious to repeat `Data.Sequence.Internal`
over and over.
There was already an edit to *rename* a module, but that changes the name of
the file itself and affects other modules using that module.
I added a new edit to *abbreviate* a module, without those side effects.
In fact, that edit only affects the edits file it is in. The parser expands
the abbreviation on the fly whenever it encounters an identifier, and after the
parser is done, the abbreviation is completely forgotten.

```
module alias Seq Data.Sequence.Internal
# "Seq" is now an abbreviation of "Data.Sequence.Internal"
```

---

- [*hs-to-coq* source](https://github.com/plclub/hs-to-coq/)
- [*hs-to-coq* tutorial](https://www.cis.upenn.edu/~plclub/blog/2020-10-09-hs-to-coq/)
