---
title: Infinite types and existential newtypes
keywords: [haskell]
---

Can we construct an infinite type in Haskell?
I don't mean "infinite" in the sense that it has infinitely many inhabitants,
but that the type itself, its name, consists of an infinite tree of type
constructors (an equirecursive type, more or less). For example, the following
type synonym, if it were legal, would define a type which is an infinite tree
of `(->)`.

```haskell
type T = T -> T
```

<details class="code-details">
<summary>Spoilers</summary>
No, we can't.
</details>

== With type families?

Here's a first attempt with type families. This compiles:

```haskell
type family F where
  F = F -> F
```

This compiles still:

```haskell
x :: F
x = x
```

But surprisingly, this doesn't:

```haskell
-- Nope.
x :: F
x = undefined
```

GHC tries the impossible task of unfolding `F` completely to unify the type of
`undefined` with `F`, and fails after spending too much fuel:

```
• Reduction stack overflow; size = 201
  When simplifying the following type: F
  Use -freduction-depth=0 to disable this check
  (any upper bound you could choose might fail unpredictably with
   minor updates to GHC, so disabling the check is recommended if
   you're sure that type checking should terminate)
```

So anything beyond `x = x` has no hope of working.

```haskell
-- Nope.
x :: F
x y = y
```

== With existential types?

Another idea is to hide the infinite type in an existential type, which would
avoid the problematic equation causing the loop in the type checker.

```haskell
data Some where
  MkSome :: a -> Some
```

The goal is to somehow wrap an `x :: a` such that:

```haskell
MkSome x = MkSome (x, x)
```

which would implicitly lead to this desired equation on the type of `x`:

```
a ~ (a, a)
```

We could try the following:

```haskell
u :: Some
u = MkSome (x, x) where
  MkSome x = u
```

But that is rejected. It is also not quite clear where the type of `x` is bound.
Maybe it means this (and that's the closest to how GHC actually understands it):

```haskell
u :: Some
u = MkSome (x, x) where
  x = case u of MkSome x -> x
```

where the type of `x` is bound by the pattern under the `case`, and would thus
"escape its scope".

Or maybe it means this, where we pattern-match first to make the existentially
quantified type variable available, before wrapping it again in a pair:

```haskell
u :: Some
u = case u of
  MkSome x -> MkSome (x, x)
```

Of course, that is not a productive definition.

For completeness, here's yet another version, but again with the same
scoping problem as the first one:

```haskell
u :: Some
u = MkSome (case u of
  MkSome x -> (x, x))
```

It appears that *unpacking an existentially quantified type requires
computation*. Do it too early and you're too strict, try to delay it and
type variables escape their scope.

This is puzzling, because "existential quantification" should be a matter
of types, of abstraction, something to be erased at run time... like `newtype`!

== With existential newtypes?

If we could define an "existential newtype", whose constructor has no run-time
presence, then perhaps this would do the job:

```haskell
newtype Some where  -- Pretend this makes sense
  MkSome :: a -> Some

u :: Some
u = case u of
  MkSome x -> MkSome (x, x)
```

It is straightforward to understand in terms of type erasure, the newtype goes
away, so we would be left with this (as we might expect):

```haskell
u = (u, u)
```

However, it seems awfully difficult to formalize what is going on with explicit
types instead, which would otherwise be the obvious way to guarantee type
soundness (i.e., "well-typed programs do not go wrong").

Indeed, newtypes are compiled using coercions. For example, a `case` expression
on the `Identity` newtype becomes a coercion `runIdentity :: Identity a -> a`
inside the term (you can check it on real examples with the compiler
option `-ddump-ds` (desugarer output)):

```haskell
case v of
  Identity y -> f y

-- desugars to --

f (runIdentity v)
```

But if we want to allow newtypes to use existential quantification,
there is no obvious type we can give to an "`unMkSome`" coercion, especially
because of the scoping issues we already ran into earlier.[^solutions]

[^solutions]: Potential, but clunky, alternatives to model that:
dependent types, that can refer explicitly to the hidden type
(`runMkSome :: foreach u : Some . case u of MkSome @a _ -> a`),
or fancier scoping rules that would somehow allow type variables to
"temporarily escape their scope" (no idea what that may look like).

Does that mean we should throw away the whole notion of "existential newtype"?
Of course not. It can be useful to not pay the cost of an extra constructor at
run time for existential quantification.
The question comes up once in a while: [here's the relevant ticket on GHC's
issue tracker](https://gitlab.haskell.org/ghc/ghc/issues/1965).
Although `newtype` is currently the *de facto* way to do such things, a different
solution that would also work for existential types, [and which was proposed in
that discussion](https://gitlab.haskell.org/ghc/ghc/issues/1965#note_56959),
is to unpack `data` types with one strict single-field constructor.
That proposal is especially nice as it doesn't add anything new to the language
itself, it is purely an optimization.

Because of that, it does not provide an answer to the above puzzle of
constructing infinite types, and that's a relief! That endeavor was
*purposefully dubious*: a working solution would suggest that something
extremely ~~wrong~~ *interesting* is going on with the type system.

Nevertheless, investigating how such a questionable requirement could be met
lead to some surprising interaction between existential types and recursion.
