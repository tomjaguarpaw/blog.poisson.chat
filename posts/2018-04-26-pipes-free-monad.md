---
title: Pipes define a free monad
---

The core type of the [*pipes*](https://hackage.haskell.org/package/pipes)
library is a free monad.
Indeed,
[`Pipes.Proxy`](https://github.com/Gabriel439/Haskell-Pipes-Library/blob/a89069e9dfcf177fe608c5837bda1eff1a4445f1/src/Pipes/Internal.hs#L71-L75)
is equivalent to `Free (ProxyF _ _ _ _ _)`, where

```haskell
data Free f a
  = Free (f (Free f a))
  | Pure a

data ProxyF a' a b' b m x
  = Request a' (a  -> x)
  | Respond b  (b' -> x)
  | M          (m     x)
```

That's nothing ground-breaking if you're familiar with free monads. In fact, [it
used to be the literal definition of
pipes](https://github.com/Gabriel439/Haskell-Pipes-Library/commit/372165a5d5be53f6308f9e465fc132e498f9d3e6#diff-4b5bacb7cbf07e2a8310ea839a4f19aeR59),
using [*free*](https://hackage.haskell.org/package/free) before I even knew
Haskell was a thing.

Nevertheless, my previous understanding of *pipes* was mostly based on the
interface (which is very nice by the way; the diagrams in
[`Pipes.Core`](https://hackage.haskell.org/package/pipes-4.3.9/docs/Pipes-Core.html)
are a pleasure to contemplate), while I needed all my focus to follow the
implementation. Hence, in spite of now extensive experience with free monads,
it took one more wander in front of the source code of *pipes* for me to have
that epiphany.

A much deeper understanding of the whole business followed immediately.
With free monads as a common starting point[^free],
it became much easier to compare
[*pipes*](https://hackage.haskell.org/package/pipes-4.3.9/docs/Pipes-Internal.html#t:Proxy),
[*conduit*](https://hackage.haskell.org/package/conduit-1.3.0.2/docs/Data-Conduit-Internal.html#t:Pipe),
and
[*quiver*](https://hackage.haskell.org/package/quiver-1.1.3/docs/Control-Quiver-Internal.html):
basically, they're all using free monads for differing I/O-like functors[^quiver].

Now it may be just another occasionally useful fun fact, but that one somehow
felt like a personal achievement. That realization gave me a strong impression
of the power of abstraction.

[^free]:
  [`Free`](https://hackage.haskell.org/package/free-5.0.1/docs/Control-Monad-Free.html#t:Free)
  encapsulates a form of recursion (it's a sibling of
  [`Fix`](https://hackage.haskell.org/package/recursion-schemes-5.0.2/docs/Data-Functor-Foldable.html#t:Fix)).

[^quiver]:
  *quiver* with its polymorphic continuations is a bit of an outlier, but
  thinking in terms of free monads is at least good enough as a first
  approximation.
