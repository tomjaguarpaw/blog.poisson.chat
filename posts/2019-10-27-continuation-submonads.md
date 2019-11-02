---
title: A monad is just a submonad of the continuation monad, what's the problem?
keywords: [haskell, theory]
---

The [previous
post](https://blog.poisson.chat/posts/2019-10-26-reasonable-continuations.html)
showed off the flexibility of the continuation monad to represent
various effects. As it turns out, it has a deeper relationship with monads in
general.

Disclaimer: this is not a monad tutorial. It will not be enlightening if you're
not already familiar with monads. Or even if you are, probably.
That's the joke.

---

The starting point is the remark that `lift` for the `ContT` monad
transformer is `(>>=)`, and `ContT` is really `Cont`.[^cont]
To make that identity most obvious, we define `Cont` as a type synonym here.

[^cont]: As before, there will be quite some blur on the distinction between
  `Cont`, `ContT`, and `CodensityT`.

```haskell
type Cont r a = (a -> r) -> r

lift :: Monad m => m a -> Cont (m r) a
     -- Monad m => m a -> (a -> m r) -> m r
lift = (>>=)
```

As a monad transformer, it is certainly an odd one. On the one hand,
`Cont (m r)` is a monad which doesn't really care whether `m` is a monad,
or anything at all.
On the other hand, `lift` is `(>>=)`: it directly depends on the full power
of a `Monad`. That contrasts with `StateT` for example, whose `Monad`
instance uses the transformed monad's `Monad` instance, while `lift` only needs
a `Functor`.

== Monads as submonads

If `lift` is `(>>=)`, we can also say that `(>>=)` is `lift`,
suggesting an alternative definition of monads as types that can be "lifted"
into `Cont`, and "unlifted" back, by passing `pure` as a continuation.

```haskell
class Monad m where
  lift :: m a -> Cont (m r) a
  pure :: a -> m a

unlift :: Monad m => Cont (m a) a -> m a
unlift u = u pure
```

We simply renamed `(>>=)` in the `Monad` class, nothing changed
otherwise.[^return]
The new monad laws below are also simple reformulations of the usual monad laws
in terms of `lift` and `unlift` primarily. There's a bit of work to fix the
third law, but no serious difficulties in the process.[^proof]

[^proof]: [A proof in Coq that these new laws imply the old
  ones,](https://gist.github.com/Lysxia/2a587be89bf8a0997a3916d6ed322d7f)
  just to be sure.

Nevertheless, such renaming opens the door to another point of view, where
monads are merely "subsets" of the `Cont` monad, and we can reframe the monad
laws accordingly.
They are the same, and yet, they look completely different.

[^return]: Assuming we've already ditched `return` for `pure`.

```haskell
-- Laws for the lift-pure definition of Monad

unlift . lift = id
(lift . unlift) (pureCont x) = pureCont x
(lift . unlift) (lift u >>=? \x -> lift (k x))
              = (lift u >>=? \x -> lift (k x))
```

where the `pure` and `(>>=)` of `Cont` are called `pureCont` and `(>>=?)`,
clarifying that they are defined once for all, independently of the `Monad`
class. That is the key to resolve the apparent circularity in the title.

```haskell
pureCont :: a -> Cont r a
pureCont a = (\k -> k a)

(>>=?) :: Cont r a -> (a -> Cont r b) -> Cont r b
c >>=? d = (\k -> c (\a -> d a k))
```

The second and third law have a common structure.
An equation `(lift . unlift) y = y` expresses the fact that `y` is in the image
of `lift`. If we also assume the first law `unlift . lift = id`,
that says nothing more.

Another interpretation of the monad laws is now apparent:
they say that a monad `m` is defined by an injection `lift` into a
subset of `Cont (m r)` closed under `pureCont` and `(>>=?)`.
That's why we can say that, by definition,
`m` is a "submonad" of `Cont (m r)`.[^sub]

[^sub]: You may be more familiar with notions of "substructure"
  being refinements of the notion of "subset", and strictly speaking, `m` is
  not a subset of `Cont (m r)`.
  But it is convenient to generalize "substructure" directly to "anything that
  injects into a structure", especially for working in category theory or
  formalizing those ideas in proof assistants based on type theory, where the
  set-theoretic notion of "subset" is awkward to express literally.

But with that fact alone, it wouldn't matter that the codomain of `lift` is
`Cont (m r)`; any monad `n` would do, as we could `unlift` the `(>>=)` of `n`
down to a `(>>=)` for `m`.
The special thing about `Cont` here is that `(>>=)` for `m` is literally
`lift`.

== A symmetric presentation

To push that idea further, one might propose a more symmetric redefinition of
`Monad` as a pair `(lift, unlift)`:

```haskell
class Monad m where
  lift   :: m a -> Cont (m r) a
  unlift :: Cont (m a) a -> m a
```

The remaining asymmetry in the first type parameter of `Cont` can also be
removed by using the `CodensityT` monad transformer:

```haskell
type CodensityT m a = forall r. Cont (m r) a

class Monad m where
  lift   :: m a -> CodensityT m a
  unlift :: CodensityT m a -> m a
```

That's certainly fine. I just prefer the simplicity of `Cont` over
`CodensityT` where we can get away with it.[^haskell]

[^haskell]: By defining `CodensityT` as a type synonym instead of a newtype, we
  would also run into minor problems with impredicativity and type inference.

In any case, we can then define `pure` by "unlifting" `pureCont`:

```haskell
pure :: Monad m => a -> m a
pure = unlift . pureCont
```

A small wrinkle with taking `unlift` as a primitive is that the new laws don't
quite match up to the old laws anymore. For example, for these two laws to be
equivalent (remember that `lift` is `(>>=)`)...

```haskell
unlift . lift = id

-- Corresponding classical monad law
u >>= pure = u
```

... we really want an extra law to "unfold" `unlift`, which is its
definition in the previous version of `Monad`.

```haskell
unlift u = u pure

-- or, without pure
unlift u = u (unlift . pureCont)
```

It's also the only sensible implementation: `unlift` has to apply its argument
`u`, which is a function, to some continuation. The only good choice is `pure`,
and we have to write it into law to prevent other not-so-good choices.[^law]
`pure` is arguably still a simpler primitive than `unlift` in practice,
because one has to implement `pure` explicitly anyway.

[^law]: I'm not actually sure whether the other laws entail this one.

To sum up, the `(lift, unlift)` presentation of `Monad` comes with
an extra fourth law to keep `unlift` in check.

```haskell
unlift . lift = id
(lift . unlift) (pureCont x) = pureCont x
(lift . unlift) (lift u >>=? \x -> lift (k x))
              = (lift u >>=? \x -> lift (k x))

unlift u = u (unlift . pureCont)
```

== What's the problem?

The title seems to be making a circular claim, defining monads in terms of
monads. But it can really be read backwards in a well-founded manner.

The "continuation monad" is a concrete thing, consisting of a function on
types `(_ -> m r) -> m r`, and two operations `pureCont` and `(>>=?)` (which
turn out to be essentially function application and function composition
respectively).

A "submonad of the continuation monad" is a subset[^subset] of the continuation
monad closed under `pureCont` and `(>>=?)`.

Although "monad" appears in those terms, we are defining them as individual
concepts independently of the general notion of "monad", which can in turn be
defined in those terms. Although confusing, the naming is meant to make sense
a posteriori, after everything is defined.

[^subset]: "Subset" is not defined but I hope you get the idea.

== Related results

That is an example of a [representation
theorem](https://en.wikipedia.org/wiki/Representation_theorem),
where some general structure is reduced to another seemingly more specific one.

Cayley's theorem says that every group on a carrier `a` is a subgroup of the group
of permutations (bijective functions) `a -> a`, and the associated injection
`a -> (a -> a)` is exactly the binary operation of the group on `a`.

The Yoneda lemma says that `fmap` is an isomorphism between `m a` and
`forall r. (a -> r) -> m r` for any functor `m` (into Set).

Here we said that `(>>=)` is a (split mono) morphism from `m a` to
`forall r. (a -> m r) -> m r` for any monad `m`.

---

= Generalized Cayley representation theorem (Update from 2019-11-02) {#cayley}

[As was pointed out to me on reddit](https://www.reddit.com/r/haskell/comments/do1h6c/a_monad_is_just_a_submonad_of_the_continuation/f5mpmjh/),
<!-- thanks /u/WhistlePayer -->
this is indeed an application of the generalized Cayley representation theorem.
This connection is studied in detail in the paper *Notions of Computations as
Monoids*, by Exequiel Rivas and Mauro Jaskelioff, JFP 2017.
([PDF](https://www.fceia.unr.edu.ar/~mauro/pubs/Notions_of_Computation_as_Monoids_ext.pdf),
extended version)

The paper shows how to view applicative functors, arrows and monads as monoids
in different categories, and how useful constructions arise from common
abstract concepts such as exponentials, Cayley's theorem, free monoids.
Below is the shortest summary I could make of Cayley's theorem applied to
monads.

Cayley's theorem generalizes straightforwardly from groups to monoids, and then
from monoids (in the category of sets) to monoids in any category with a tensor
`×` (i.e., a monoidal category) and with exponentials[^expo]:
a monoid `m`, given by a pair of morphisms `mult : m × m -> m` and `one : 1 -> m`,
satisfying some conditions, injects into the exponential object `(m -> m)`
by currying the morphism `mult` as `m -> (m -> m)`.

[^expo]: or rather, it is sufficient for `m` alone to be an exponent, so
  `(m -> m)` is defined as an object.

Then consider that statement in the category of endofunctors on *Set*, where
the tensor `×` is functor composition. In this category,

- a monoid is a monad, i.e., a pair `join : m × m -> m` and
  `pure : 1 -> m` (where `1` is the identity functor);

- the exponential object `(m -> m)` is the *codensity monad* on `m`
  (which we've been deliberately confusing with `Cont` throughout the post):
  `CodensityT m a` is the set of natural transformations[^sets] between the
  functor `a -> m _` and `m`.

[^sets]: which is not always a set, but we care when it is.

```haskell
type CodensityT m a = forall r. (a -> m r) -> m r
```

Now, Cayley's theorem translates directly to: a monad is a submonad of the
codensity monad.
