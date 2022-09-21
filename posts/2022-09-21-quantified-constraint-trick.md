---
title: The quantified constraint trick
keywords: ["haskell", "haskell-tricks", "libraries"]
---

My favorite Haskell trick is how to use quantified constraints with type families.
[Kudos to *Iceland_jack* for coming up with it.](https://gitlab.haskell.org/ghc/ghc/-/issues/14860#note_188736)

= Quantified constraints and type families

`QuantifiedConstraints` is an extension from GHC 8.6 that lets us
use `forall` in constraints.

It lets us express constraints for instances of higher-kinded types like `Fix`:

```haskell
newtype Fix f = Fix (f (Fix f))

deriving instance (forall a. Eq a => Eq (f a)) => Eq (Fix f)
```

Other solutions existed previously, but they're less elegant:

```haskell
deriving instance Eq (f (Fix f)) => Eq (Fix f)

instance Eq1 f => Eq (Fix f) where ...
```

It also lets us say that a monad transformer indeed transforms monads:

```haskell
class (forall m. Monad m => Monad (t m)) => MonadTrans t where
  lift :: m a -> t m a
```

(Examples lifted from [the GHC User Guide on `QuantifiedConstraints`](https://downloads.haskell.org/ghc/latest/docs/users_guide/exts/quantified_constraints.html), section Motivation.)

One restriction is that the conclusion of a quantified constraint cannot
mention a type family.

```haskell
type family F a

-- (forall a. C (F a))  -- Illegal type family application in a quantified constraint
```

A quantified constraint can be thought of as providing a local instance,
and they are subject to a similar restriction on the shape of instance heads
so that instance resolution may try to match required constraints with
the head of existing instances.

Type families are not matchable: we cannot determine whether an applied
type family `F a` matches a type constructor `T` in a manner satisfying the
properties required by instance resolution ("coherence"). So type families
can't be in the conclusion of a type family.

= The quantified constraint trick

== Step 1

To legalize type families in quantified constraints,
all we need is a *class synonym*:

```haskell
class    C (F a) => CF a
instance C (F a) => CF a
```

That `CF a` is equivalent to `C (F a)`, and `forall a. CF a` is legal.

== Step 2?

Since GHC 9.2, Step 1 alone solves the problem. It Just Works™.
[And I don't know why.](https://mail.haskell.org/pipermail/haskell-cafe/2022-September/135571.html)

Before that, for GHC 9.0 and prior,
we also needed to hold the compiler's hand and tell it how
to instantiate the quantified constraint.

Indeed, now functions may have constraints of the form `forall a. CF a`,
which should imply `C (F x)` for any `x`.
Although `CF` and `C (F x)` are logically related, when `C (F x)` is required,
that triggers a search for instances of the class `C`, and not the `CF` which
is provided by the quantified constraint.
The search would fail unless some hint is provided to the compiler.

When you require a constraint `C (F x)`, insert a type annotation mentioning
the `CF x` constraint (using the `CF` class instead of `C`).

```haskell
_ {- C (F x) available here -} :: CF x => _
```

Inside the annotation (to the left of `::`), we are given `CF x`, from which `C
(F x)` is inferred as a superclass. Outside the annotation, we are requiring `CF x`,
which is trivially solved by the quantified constraint `forall a. CF a`.

== Recap

```haskell
-- Mixing quantified constraints with type families --

class C a
type family F a

-- forall a. C (F a)  -- Nope.

class    C (F a) => CF a  -- Class synonym
instance C (F a) => CF a

-- forall a. CF a     -- Yup.

-- Some provided function we want to call.
f :: C (F t) => t

-- A function we want to implement using f.
g :: (forall a. CF a) => t
g = f               -- OK on GHC >= 9.2
g = f :: CF t => t  -- Annotation needed on GHC <= 9.0
```

The part of that type annotation that really matters
is the constraint. The rest of the type to the right of the arrow
is redundant. Another way to write only the annotation uses the following
identity function with a fancy type:

```haskell
with :: forall c r. (c => r) -> (c => r)
with x = x
```

So you can supply the hint like this instead:

```haskell
g :: forall t. (forall a. CF a) => t
g = with @(CF t) f
```

= Application: *generic-functor*

What do I need that trick for? It comes up in generic metaprogramming with
parameterized types.

Imagine deriving `Functor` for `Generic` types (no `Generic1`, which is not as
general as you might hope). One way is to implement the following class on
generic representations:

```haskell
class RepFmap a a' rep rep' where
  repFmap :: (a -> a') -> rep -> rep'
```

A type constructor `f :: Type -> Type` will be a `Functor` when its
generic representation (`Rep`) implements `RepFmap a a'`...
for all `a`, `a'`.

```haskell
-- Class synonym for generically derivable functors
class    (forall a. Generic (f a), forall a a'. RepFmap a a' (Rep (f a) ()) (Rep (f a') ())) => GFunctor f
instance ...   -- idem (class synonym)

-- Wait a second...
```

But that is illegal, because the type family `Rep` occurs in the conclusion of
a quantified constraint. Time for the trick! We give a new name to the conclusion:

```haskell
class    RepFmap a a' (Rep (f a) ()) (Rep (f a') ()) => RepFmapRep a a' f
instance ...  -- idem (class synonym)
```

And boom, the quantified constraint can be written:

```haskell
-- Now this works!
class    (forall a. Generic (f a), forall a a'. RepFmapRep a a' f) => GFunctor f
instance ...   -- idem (class synonym)
```

To obtain the final generic implementation of `fmap`, we wrap `repFmap` between `to` and `from`.

```haskell
gfmap :: forall f a a'. GFunctor f => (a -> a') -> f a -> f a'
gfmap f =
  with @(RepFmapRep a a' f)             -- Hand-holding for GHC <= 9.0
    (to @_ @() . repFmap f . from @_ @())
```

Et voilà.

[(Gist of this example)](https://gist.github.com/Lysxia/7714c19ef9c17b487a46c804694fc0f9)

---

= Appendix: Couldn't we do this instead?

If you've followed all of that, there's one other way you might try defining
`gfmap` without `QuantifiedConstraints`, by just listing the three constraints
actually needed in the body of the function.

```haskell
-- Bad gfmap!
gfmap ::
  Generic (f a) =>
  Generic (f a') =>
  RepFmap a a' (Rep (f a) ()) (Rep (f a') ()) =>
  (a -> a') -> f a -> f a'
gfmap f = to @_ @() . repFmap f . from @_ @()
```

This is okay as long as it is only ever used to implement `fmap` as in:

```haskell
fmap = gfmap
```

Any other use voids a guarantee you didn't know you expected.

The thing I haven't told you is that `RepFmap` is implemented with...
incoherent instances! In fact, `gfmap` may behave differently depending
on how it is instantiated *at compile time*.

For example, for a functor with a field of constant type:

```haskell
data T a b = C Int a b
  deriving Generic
```

`gfmap @(T a) @b @b'` where `a`, `b` and `b'` are distinct type variables
behaves like `fmap` should. But `gfmap @(T Int) @Int @Int`
will unexpectedly apply its argument function to every field.
They all have type `Int`, so a function `Int -> Int` can and will be applied to
all fields.

I could demonstrate this if I had implemented `RepFmap`...
Luckily, there is a more general version of this "bad `gfmap`" readily
available in my library
[*generic-functor*](https://hackage.haskell.org/package/generic-functor).
It can be very incoherent, but if you follow some rules, it can also be very
fun to use.

== Playing with fire

`gsolomap`[^multimap] is a function from *generic-functor* that can implement
`fmap`, and much more.

[^multimap]: `gsolomap` accepts one function parameter. There is also
`gmultimap` which accepts arbitrarily many functions.

```haskell
fmapT :: (b -> b') -> T a b -> T a b'
fmapT = gsolomap
```

Map over the first parameter if you prefer:

```haskell
firstT :: (a -> a') -> T a b -> T a' b
firstT = gsolomap
```

Or map over both type parameters at once:

```haskell
bothT :: (a -> a') -> T a a -> T a' a'
bothT = gsolomap
```

I don't know what to call this, but `gsolomap` also does what you might guess
from this type:

```haskell
watT ::
  (a -> a') ->
  T (a , a ) ((a  -> a') -> Maybe a ) ->
  T (a', a') ((a' -> a ) -> Maybe a') 
watT = gsolomap
```

It's important to specialize `gsolomap` with *distinct type variables*
(`a` and `a'`).
You cannot refactor code by inlining a function if its body uses `solomap`,
as it risks breaking that requirement.

== Witnessing incoherence

For example, apply the `fmapT` defined above to some concrete
arguments. See how the result changes then you replace `fmapT` with its
definition, `gsolomap`.

```haskell
fmapT    ((+1) :: Int -> Int) (C 0 0 0) == C 0 0 1 :: T Int Int
gsolomap ((+1) :: Int -> Int) (C 0 0 0) == C 1 1 1 :: T Int Int  -- Noooooo...
```

[(Gist of those `gsolomap` (counter)examples)](https://gist.github.com/Lysxia/a83b16c992d9945576fbff3611ab8f3a)

This is why `gfmap`'s signature should use quantified constraints:
this guarantees that when the `RepFmap` constraint is solved,
the first two parameters are going to be *distinct type variables*,
thanks to the universal quantification (`forall a a'`).
Thus, incoherence is hidden away.

Following that recipe, *generic-functor* contains *safe* implementations of
`Functor`, `Foldable`, `Traversable`, `Bifunctor`, and `Bitraversable`.

In particular, the type of `gfmap` guarantees that it has a unique
inhabitant satisfying `gfmap id = id`, and this property is quite
straightforward to check by visual inspection of the implementation.

After all, `gfmap` will essentially do one of three things:
(1) it will be `id` on types that don't mention the type parameters
in its function argument `a -> a'`, (2) it will apply the provided function
`f`, or (3) it will `fmap` (or `bimap`, or `dimap`) itself through a type
constructor. In all cases (with some inductive reasoning for (3)),
if `f = id`, then `gfmap f = id`.

```haskell
gfmap f = id
gfmap f = f
gfmap f = fmap (gfmap f)
```

The bad `gfmap` (without `QuantifiedConstraints`) or `gsolomap` fail this
property, because the extra occurrences of `a` and `a'` in its constraint make
their signatures have a different "shape" from `fmap`.

The trade-off is that those safe functions can't do the same crazy things
as `gsolomap` above.
