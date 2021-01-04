---
title: Theory of iteration and recursion
keywords: ["theory"]
---

Recursion and iteration are two sides of the same coin.
A common way to elaborate that idea is to express one in terms of the other.
Iteration, recursively: to iterate an action, is to do the action, and then
iterate the action again.
Conversely, a recursive definition can be approximated by unfolding it
iteratively. To implement recursion on a sequential machine, we can use a stack
to keep track of those unfoldings.

So there is a sense in which these are equivalent, but that already presumes
that they are not exactly the same. We think about recursion differently than
iteration. Hence it may a little surprising when recursion and iteration both
appear directly as two implementations of the same interface.

To summarize the main point without all the upcoming category theory jargon,
there is one signature which describes an operator for iteration, recursion, or
maybe a bit of both simultaneously, depending on how you read the symbols `==>`
and `+`:

```haskell
iter :: (a ==> a + b) -> (a ==> b)
```

= Iteration operator

The idea of "iteration" is encapsulated by the following function `iter`:

```haskell
iter :: (a -> Either a b) -> (a -> b)
iter f a =
  case f a of
    Left a' -> iter f a'
    Right b -> b
```

`iter` can be thought of as a "while" loop.
The body of the loop `f` takes some state `a`, and either says "continue" with
a new state `a'` to keep the loop going, or "break" with a result `b`.

= Iterative categories

We can generalize `iter`. It transforms "loop bodies" into "loops", and rather
than functions, those could be entities in any category. An iteration operator
on some category denoted `(==>)` is a function with the following signature:

```haskell
iter :: (a ==> a + b) -> (a ==> b)
```

satisfying a bunch of laws, with the most obvious one being a fixed point
equation:[^laws]

```haskell
iter f = (f >>> either (iter f) id)
```

where `(>>>)` and `id` are the two defining components of a [category][category],
and `either` is the eliminator for sums (`+`).
The technical term for "a category with sums" is a cocartesian category.

[category]: https://hackage.haskell.org/package/base-4.14.1.0/docs/Control-Category.html#t:Category

[^laws]: The notion of "iterative category" is not quite standard;
[here is my version in Coq][itree] which condenses the little I could digest
from the related literature (I mostly skip a lot and look for equations or
commutative diagrams).
Those and other relevant equations can be found in the book
[*Iteration Theories: The Equational Logic of Iterative Processes*][bloom-esik]
by Bloom and Ésik (in Section 5.2, Definition 5.2.1 (fixed point equation), and
Theorems 5.3.1, 5.3.3, 5.3.9). It's a pretty difficult book to just jump into though.
The nice thing about category theory is that such dense formulas can be
replaced with pretty pictures, like
[in this paper][metalanguage-iteration] (page 7).
For an additional source of diagrams and literature, a related notion is that of
[*traced monoidal categories*][tmc]---every iterative category is traced monoidal.

[bloom-esik]: http://citeseerx.ist.psu.edu/viewdoc/summary?doi=10.1.1.363.3634
[metalanguage-iteration]: https://arxiv.org/abs/1807.11256
[tmc]: https://en.wikipedia.org/wiki/Traced_monoidal_category
[itree]: https://github.com/DeepSpec/InteractionTrees/blob/master/theories/Basics/CategoryTheory.v#L485-L506

```haskell
class Category k => Cocartesian k where
  type a + b    -- Not fully well-formed Haskell.
  either :: k a c -> k b c -> k (a + b) c
  left :: k a (a + b)
  right :: k b (a + b)

-- Replacing k with an infix (==>)
-- either :: (a ==> c) -> (b ==> c) -> (a + b ==> c)
```

Putting this all together, an *iterative category* is a cocartesian category
plus an `iter` operation.

```haskell
class Cocartesian k => Iterative k where
  iter :: k a (a + b) -> k a b
```

The fixed point equation provides a pretty general way to define `iter`.
For the three in this post, it produces working functions in Haskell.
In theory, properly sorting out issues of non-termination can get hairy.

```haskell
iter :: (a -> Either a b) -> (a -> b)
iter f = f >>> either (iter f) id
-- NB: (>>>) = flip (.)
```

= Recursion operator

Recursion also provides an implementation for `iter`, but in the opposite category,
`(<==)`. If you flip arrows back the right way, this defines a twin interface of
"coiterative categories". Doing so, sums `(+)` become products `(*)`.

```haskell
class Cartesian k => Coiterative k where
  coiter :: k (a * b) a -> k b a

-- with infix notation (==>) instead of k,
-- coiter :: (a * b ==> a) -> (b ==> a)
```

We can wrap any instance of `Iterative` as an instance of `Coiterative` and
vice versa, so `iter` and `coiter` can be thought of as the same interface in
principle. For particular implementations, one or the other direction may seem
more intuitive.

If we curry and flip the argument,
the type of `coiter` becomes `(b -> a -> a) -> b -> a`,
which is like the type of `fix :: (a -> a) -> a` but with
the functor `(b -> _)` applied to both the domain `(a -> a)`
and codomain `a`: `coiter` is `fmap fix`.

```haskell
coiter' :: (b -> a -> a) -> b -> a
coiter' = fmap fix
```

The fixed point equation provides an equivalent definition.
We need to flip `(>>>)` into `(<<<)` (which is `(.)`),
and the dual of `either` does not have a name in the standard
library, but it is `liftA2 (,)`.

```haskell
coiter :: ((a, b) -> a) -> b -> a
coiter f = f . liftA2 (,) (coiter f) id

-- where --

liftA2 (,) :: (c -> a) -> (c -> b) -> (c -> (a, b))
```

That latter definition is mostly similar to the naive definition
of `fix`, where `fix f` will be reevaluated with every unfolding.

```haskell
fix :: (a -> a) -> a
fix f = f (fix f)
```

We have two implementations of `iter`, one by iteration, one by recursion.
Iterative categories thus provide a framework generalizing both iteration and
recursion under the same algebraic rules.

From those two examples, one might hypothesize that `iter` models
iteration, while `coiter` models recursion. But here is another example
which suggests the situation is not as simple as that.

= Functor category, free monads

We start with the category of functors `Type -> Type`,
which is equipped with a sum:

```haskell
data (f :+: g) a = L (f a) | R (g a)
```

But the real category of interest is the Kleisli category of the "monad of free
monads", *i.e.*, the mapping [`Free`][free] from functors `f` to the free
monads they generate `Free f`. That mapping is itself a monad.

[free]: https://hackage.haskell.org/package/free-5.1.6/docs/Control-Monad-Free.html#t:Free

```haskell
data Free f a = Pure a | Lift (f (Free f a))
```

An arrow `f ==> g` is now a natural transformation `f ~> Free g`,
*i.e.*, `forall a. f a -> Free g a`:

```haskell
-- Natural transformation from f to g
type f ~> g = forall a. f a -> g a
```

One intuition for that category is that functors `f` are *interfaces*,
and the free monad `Free f` is inhabited by expressions, or *programs*, using
operations from the interface `f`.
Then a natural transformation `f ~> Free g` is an *implementation* of the
interface `f` using interface `g`. Those operations compose naturally:
given an implementation of `f` in terms of `g` (`f ~> Free g`),
and an implementation of `g` in terms of `h` (`g ~> Free h`),
we can obtain an implementation of `f` in terms of `h` (`f ~> Free h`).
Thus arrows `_ ~> Free _` form a category---and that also mostly implies that
`Free` is a monad.

We can define `iter` in that category. Like previous examples, we can define it
without thinking by using the fixed point equation of `iter`.
We will call `rec` this variant of `iter`, because it actually behaves a lot
like `fix` whose name is already taken:

```haskell
rec :: (f ~> Free (f :+: g)) -> (f ~> Free g)
rec f = f >>> either (rec f) id

-- where --

(>>>) :: (f ~> Free g) -> (g ~> Free h) -> (f ~> Free h)
id :: f ~> Free f
either :: (f ~> h) -> (g ~> h) -> (f :+: g ~> h)
```

We eventually do have to think about what `rec` means.

The argument `f ~> Free (f :+: g)` is a *recursive* implementation of an
interface `f`: it uses an interface `f :+: g` which includes `f` itself.
`rec f` composes `f` with `either (rec f) id`, which is basically some
plumbing around `rec f`.
Consequently, `rec` takes a recursive program `prog :: f ~> Free (f :+: g)`, and
produces a non-recursive program `f ~> Free g`, using that same result to implement
the `f` calls in `prog`, so only the other "external" calls in `g` remain.

That third version of `iter` (`rec`) has similarities to both of the previous versions
(`iter` and `fix`).

Obviously, the whole explanation above is given from perspective of
recursion, or self-referentiality. While `fix` simply describes recursion
as fixed points, `rec` provides a more elaborate model
based on an explicit notion of syntax using `Free` monads.

There is also a connection to the eponymous interpretation of `iter` as
iteration. Both `iter` and `rec` use a sum type (`Either` or `(:+:)`), representing
a choice: to "continue" or "break" the loop, to "recurse" or "call" an external
function.

= Control-flow graphs

That similarity may be more apparent when phrased in terms of low-level
"assembly-like" languages, control-flow graphs.
Here, programs consist of blocks of instructions, with "jump" instructions pointing
to other blocks of instructions. Those programs form a category.
The objects, *i.e.*, interfaces, are sets of "program labels" that one can jump to.
A program `p : I ==> J` exposes a set of "entry points" `I` and a set of "exit
points" `J`: execution enters the program `p` by jumping to a label in `I`, and
exits it by jumping to a label in `J`. There may be other "internal jumps"
within such a program, which are not visible in the interface `I ==> J`.

The operation `iter : (I ==> I + J) -> (I ==> J)` takes a program
`p : I ==> I + J`, whose exit points are in the disjoint union of `I` and `J`;
`iter p : I ==> J` is the result of linking the exit points in `I` to the
corresponding entry points, turning them into internal jumps. With some extra
conditional constructs, we can easily implement "while" loops
("`iter` on `_ -> _`") with such an operation.

Simple jumps ("jump to this label") are pretty limited in expressiveness.
We can make them more interesting by adding return locations to jumps, which
thus become "calls" ("push a frame on the stack and jump to this label")---to
be complemented with "return" instructions.
That generalization allows us to (roughly) implement `rec`,
suggesting that those various interpretations of `iter` are maybe not as
different as they seem.

---

```haskell
iter :: (a ==> a + b) -> (a ==> b)

-- specializes to --

iter   :: (a -> Either a b)     -> (a -> b)
coiter :: ((a, b) -> a)         -> (b -> a)
rec    :: (f ~> Free (f :+: g)) -> (f ~> Free g)
```
