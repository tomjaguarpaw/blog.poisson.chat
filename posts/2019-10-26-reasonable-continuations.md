---
title: The reasonable effectiveness of the continuation monad
keywords: [haskell, theory]
---

There are common monads associated with common effects: `Maybe` for failure,
`[]` (list) for nondeterminism, `State` for state...
What about [the continuation
monad](https://hackage.haskell.org/package/transformers-0.5.6.2/docs/Control-Monad-Trans-Cont.html)?
We shall see why the answer is all of the above, but better.
Indeed, many effects can be understood and implemented in a simple and uniform
fashion in terms of first-class continuations.

<details class="code-details">
<summary>Extensions and imports for this Literate Haskell file</summary>
\begin{code}
{-# LANGUAGE
    InstanceSigs,
    RankNTypes #-}

module Continuations where

import Control.Applicative ((<|>))
import Control.Monad (replicateM, when)
import Data.Foldable (for_)
\end{code}
</details>

= A way too short introduction to continuation-passing style

The key insight behind continuations is that producing a result in a function
is equivalent to calling another function which does the rest of the
computation with that result.

In this small starting example, we apply some function `timesThree`, and
compare the result to 10.
We will transform this code in continuation-passing style.

\begin{code}
example1 :: Int -> Bool
example1 x = 10 < timesThree x where

  timesThree :: Int -> Int
  timesThree x = 3 * x
\end{code}

As our first step, following the train of thought above, instead of taking the
result of `timesThree` and doing something (`10 < _`) with it, let `timesThree`
do that operation directly.

\begin{code}
example2 :: Int -> Bool
example2 x = timesThree x where

  timesThree :: Int -> Bool
  timesThree x = 10 < 3 * x
\end{code}

Of course, that's not much of a `timesThree` function anymore.
Moreover, we know how `3 * x` is going to be used in this case,
but that's quite counter to modularity.
Let us generalize `timesThree`: instead of hard-coding `10 < _`, we
parameterize `timesThree` by the context in which the result `3 * x` will be
used. That context is called the *continuation* `k`.

\begin{code}
example3 :: Int -> Bool
example3 x = timesThree x (\ y -> 10 < y) where

  timesThree :: Int -> (Int -> Bool) -> Bool
  timesThree x k = k (3 * x)
\end{code}

Furthermore, the result of the continuation doesn't have to be of type `Bool`;
we can generalize the type of `timesThree` further to also be parameterized by
the result type `r` of the continuation.
In the main body where we apply `timesThree`, `r` is specialized to the type of
the final result, which is `Bool`.

\begin{code}
example4 :: Int -> Bool
example4 x = timesThree x (\ y -> 10 < y) where

  timesThree :: Int -> (Int -> r) -> r
  timesThree x k = k (3 * x)
\end{code}

That was continuation-passing style (CPS) in a nutshell.

Functions written in CPS can be composed as follows.
Let us refactor the comparison `10 < _` into another CPS function
`greaterThanTen`.
Once the program is entirely written in CPS, the identity function
(here `\ z -> z`) is commonly used as the last continuation,
which receives the final result.

\begin{code}
example5 :: Int -> Bool
example5 x =
    timesThree     x (\ y ->
    greaterThanTen y (\ z ->
    z))

  where

    timesThree :: Int -> (Int -> r) -> r
    timesThree x k = k (3 * x)

    greaterThanTen :: Int -> (Bool -> r) -> r
    greaterThanTen y k = k (10 < y)
\end{code}

Hey, this example looks a lot like `do` notation...
Indeed, note how we changed the result type of `timesThree` from `Int` to
`(Int -> r) -> r`; that mapping between types `(_ -> r) -> r` defines a monad.

= The `Cont` monad

(The descriptions in this section are principally meant to provide context if
you've never seen the implementation of `Cont` before, but they may be quite
dense. It's not necessary to follow every single detail to catch the rest, so
[skipping forward](#many-monads-in-one) is an option.)

A function of type `((a -> r) -> r)` takes a continuation `(a -> r)`
and is expected to produce a result `r`. The obvious way to do that is to apply
the continuation to a value `a`, which is exactly the idea behind continuations
given at the beginning. In fact that is also what it means to "return" a
value in this monad (`pureCont` below; the instances are collapsed at the end
of this section). As we will soon see, the power of the continuation monad
hides in the myriad other ways of using that continuation.

\begin{code}
newtype Cont r a = Cont ((a -> r) -> r)

-- Eliminate Cont
runCont :: Cont r a -> (a -> r) -> r
runCont (Cont m) = m

-- Use the identity continuation to extract the final result.
evalCont :: Cont a a -> a
evalCont (Cont m) = m id

pureCont :: a -> Cont r a
pureCont a = Cont (\ k -> k a)
\end{code}

The *bind* `(>>=)` of the monad captures the pattern in `example5` above
to compose two CPS functions. We start with a continuation `(k :: b -> r)`
for the whole computation (`Cont r b`). We first apply `ma`,
with a continuation which takes the result `a` of `ma`, and passes it to `mc`,
which in turn produces a `b` that is just what `k` wants.

\begin{code}
bindCont :: Cont r a -> (a -> Cont r b) -> Cont r b
bindCont (Cont ma) mc_ =
    Cont (\ k ->
      ma   (\ a ->
      mc a (\ b ->
      k b)))

  where

    mc = runCont . mc_
\end{code}

<details class="code-details">
<summary>
The instances of `Functor`, `Applicative`, `Monad` for `Cont`.
</summary>

\begin{code}
instance Functor (Cont r) where
  fmap :: (a -> b) -> Cont r a -> Cont r b
  fmap f (Cont m) = Cont (\ k -> m (k . f))

instance Applicative (Cont r) where
  pure :: a -> Cont r a
  pure = pureCont

  (<*>) :: Cont r (a -> b) -> Cont r a -> Cont r b
  Cont mf <*> Cont ma = Cont (\ k ->
    mf (\ f ->
    ma (\ a ->
    k (f a))))

instance Monad (Cont r) where
  (>>=) :: Cont r a -> (a -> Cont r b) -> Cont r b
  (>>=) = bindCont
\end{code}
</details>

We can thus rewrite the example using `do`-notation for `Cont`.

\begin{code}
example6 :: Int -> Bool
example6 x = evalCont $ do
    y <- timesThree x
    z <- greaterThanTen y
    pure z

  where

    timesThree :: Int -> Cont r Int
    timesThree x = Cont (\ k -> k (3 * x))

    greaterThanTen :: Int -> Cont r Bool
    greaterThanTen y = Cont (\ k -> k (10 < y))
\end{code}

=== Continuation transformers

Here is another way to look at monadic composition of `Cont`.
If we unfold the definition of `Cont`, a continuation in the continuation monad,
`a -> Cont r b`, is really a function mapping continuations to
continuations, we shall call that a *continuation transformer*:
`(b -> r) -> (a -> r)`.
They map "future" continuations to "present" continuations.[^predicates]

[^predicates]: This is intimately related to [*predicate transformer
  semantics*](https://en.wikipedia.org/wiki/Predicate_transformer_semantics).
  There were two relevant papers at ICFP this year where continuations
  play a great role:

    - *A predicate transformer semantics for effects*,
      by Wouter Swierstra and Tim Baanen, ICFP 2019. ([PDF](http://www.staff.science.uu.nl/~swier004/publications/2019-icfp-tim.pdf))
    - *Dijkstra monads for all*,
      by Kenji Maillard et al., ICFP 2019. ([arxiv](https://arxiv.org/abs/1903.01237))

This suggests to take a look at the fish operator, which
composes monadic continuations.

```haskell
(>=>) :: Monad m => (a -> m b) -> (b -> m c) -> (a -> m c)
(>=>) :: (a -> Cont r b) -> (b -> Cont r c) -> (a -> Cont r c)
```

Looking at the type of `(>=>)`:

1. unfold the definition of `Cont r b` to `(b -> r) -> r`,
2. swap the arguments of each function `a -> (b -> r) -> r` to `(b -> r) -> (a -> r)`.

The result shows that sequencing in the `Cont` monad (with `(>=>)`) is
basically function composition. The function `f >=> g :: a -> Cont r c`
takes a continuation `c -> r`, passes it to the function `g` to produce
a continuation `b -> r`, which goes into `f` to produce a continuation `a -> r`
(note that continuations do flow from right to left in `f >=> g`).

```haskell
(>=>) ::
           (a -> Cont r b)      -> (b -> Cont r c)      -> (a -> Cont r c)
  {- 1 -}  (a -> (b -> r) -> r) -> (b -> (c -> r) -> r) -> (a -> (c -> r) -> r)
  {- 2 -}  ((b -> r) -> a -> r) -> ((c -> r) -> b -> r) -> ((c -> r) -> a -> r)
           (y        -> x     ) -> (z        -> y     ) -> (z        -> x     )

(.) ::
  (y -> x) -> (z -> y) -> (z -> x)
```

= Many monads in one

In spite of (or thanks to) its simplicity, the `Cont` monad is quite versatile.
Many kinds of effects can be represented in `Cont`, all with only the one
`Monad` instance given above, that knows nothing about effects.

In contrast with free monads, which are just waiting to be interpreted,
we can define an effect directly by its operations in `Cont`.

The main idea is to consider what operations we allow on continuations.
Here we describe various restrictions through the result type `r` in
`(a -> r) -> r`, but there may be other ways.

== `Identity`

Our starting point was that producing a result is equivalent to calling the
continuation.
If we add the constraint that the result type `r` is abstract, so that there
are no operations possible on it, then calling the continuation with some
argument `a` is the only option, i.e., we must produce a result `a`, nothing
else. In that case, the continuation monad is isomorphic to the identity monad.

To express the restriction that `r` is abstract, we can use the `forall`
quantifier. If no operations are possible on `r`, then `r` could actually be
any type. So `Cont` computations defined under that restriction are
polymorphic in `r`. We name `Done` the resulting "specialization" of `Cont` (if
we may call it one), with an isomorphism given by `pure :: a -> Done a`
from the `Applicative` instance above, and `runDone :: Done a -> a` below.

\begin{code}
type Done a = forall r. Cont r a
-- forall r. (a -> r) -> r

runDone :: Done a -> a
runDone (Cont m) = m id
\end{code}

== `Maybe`

The next interesting case to consider is that the continuation may be dropped.
But, `(a -> r) -> r` must still somehow produce a result of type `r`.
We thus replace `r` with `Maybe r`, so that a computation can
produce `Nothing` instead of calling the continuation (`abort` below).
As you might expect, the result is a monad which models computations that can
exit early with no output, i.e., a variant of the `Maybe` monad,

<!-- The point is that the continuation monad serves as an alternative foundation
for describing common effects such as `Maybe`. -->

Although the type `Maybe` appears in this definition, the fact that
it is a monad is not used anywhere. In fact, whereas monadic composition
`(>>=)` for `Maybe` is defined with pattern-matching, there is not a single
`case` in the operations for `Abortable` defined here. Each constructor
is only used once, `Nothing` when aborting the computation, `Just`
as the final continuation to indicate success. So `Abortable` does not
just imitate `Maybe`, it is even more efficient!

\begin{code}
type Abortable a = forall r. Cont (Maybe r) a
-- forall r. (a -> Maybe r) -> Maybe r

abort :: Abortable x
abort = Cont (\ _k -> Nothing)

runAbortable :: Abortable a -> Maybe a
runAbortable (Cont m) = m Just
\end{code}

Contrary to `Done` and `Identity`,
`Abortable` is not isomorphic to `Maybe`.
Whereas a `Maybe` computation must decide to be `Just` or `Nothing`
on the spot, an `Abortable` is a function `(a -> Maybe r) -> Maybe r`,
which may inspect the continuation before making a decision,
even though "intuitively" it's not supposed to.

Thus we can construct a computation `secondGuess` which is expected to return a
`Bool`, calls the continuation with `True` (like `pure True` would) but
backtracks to `False` if that fails.

\begin{code}
secondGuess :: Abortable Bool
secondGuess = Cont (\k -> k True <|> k False)

pureTrue :: Abortable Bool
pureTrue = pure True
\end{code}

`runAbortable` maps both `secondGuess` and `pureTrue` to `Just True`,
but they behave differently with a continuation which fails on `True` and
succeeds on `False`.

Nevertheless, it is not possible to construct examples such as `secondGuess`
with only the monad operations and `abort`;
you have to break the `Abortable` abstraction.
In that sense, `Abortable` is still a practical alternative to the `Maybe`
monad.

== `Either`

Naturally, a slight variant of "exit early" is to "exit early with an explicit
error", obtained by replacing `Maybe` with `Either e`.

\begin{code}
type Except e a = forall r. Cont (Either e r) a
-- forall r. (a -> Either e r) -> Either e r

throw :: e -> Except e a
throw e = Cont (\ _k -> Left e)

runExcept :: Except e a -> Either e a
runExcept (Cont m) = m Right
\end{code}

== `State`

What if the continuation takes an extra parameter, with result type `s -> r`?
Then we may want to call it with different parameters, resulting in a notion of
stateful computation.

Remember that the result type `s -> r` is both the result type of the
continuation, and of the whole computation (`(a -> s -> r) -> s -> r`).
The whole computation can just call the continuation (with some value `a`) to
produce a result `s -> r`, or it can first take the parameter `s`, and
obtain an `r` by calling the continuation with a different state.

Thus `get` takes that parameter `s`, and feeds it twice to the continuation
`k :: s -> s -> r`, keeping the state (second argument) unchanged, but also
giving it as the main (first) argument of the subsequent computation.
The other function, `put` ignores that parameter, and calls the continuation
`k :: () -> s -> r` with another state given externally.

\begin{code}
type State s a = forall r. Cont (s -> r) a
-- forall r. (a -> s -> r) -> s -> r

get :: State s s
get = Cont (\ k s -> k s s)

put :: s -> State s ()
put s = Cont (\ k _s -> k () s)

runState :: State s a -> s -> (a, s)
runState (Cont m) = m (,)
\end{code}

That `State` is isomorphic to the standard definition, `s -> (s, a)`.
Indeed, contrary to `Abortable`, there is no observation to be made about the
continuation `a -> s -> r` when `r` is abstract.

As with `Maybe`/`Either`, there is no pattern-matching on pairs going on.
The `s` and the `a` are always just two arguments to the continuation, and a
pair gets built up only in the final continuation in `runState`.

== `Writer`

Are we running out of ideas for what to put in `Cont _ a`?

Above we tried `r`, `Either e r` (sums!), `s -> r` (exponentials!). Surely we
should also try products.
The result is not quite nice, because to do anything with the pair
we have to break the property that was maintained until now: that the
continuation `k` is the last thing we call.

We can `tell` an element of a monoid, by appending it in front of whatever the
rest of the computation outputs.

\begin{code}
type Writer w a = forall r. Cont (w, r) a
-- forall r. (a -> (w, r)) -> (w, r)

tell :: Monoid w => w -> Writer w ()
tell w = Cont (\ k ->
  let (w0, r) = k () in (w <> w0, r))

runWriter :: Monoid w => Writer w a -> (w, a)
runWriter (Cont m) = m (\ a -> (mempty, a))
\end{code}

== `State`, reversed

`Cont (w, r)` can also be viewed as a variant of `State`. Instead of treating
`w` as a monoid, we can let the user update it however they want.
However, that update happens *after* the rest of the computation is done,
so the last update (in the order they would appear in a `do` block for example)
is applied first to the initial state. This is the
*reverse state monad*, where modifications map the future state to the
past state.

Getting the current state in the `RState` monad requires recursion:
the current state comes from the future (the continuation), which is
asking for the current state itself. With this `rget` operation,
you have to be careful not to introduce any causality loop and
accidentally tear down the fabric of reality.

Compare our `RState` with [a more conventional definition of
it](https://hackage.haskell.org/package/rev-state-0.1.2/docs/Control-Monad-Trans-RevState.html)
as `s -> (a, s)`. There, recursion is used in the definition of `(>>=)`,
while `get` is trivial, which is a situation opposite to `RState`.

\begin{code}
type RState s a = forall r. Cont (s, r) a
-- forall r. (a -> (s, r)) -> (s, r)

rmodify :: (s -> s) -> RState s ()
rmodify f = Cont (\ k ->
  let (s, r) = k () in (f s, r))

rget :: RState s s
rget = Cont (\ k ->
  let (s, r) = k s in (s, r))

runRState :: RState s a -> s -> (s, a)
runRState (Cont m) s = m (\a -> (s, a))
\end{code}

== `Tardis`

We can combine `State`, given by `s -> r`, and `RState`, given by `(s, r)`:
instead, if we make the continuation result type `s -> (s, r)`, we obtain a
[Tardis
monad](https://hackage.haskell.org/package/tardis-0.4.1.0/docs/Control-Monad-Trans-Tardis.html),
with one state going forward in time, and one going backwards.

The forward and backward states don't actually have to be the same,
so we can also generalize `(s -> (s, r))` into `(fw -> (bw, r))`.

\begin{code}
type Tardis bw fw a = forall r. Cont (fw -> (bw, r)) a
-- forall r. (a -> fw -> (bw, r)) -> fw -> (bw, r)
\end{code}

== `List`

One last standard type we haven't tried for `r` is the type of lists.
In our previous examples, computations called the continuation only once
(or at least they should, we can exclude `secondGuess` as a degenerate
example).
Equipping the result type with the structure of lists, we can call a
continuation multiple times, and return a combination of all the results.

This provides a model of nondeterministic computations, keeping track of all
possible executions, which is the same interpretation as the standard list `[]`
monad.

`decide` chooses both `True` and `False`, i.e., it calls the continuation
on both booleans, and concatenates the results together.
`vanish` chooses nothing, it drops the continuation like `abort`.

\begin{code}
type List a = forall r. Cont [r] a
-- forall r. (a -> [r]) -> [r]

decide :: List Bool
decide = Cont (\ k -> k True ++ k False)

vanish :: forall a. List a
vanish = Cont (\ _k -> [])

runList :: List a -> [a]
runList (Cont m) = m (\ a -> [a])
\end{code}

There's a handful of variations for that one. Use `NonEmpty r` to rule out
`vanish`; generalize over an abstract monoid or semigroup `r` to prevent
inspection of the continuation; or use a `Tree r` to keep track of the order of
choices.

```haskell
type List1  a = forall r.                Cont (NonEmpty r) a
type List'  a = forall r. Monoid    r => Cont r a
type List1' a = forall r. Semigroup r => Cont r a
type Tree0  a = forall r.                Cont (Tree r) a
```

== `ContT`

There is also a continuation monad transformer, which is simply the
continuation monad with a monadic result type `m r`.
The *transformers* library defines `ContT` as a newtype mostly so that it has
the right kind to be an instance of `MonadTrans`.
All instances stay the same, so here we will prefer a type synonym to keep our
`Monad` instance count at 1.
We will refer to `ContT` and `Cont` interchangeably, as we're not too concerned
about kinds in this post, whichever looks better in context.

\begin{code}
type ContT r m a = Cont (m r) a
-- (a -> m r) -> m r
\end{code}

What does it mean that `ContT` is a monad transformer? There is a `lift`
function, which commutes with monadic operations (that's called a
*monad morphism*). For `ContT`, `lift` is simply `(>>=)`,

\begin{code}
lift :: Monad m => m a -> ContT r m a
     -- Monad m => m a -> (a -> m r) -> m r
lift u = Cont (\ k -> u >>= k)

-- Monad morphism laws:
--   lift (pure a)   =   pure a
--   lift (u >>= \ a -> k a)   =   lift u >>= \ a -> lift (k a)
\end{code}

== `CodensityT`

A closely related sibling is the ["codensity" monad
transformer](https://hackage.haskell.org/package/kan-extensions-5.2/docs/Control-Monad-Codensity.html),
where `r` is universally quantified, like it is in previous examples.
Both `ContT` and `CodensityT` can be used to optimize monads[^optim]
that have expensive *bind* `(>>=)` operations.
We won't say anything here about the actual differences between `ContT` and
`CodensityT`.

[^optim]: *Asymptotic improvement of computations over free monads*,
  by Janis Voigtländer, MPC 2008.
  ([PDF](https://www.janis-voigtlaender.eu/papers/AsymptoticImprovementOfComputationsOverFreeMonads.pdf))

\begin{code}
type CodensityT m a = forall r. Cont (m r) a
-- forall r. (a -> m r) -> m r
\end{code}

In the examples above, the types we used instead of `r` happen to be monads,
even if we did not rely on that fact. Here's a quick summary, with the names
of the resulting variant of `Cont` on the left, an equivalent definition in terms
of `CodensityT` in the middle, and their more-or-less standard counterparts on
the right as they can be found on Hackage (*base*, *transformers*, *rev-state*
and *tardis*).
The words "retracts to" mean that there is a surjective but not injective
mapping from the left to the right.

```
Done       =  CodensityT Identity    isomorphic to  Identity
Abortable  =  CodensityT Maybe         retracts to  Maybe
Except e   =  CodensityT (Either e)    retracts to  Either e
State s    =  CodensityT (Reader s)  isomorphic to  State s
Writer w   =  CodensityT (Writer w)    retracts to  Writer w, or (reverse) State w
Tardis s   =  CodensityT (State s)     retracts to  Tardis s
List       =  CodensityT []            retracts to  []
```

<!--
Interestingly, `abort = lift Nothing` for `Abortable`, `tell = lift tell` for
our version of `Writer`, but of course there is no way to lift `Reader`
operations into `get` or `put` for `State`.
-->

= Many monad transformers in one

The monad transformers corresponding to the above monads also find
their equivalent in terms of `Cont`. They are not exactly isomorphic, but
a noteworthy feature, as before, is that they still use the same old `Monad`
instance for `Cont`. Operations do rely on a `Monad` constraint for the
transformed monad `m`.

== `ListT`

Turning the previous examples into monad transformers is left as an exercise
for the reader.

Here we will focus on `List`; it is an interesting case because
a monad transformer corresponding to lists is notoriously non-obvious.
The obvious candidate `m [a]` is not a monad (unless `m` is commutative).

Curiously, we have the "monad" part down for free, and we only
need to solve "list" and "transformer".

We briefly saw earlier that we can get a "list" monad by using any monoid
instead of `[r]` as the result type. We also saw that a monadic result type
`m r` makes a monad transformer. In addition, any monad defines a monoid `m ()`
if we ignore the result (we can also use a different monoid instead of `()`
but that doesn't seem as interesting), with `pure ()` as the unit
and `(*>)` (or `(>>)`) for composition. In fact, we only need an `Applicative`
constraint for the "list" operations, but `lift` still requires `Monad`.

We already had all the ingredients to make a *list monad transformer*!

Reading the definition of `ListT` slowly, it takes a continuation
`(a -> m ())`, and produces a computation `m ()`. What can it actually do?
Mostly, call the continuation with various values of `a` in some order.

\begin{code}
type ListT m a = Cont (m ()) a
-- (a -> m ()) -> m ()

decideM :: Applicative m => ListT m Bool
decideM = Cont (\ k -> k True *> k False)

vanishM :: Applicative m => ListT m a
vanishM = Cont (\ _k -> pure ())

runListT :: Applicative m => (a -> m ()) -> ListT m a -> m ()
runListT k (Cont m) = m k
\end{code}

The list transformer is a nice pattern for deeply nested loops common
in enumeration/search algorithms.

Here are three nested `for_` loops:

\begin{code}
-- All 3 bit patterns
threebit :: IO ()
threebit =
  for_ [0, 1] $ \ i ->
  for_ [0, 1] $ \ j ->
  for_ [0, 1] $ \ k ->
  printDigits [i, j, k]

printDigits :: [Int] -> IO ()
printDigits ds = do
  for_ ds (\i -> putStr (show i))
  putStrLn ""
\end{code}

Here they are again, where each value is bound using `do` notation thanks to
the list transformer (this combination is really neat: `Cont $ for_ [ ... ]`).

\begin{code}
-- All 3 bit patterns
threebit' :: IO ()
threebit' = runListT printDigits $ do
  i <- Cont $ for_ [0, 1]
  j <- Cont $ for_ [0, 1]
  k <- Cont $ for_ [0, 1]
  pure [i, j, k]
\end{code}

Once iteration is captured in a monad, we can iterate across dimensions:

\begin{code}
-- All 8 bit patterns
eightbit :: IO ()
eightbit = runListT printDigits $
  replicateM 8 (Cont (for_ [0, 1]))

-- 00000000
-- 00000001
-- 00000010
-- 00000011
-- 00000100
-- 00000101
-- 00000110
-- ...
\end{code}

All of that is technically possible with just the list monad. The transformer
really adds the ability to interleave enumeration and computation.

\begin{code}
-- All 8 bit patterns, but show only the suffix that changed at every step.
eightbit' :: IO ()
eightbit' = runListT pure $ do
  for_ [0 .. 7] $ \ n -> do
    i <- Cont $ for_ [0, 1]
    lift $ when (i == 1) $ putStr (replicate n ' ')
    lift $ putStr (show (i :: Int))
  lift $ putStrLn ""

-- 00000000
--        1
--       10
--        1
--      100
--        1
--       10
-- ...
\end{code}

=== Other list monad transformers

This "list monad transformer" is actually different from another incarnation
which may be found on Hackage. The more common version of a "list monad
transformer" is an "effectful list", where the list constructors are
interleaved with computations.[^listt]

```haskell
newtype ListT m a = ListT (m (Maybe (a, ListT m a)))
```

[^listt]: In more than one place:
  [*logict*](https://hackage.haskell.org/package/logict),
  [*pipes*](https://hackage.haskell.org/package/pipes-4.3.12/docs/Pipes.html#t:ListT),
  [*list-t*](https://hackage.haskell.org/package/list-t),
  [*list-transformer*](https://hackage.haskell.org/package/list-transformer).
  In particular, *logict* provides a Church-encoded version of the "effectful
  list", which brings it close to the continuation transformer, but
  there's still a gap.

The biggest difference is that the "effectful list" transformer naturally
supports an *uncons* operation, which evaluates the effectful list and pauses
after producing the first element (or the empty list).

<!-- A possible implementation of *uncons* using the "continuation" transformer may be...
to first apply the continuation transformer a second time. -->

The trade-off is that *uncons* has a cost in usability.
The paused computation must be resumed explicitly: it may be dropped, or
resumed more than once.
The continuation transformer, by not allowing such "interruptions", may offer
stronger guarantees for resource management.

= Conclusion

The continuation monad can thus serve as a uniform foundation for many kinds of
monadic effects, and is even often a more efficient replacement of "standard" monads.

"Control operations" might cause some difficulties; those are operations
parameterized by computations, such as `catch` and `bracket`;
they weren't discussed here, but I think the problems can be overcome.[^local]

[^local]: For example, [there is an instance of the class `MonadReader` for
  `ContT`](https://hackage.haskell.org/package/mtl-2.2.2/docs/src/Control.Monad.Reader.Class.html#line-130),
  with a problematic operation `local :: MonadReader r m => (r -> r) -> m a -> m a`.
  It can be implemented by explicitly restoring the environment of the
  continuation following `local`.
  We also have to restrict `ContT` values under consideration to a subset of
  "well-behaved" ones. That would most likely forbid use of `callCC` or
  `shift`/`reset`, but as we've seen throughout this post, there is a lot we
  can do without those: avoiding insane control operations keeps the `Cont`
  monad *reasonable* (*cf.* the title of this post).

= See also

- Oleg Kiselyov's [page on Continuations](http://okmij.org/ftp/continuations/).
- [*The Mother of all Monads*](http://blog.sigfpe.com/2008/12/mother-of-all-monads.html),
  by Dan Piponi.
- [*The best refactoring you've never heard
  of*](http://www.pathsensitive.com/2019/07/the-best-refactoring-youve-never-heard.html)
  (aka. *Defunctionalize the continuation*),
  by James Koppel.
