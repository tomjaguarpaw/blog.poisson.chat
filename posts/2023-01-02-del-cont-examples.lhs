---
title: From delimited continuations to algebraic effects in Haskell
keywords: [haskell]
---

The upcoming version of GHC will feature primitives for
[delimited continuations][delcontprimops]. Let's put them to use and build a bare bones algebraic effect
system.

[delcontprimops]: https://github.com/ghc-proposals/ghc-proposals/blob/master/proposals/0313-delimited-continuation-primops.rst

= Algebraic effects

In Haskell, different sorts of effectful computations can be expressed using monads.
Monads for individual effects are fairly well understood. The challenge now is
to combine many different effects. Applications manage many kinds of resources
(files, network, databases...), handle many types of errors, and run in
different environments (production vs testing with mock components).
Can that be done while maintaining a reasonable level of separation of concerns?

Currently, a common approach is to use monad transformers and type classes (*mtl*-style).
But when you have a big stack of monad transformers, it may not be easy to even
understand what `(>>=)` does, because its behavior arises from the composition
of all of these transformers. So the actual control flow of the program is
opaque to us, which can be an obstacle to locating errors and guaranteeing
performance.

Algebraic effects are another approach to combine effects.
Whereas with transformers, every monad transformer must be defined from
scratch, algebraic effects start from a few core primitives: you have one
(parameterized) monad with abilities to "call" an operation and to "handle"
such calls. The hope is that those core primitives:

1. are simple to implement and to optimize;
2. make it easy to define and reason about effects,
   in terms of both behavior and performance.

Until now, algebraic effect systems in Haskell used free monads or the
continuation monad. Continuations were emulated as closures; this comes
with a level of indirection whose cost is difficult to mitigate.
The newly implemented
[delimited continuations primops][delcontprimops]
let us directly manipulate native continuations.

This post uses delimited continuations to implement programs with various effects.
The usual culprits:

- [Exceptions](#exceptions)
- [Output](#output)
- [Combining exceptions and output](#combining-exceptions-and-output)
- [Input](#input)
- [Combining input and output: streaming](#streaming)
- [Interacting with the real world](#real-world)
- [State](#state)
- [Nondeterminism](#nondeterminism)
- [Concurrency](#concurrency)

The example programs leveraging this mini effect library will look like your
standard-fare monadic code. What makes them interesting is that, operationally,
they are all in the `IO` monad. Unlike with monad transformers, adding a new
effect does not change the underlying monad, so code that doesn't use that
effect does not pay a price for it. Another notable consequence is that
"unlifting" abstractions like `UnliftIO` or `MonadBaseControl` are no longer
relevant: there is nothing to "unlift" if you never leave `IO`.

The abstraction layer of algebraic effects over continuations is so thin that I
just use `prompt` and `control0` directly, but the bits that are "operations"
and the bits that are "handlers" are clearly identifiable. The system
implemented here is untyped as far as effects are concerned, but features
named handlers as a mitigating alternative;
a complete effect system which would keep track of what operations each
computation may call and would provide safe primitives to define new effects is
left as an exercise for the reader.

This post is written in Literate Haskell ([source code][source]).
It can be compiled using the development version of GHC (or GHC 9.8 if it has been released).

[source]: https://bitbucket.org/lyxia/blog.poisson.chat/src/master/posts/2023-01-02-del-cont-examples.lhs

```
$ ghc 2023-01-02-del-cont-examples.lhs -main-is DelContExamples.main -o run-tests
$ ./run-tests
All tests passed!
```

<details class="code-details">
<summary>Extensions and imports</summary>

> {-# LANGUAGE
>   BangPatterns,
>   BlockArguments,
>   DerivingStrategies,
>   GADTs,
>   GeneralizedNewtypeDeriving,
>   MagicHash,
>   UnboxedTuples #-}
> module DelContExamples where
> 
> import qualified Control.Exception as E
> import Control.Exception.Base (NoMatchingContinuationPrompt(..))
> import Data.Either
> import Data.Foldable (for_)
> import Data.Functor (void)
> import Data.Functor.Sum (Sum(..))
> import Data.Maybe (fromMaybe, maybe)
> import System.IO.Unsafe
> import System.Environment
> import GHC.Exts (PromptTag#, newPromptTag#, prompt#, control0#)
> import GHC.IO (IO(..))
> import GHC.Stack (HasCallStack)
> import Prelude hiding (log)

</details>

= The mother of all monads

Capturing continuations is the power of the continuation monad,
in which we can embed all other monads. It's
[the mother of all monads.](http://blog.sigfpe.com/2008/12/mother-of-all-monads.html)

`Mom` is defined identically to `IO`, but its only operations are the new
delimited continuation primitives.

> newtype Mom a = Mom (IO a)
>   deriving newtype (Functor, Applicative, Monad)

The available operations wrap the RTS primitives `newPromptTag#`,
`prompt#` and `control0#`.

> -- Unsafe primitives
>
> data PromptTag a = PromptTag (PromptTag# a)
> 
> newPromptTag :: Mom (PromptTag a)
> newPromptTag = Mom (IO (\s -> case newPromptTag# s of
>   (# s', tag #) -> (# s', PromptTag tag #)))
>
> prompt :: PromptTag a -> Mom a -> Mom a
> prompt (PromptTag tag) (Mom (IO m)) = Mom (IO (prompt# tag m))
> 
> control0 :: PromptTag a -> ((Mom b -> Mom a) -> Mom a) -> Mom b
> control0 (PromptTag tag) f =
>   Mom (IO (control0# tag (\k -> case f (\(Mom (IO a)) -> Mom (IO (k a))) of Mom (IO b) -> b)))

The boxing of the continuation `k` in `control0` could be avoided by
introducing a new type for continuations, replacing `(Mom b -> Mom a)`.
I'm not sure whether there is much to gain from that optimization.
I leave it like this for simplicity.

== `prompt` and `control0`, "goto" with extra steps?

When a function terminates normally, it returns its result to its caller,
its predecessor in the call stack. `prompt` lets you prepare another return point
earlier in the call stack, and `control0` returns to that point. What happens
to all the stack frames that were skipped that way? They are copied to the heap so they
can be restored later.

In more concrete terms, when you call `control0 t f :: Mom b`, the caller expects a
result of some type `b`. It is assumed that you have previously set up a
`prompt t :: Mom a -> Mom a` in the call stack with the same tag `t :: PromptTag a`.
The slice of the stack up to that `prompt t` is unwinded and stored as a function
`continue :: Mom b -> Mom a` (`IO b -> IO a`).
`prompt t` is popped off the stack, and the program carries on as `f continue`.

It sounds completely insane the first time you learn about it,
it's like "goto" with extra steps. And yet, when you get down to it, delimited
continuations have rather clean semantics, both operationally and
denotationally.
The implementation was a surprisingly small change in GHC.

<blockquote>
The changes required to implement `prompt#` and `control0#` are relatively minimal.
They only impact the RTS, and they do not require any changes to existing
functionality. Though capturing portions of the RTS stack may seem like a
radical proposition, GHC actually already does it when raising an asynchronous
exception to avoid the need to duplicate work for any blackholed thunks. In
fact, getting that right is significantly more subtle than implementing
`control0#`, which is quite straightforward in comparison.

--- [The GHC Proposal][delcontprimops]
</blockquote>

The richness of continuations, both theoretically and practically, suggests that these
control operators are not as arbitrary as they seem.

== Effectful code, pure semantics

The code in this post can be split in two levels. Library-level code uses the delimited
continuation primitives to implement effects---operations and handlers, and user-level
code uses those effects in example programs.
Without direct access to delimited continuations, user-level code cannot
observe any mutation, so it will be safe to use the following pure `run`
function.

> -- Look Ma', no IO!
> run :: Mom a -> Maybe a
> run (Mom m) = unsafePerformIO
>   (E.catch (Just <$> m) \NoMatchingContinuationPrompt -> pure Nothing)

Hiding the delimited continuations primitives avoids the danger of duplicating
and observing the creation of fresh `PromptTag`s in a pure context.
Some partiality remains (`Maybe`) due to potentially mismatched
`control0#` calls. Such errors would be prevented by a type system for effects,
which is beyond the scope of this post.

== Further reading

On `prompt#`, `control0#`, and `newPromptTag#`:

- [The GHC proposal: Delimited continuations primops;][delcontprimops]
- [Comment by @tomjaguarpaw in the discussion of the GHC proposal](https://github.com/ghc-proposals/ghc-proposals/pull/313#issuecomment-590075484) illustrating the semantics of the primops;
- [Gist by @lexi-lambda](https://gist.github.com/lexi-lambda/d97b8187a9b63619af29689e9fa1b880) with
  background on reduction semantics and continuations;
- [*A Monadic Framework for Delimited Continuations*](https://legacy.cs.indiana.edu/~dyb/pubs/monadicDC.pdf) by Kent Dybvig, Simon Peyton Jones, and Amr Sabry (JFP 2007).
- [The patch implementing the proposal](https://gitlab.haskell.org/ghc/ghc/-/merge_requests/7942).

On the continuation monad:

- [The reasonable effectiveness of the continuation monad.](https://blog.poisson.chat/posts/2019-10-26-reasonable-continuations.html)
- [The essence of functional programming](https://dl.acm.org/doi/10.1145/143165.143169),
  by Philip Wadler (POPL 1992).

= Exceptions

To begin, let's implement exceptions using delimited continuations.
This effect has an operation `throw` and a handler `catch`.

== Operation

We first declare the uninterpreted operation `Throw` as a constructor
in a functor. The parameter `a` is ignored by exceptions; it will be
used by other effects.

> data Exception e a
>   = Throw e

We wrap this constructor in a user-facing function `throw`.
Every `throw` should have a matching `catch`, and we ensure this
by requiring a `tag` that identifies the corresponding `catch`.
The exact type of `tag` will be revealed in a moment.
`control0` uses that `tag` to look up the matching `catch` in the call stack,
and returns to it with the exception `e` wrapped in `Throw`.
The underscore is the continuation, which is the slice of the stack below the
`catch`, which is thus discarded.

> throw :: Exception e % r -> e -> Mom a
> throw tag e = control0 tag \_ -> pure (Op (Throw e))

== Handler

The type of `catch` should also look familiar, with the novelty that the
handled computation `f` expects a tag---so that it may call `throw`.
In `catch f onThrow`, a fresh `tag` is generated, then
`f tag` either returns normally, then its result is wrapped in `Pure a`,
or `f tag` `throw`s an exception wrapped in `Op (Throw e)`.
We then return the result or apply the handler `onThrow` accordingly.

> catch :: (Exception e % a -> Mom a) -> (e -> Mom a) -> Mom a
> catch f onThrow = do
>   tag <- newPromptTag
>   handle tag (f tag)
>  where
>   handle tag action = do
>     next <- prompt tag (Pure <$> action)
>     case next of
>       Op (Throw e) -> onThrow e
>       Pure a -> pure a

You might have guessed that the `Exception e % a` tag is just a `PromptTag`.
More surprisingly, the tag index involves a free monad.
For exceptions, `Free (Exception e) a` is equivalent to `Either e a`:
we expect the computation under `prompt` to produce either an exception `e` or
a result `a`. More generally, for an effect expressed as a functor `f`,
things will be set up exactly so that handlers will be matching on a
computation/tree of type `Free f r`.

> type f % r = PromptTag (Free f r)
>
> data Free f r
>   = Op (f (Free f r))
>   | Pure r

Using `catch`, we can implement `try`.

> try :: (Exception e % Either e a -> Mom a) -> Mom (Either e a)
> try f = catch (\tag -> Right <$> f tag) (\e -> pure (Left e))

The explicit tags serve as a form of *capabilities*, handles that functions
take as explicit arguments, granting the permission to use the associated
effects. This partly makes up for the lack of effect typing.
It's not watertight: you can easily capture the tag to call `throw` outside of
`try`/`catch`. But from a non-adversarial perspective, this mechanism may
prevent quite a few mistakes.

== Test

> testThrow :: IO ()
> testThrow = do
>   assert (isRight' (run (try (\_ -> pure "Result"))))
>   assert (isLeft'  (run (try (\exc -> throw exc "Error"))))
>  where
>   isRight' = maybe False isRight
>   isLeft' = maybe False isLeft

> -- Minimalistic unit testing framework
> assert :: HasCallStack => Bool -> IO ()
> assert True = pure ()
> assert False = error "Assertion failed"

= Output

Algebraic effects are also known as "resumable exceptions", extending
exceptions with the ability to continue the computation right where
the exception was thrown.

The next simplest effect after exceptions is to produce some output.
Like `Throw`, we represent the `Output` operation as a constructor,
containing the value to output, and now also a continuation.

== Operation

> data Out o a
>   = Output o (Mom () -> Mom a) 

The `output` wrapper is similar to `throw`, additionally storing the
continuation in the `Output` constructor.
The expected argument of the continuation `continue` is a computation which is
to replace the operation call.
When we call `output o :: Mom ()`, that call "bubbles
up" like an exception, gets caught by a handler, and the call gets replaced by
`pure ()` or some other `Mom ()` computation.

> output :: Out o % r -> o -> Mom ()
> output tag o = control0 tag \continue -> pure (Op (Output o continue))

A synonym specialized to strings.

> log :: Out String % r -> String -> Mom ()
> log = output

== Example

An infinite output stream of the Fibonacci sequence.

> fibonacci :: Out Int % r -> Mom a
> fibonacci out = fib 0 1
>   where
>     fib !a !b = do
>       output out a
>       fib b (a + b)

== Handler

Run a computation lazily and collect its output in a list.

> collect :: (Out o % () -> Mom ()) -> [o]
> collect f = runList do
>   tag <- newPromptTag
>   handle tag (Pure <$> f tag)
>  where
>   handle tag action = do
>     next <- prompt tag action
>     case next of
>       Op (Output o continue) ->
>         pure (o : runList (handle tag (continue (pure ()))))
>       Pure () -> pure []
>   runList = fromMaybe [] . run

== Test

> testFibonacci :: IO ()
> testFibonacci =
>   assert (take 8 (collect fibonacci)
>           == [0, 1, 1, 2, 3, 5, 8, 13])

= Combining exceptions and output

== Example

The big selling point of algebraic effects is that effects can be
combined smoothly. We can thus use `log` to trace the
execution flow of a program using `throw` and `catch`
without further ceremony.

This looks like your usual monadic program. The point is that everything lives
in the same monad `Mom` (which is operationally equal to `IO`),
so you do not have to worry about "lifting" or "unlifting" anything through a
transformer: the semantics of `(>>=)` do not change with every new effect, and
there isn't the problem that "lifting" `catch` and other operations that are
actually handlers is counter-intuitive for many transformers, if possible at all.
To be fair, there remain
[difficulties](https://github.com/hasura/eff/issues/12) in this area even with
algebraic effects.

> tracedCatch :: Out String % r -> Mom Bool
> tracedCatch out = catch this onThrow 
>  where
>   this exc = do
>     log out "Start"
>     _ <- throw exc "Boom"
>     log out "This is unreachable"
>     pure False
>   onThrow msg = do
>     log out ("Error: " ++ msg)
>     pure True

== Test

> testTracedCatch :: IO ()
> testTracedCatch =
>   assert (collect (void . tracedCatch) ==
>     [ "Start"
>     , "Error: Boom" ])

== Silent handler

There can also be different ways of handling an effect.
The following handler discards output instead of collecting it,
for example to ignore debugging logs.

> discardOutput :: (Out o % a -> Mom a) -> Mom a
> discardOutput f = do
>   tag <- newPromptTag
>   handle tag (Pure <$> f tag)
>  where
>   handle tag action = do
>     next <- prompt tag action
>     case next of
>       Op (Output _o continue) -> handle tag (continue (pure ()))
>       Pure a -> pure a

> testDiscard :: IO ()
> testDiscard =
>   assert (run (discardOutput tracedCatch) == Just True)

= Input

Dually, there is an effect to request some input.

== Operation

> data In i a
>   = Input (Mom i -> Mom a) 

The `input` call is expected to return a result `i`. As before, the type of the
`input _` operation must coincide with the domain `Mom i` of the continuation.

> input :: In i % r -> Mom i
> input tag = control0 tag \continue -> pure (Op (Input continue))

== Example

Output the cumulative sum of an input stream.
Like `fibonacci`, this is an infinite loop in `IO`.
It gets broken by `control0` in `input`.
Until now, an infinite loop in `IO` would either have to be broken by an
exception (which makes it not actually infinite), or have to involve
concurrency.

> csum :: In Int % r -> Out Int % r -> Mom a
> csum inp out = go 0
>   where
>     go !acc = do
>       n <- input inp
>       let acc' = acc + n
>       output out acc'
>       go acc'

== Handler

Supply a list of inputs and stop when we run out.

> listInput :: [i] -> (In i % a -> Mom a) -> Mom (Maybe a)
> listInput is f = do
>   tag <- newPromptTag
>   catch (\exc -> handle exc tag is (Pure <$> f tag))
>     (\() -> pure Nothing)
>  where
>   handle exc tag is action = do
>     next <- prompt tag action
>     case next of
>       Op (Input continue)
>         | i : is' <- is -> handle exc tag is' (continue (pure i))
>         | otherwise -> handle exc tag [] (continue (throw exc ()))
>       Pure a -> pure (Just a)

== Test

> testCsum :: IO ()
> testCsum =
>   assert ((collect \out ->
>            void $ listInput [1 .. 5] \inp ->
>            csum inp out
>           ) == [1, 3, 6, 10, 15])

= Combining input and output: streaming {#streaming}

The input and output effect can be combined in a streaming fashion,
alternating execution between the consumer and the producer.

== Handler

Feed the output of one computation into the input of the other.
Terminate whenever one side terminates, discarding the other.

> connect :: (Out x % a -> Mom a) -> (In x % a -> Mom a) -> Mom a
> connect producer consumer = do
>   out <- newPromptTag
>   inp <- newPromptTag
>   handleI out inp (Pure <$> producer out) (Pure <$> consumer inp)
>  where
>   handleI out inp produce consume = do
>     next <- prompt inp consume
>     case next of
>       Op (Input continue) -> handleO out inp produce continue
>       Pure a -> pure a
>   handleO out inp produce consuming = do
>     next <- prompt out produce
>     case next of
>       Op (Output o continue) ->
>         handleI out inp (continue (pure ())) (consuming (pure o))
>       Pure a -> pure a

== Test

Connect two copies of the cumulative sum process: compute the cumulative sum
of the cumulative sum.

> csum2 :: In Int % () -> Out Int % () -> Mom ()
> csum2 inp out = connect (\out' -> csum inp out') (\inp' -> csum inp' out)

> testConnect :: IO ()
> testConnect =
>   assert ((collect \out ->
>            void $ listInput [1 .. 5] \inp ->
>            csum2 inp out
>           ) == [1, 4, 10, 20, 35])

= Interacting with the real world {#real-world}

What sets `IO` apart from `ST` and `Mom` is that it can change the world.
We can define handlers to send output and receive input from the real world.
The result of these handlers must be in `IO`.

== Printing output

Text output can be printed to `stdout`.

> printOutput :: (Out String % () -> Mom ()) -> IO ()
> printOutput f = momToIO do
>   tag <- newPromptTag
>   handle tag (Pure <$> f tag)
>  where
>   handle tag action = do
>     next <- prompt tag action
>     case next of
>       Op (Output o continue) -> pure do
>         putStrLn o
>         momToIO (handle tag (continue (pure ())))
>       Pure () -> pure (pure ())
>   momToIO = fromMaybe (pure ()) . run

== Reading input

We can forward input from `stdin` into a
consumer computation.

> readInput :: (In String % () -> Mom ()) -> IO ()
> readInput f = momToIO do
>   tag <- newPromptTag
>   handle tag (Pure <$> f tag)
>  where
>   handle tag action = do
>     next <- prompt tag action
>     case next of
>       Op (Input continue) -> pure do
>         i <- getLine
>         momToIO (handle tag (continue (pure i)))
>       Pure () -> pure (pure ())
>   momToIO = fromMaybe (pure ()) . run

A drawback of this implementation is that for a computation that features both
input and output, these handlers are awkward to compose.
We can coerce `IO` to `Mom` so `readInput` can be composed with `printOutput`,
but that is a hacky solution that makes the type `Mom` a lie (it's not supposed
to have side effects). A better solution may be to combine effects before
interpreting them in `IO` all at once.

= State

No effect tutorial would be complete without the state effect.

== Operations

> data State s a
>   = Get (Mom s -> Mom a)
>   | Put s (Mom () -> Mom a)

> get :: State s % r -> Mom s
> get tag = control0 tag \continue -> pure (Op (Get continue))
> 
> put :: State s % r -> s -> Mom ()
> put tag s = control0 tag \continue -> pure (Op (Put s continue))

== Handler

State-passing, no mutation.

> runState :: s -> (State s % a -> Mom a) -> Mom (s, a)
> runState s0 f = do
>   tag <- newPromptTag
>   handle tag s0 (Pure <$> f tag)
>  where
>   handle tag s action = do
>     next <- prompt tag action
>     case next of
>       Op (Get continue) -> handle tag s (continue (pure s))
>       Op (Put s' continue) -> handle tag s' (continue (pure ()))
>       Pure a -> pure (s, a)

== Example

> incr :: State Int % r -> Mom ()
> incr st = do
>   n <- get st
>   put st (n + 1)

Again, combining state with logging is effortless, because
effects live in the same underlying monad.

> logState :: Out String % r -> State Int % s -> Mom ()
> logState out st = do
>   n <- get st
>   log out (show n)

> incr2 :: Out String % r -> State Int % s -> Mom ()
> incr2 out st = do
>   incr st
>   logState out st
>   incr st
>   logState out st

== Test

> testState :: IO ()
> testState = do
>   assert ((collect \out -> runState 0 (incr2 out) *> pure ()) == ["1", "2"])
>   assert (run (discardOutput \out -> runState 0 (incr2 out)) == Just (2, ()))

= Nondeterminism

The examples above are quite sequential in nature.
`Mom` can also replace the list monad.

== Operation

Choose one element in a list.

> data Nondet a where
>   Choose :: [x] -> (Mom x -> Mom a) -> Nondet a

> choose :: Nondet % r -> [x] -> Mom x
> choose tag xs = control0 tag \continue -> pure (Op (Choose xs continue))

== Example

> nameTheorems :: Nondet % r -> Mom String
> nameTheorems nd = do
>   name1 <- choose nd ["Church", "Curry"]
>   name2 <- choose nd ["Turing", "Howard"]
>   result <- choose nd ["thesis", "isomorphism"]
>   pure (name1 ++ "-" ++ name2 ++ " " ++ result)

== Handler

Use the output effect to stream all results of a nondeterministic computation.
Here, the continuation is not used linearly: it is called once for every
element in the given list.

> enumerate :: (Nondet % a -> Mom a) -> Out a % r -> Mom ()
> enumerate f out = do
>   tag <- newPromptTag
>   handle tag (Pure <$> f tag)
>  where
>   handle tag action = do
>     next <- prompt tag action
>     case next of
>       Op (Choose xs continue) -> for_ xs (handle tag . continue . pure)
>       Pure a -> output out a

== Test

> testEnumerate :: IO ()
> testEnumerate = do
>   assert (collect (enumerate nameTheorems) ==
>     [ "Church-Turing thesis"
>     , "Church-Turing isomorphism"
>     , "Church-Howard thesis"
>     , "Church-Howard isomorphism"
>     , "Curry-Turing thesis"
>     , "Curry-Turing isomorphism"
>     , "Curry-Howard thesis"
>     , "Curry-Howard isomorphism"
>     ])

= Concurrency

Earlier, the streaming handler `connect` interleaved execution of one consumer
and one producer thread. Here is a cooperative concurrency effect that lets us
dynamically fork any number of threads and interleave them.

== Operations

> data Conc a
>   = Fork (Mom ()) (Mom () -> Mom a)
>   | Yield (Mom () -> Mom a)

Fork a thread to run the given computation.

> fork :: Conc % r -> Mom () -> Mom ()
> fork tag thread = control0 tag \continue -> pure (Op (Fork thread continue))

Cooperative concurrency: threads must yield explicitly.

> yield :: Conc % r -> Mom ()
> yield tag = control0 tag \continue -> pure (Op (Yield continue))

== Example

A thread that repeats an output value three times.

> simpleThread :: Out String % r -> Conc % s -> Int -> Mom ()
> simpleThread out conc n = do
>   log out (show n)
>   yield conc
>   log out (show n)
>   yield conc
>   log out (show n)
>   yield conc

Interleave `111`, `222`, `333`.

> interleave123 :: Out String % r -> Conc % s -> Mom ()
> interleave123 out conc = do
>   fork conc (simpleThread out conc 1)
>   fork conc (simpleThread out conc 2)
>   fork conc (simpleThread out conc 3)

== Handler

A round-robin scheduler. `handle` keeps track of a queue of threads.
It runs the first thread until the next event. If the thread yields,
its continuation is pushed to the end of the queue. If the thread
forks another thread, the forked thread is pushed to the end of the queue,
and we continue in the main thread (forking does not yield).
If the thread terminates, we remove it from the queue.

> runConc :: (Conc % () -> Mom ()) -> Mom ()
> runConc f = do
>   tag <- newPromptTag
>   handle tag [Pure <$> f tag]
>  where
>   handle tag [] = pure ()
>   handle tag (thread : threads) = do
>     next <- prompt tag thread
>     case next of
>       Op (Yield continue) -> handle tag (threads ++ [continue (pure ())])
>       Op (Fork th continue) -> handle tag (continue (pure ()) : threads ++ [Pure <$> th])
>       Pure () -> handle tag threads

== Test

> testInterleave :: IO ()
> testInterleave =
>   assert ((collect \out -> runConc \conc -> interleave123 out conc)
>           == ["1", "2", "3", "1", "2", "3", "1", "2", "3"])

= Conclusion

Primitive delimited continuation in Haskell give us the power to jump around
the stack to implement many kinds of effects. Under the hood, those operations
live in the IO monad, grounding effectful code in a familiar execution model. 

For those new to the topic, I hope that these examples may serve as a good
starting point to experiment with delimited continuations and algebraic effects
in Haskell.

The system implemented here is as rudimentary as it gets.
To define new effects and handlers, we use the new primitives directly, which
is dangerous. This was deliberate to provide material to familiarize oneself
with those primitives.
Moreover, on the one hand, a type system to keep track of the scope of
delimited continuations is a non-trivial ask. On the other hand, the examples
here all follow a regular structure, so there is probably a way to encapsulate
the primitives, trading off some expressiveness for a safe interface
to define new effects and handlers.

Named handlers---via prompt tags---occupy an interesting spot in the scale of
safety guarantees. It is imperfect, even very easy to circumvent. But if you're
not working against it, it is still a neat way to prevent simple mistakes.
This system can be reinforced further using rank-2 polymorphism,
a technique described in:

- [*First-Class Names for Effect Handlers*](https://dl.acm.org/doi/10.1145/3563289),
  Ningning Xie, Youyou Cong, Kazuki Ikemori, Daan Leijen (OOPSLA 2022).

Interestingly, prompt tags were not part of the original proposal, and
they are not used by [*eff*](https://github.com/lexi-lambda/eff), the effect
system which gave rise to Alexis King's GHC proposal. Prompt tags were added during
the feedback process to make the primitives type-safe by default.

Now is an exciting time for algebraic effects/delimited continuations,
as they are making their way into industrial languages:
[Haskell][delcontprimops],
[OCaml](https://discuss.ocaml.org/t/ocaml-5-0-0-is-out/10974),
[WebAssembly](https://wasmfx.dev/).

---

= All of this is executable

> main :: IO ()
> main = do
>   testThrow
>   testFibonacci
>   testTracedCatch
>   testDiscard
>   testCsum
>   testConnect
>   testState
>   testEnumerate
>   testInterleave
>   putStrLn "All tests passed"
