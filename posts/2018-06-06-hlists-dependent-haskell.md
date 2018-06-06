---
title: Heterogeneous lists with dependent types in Haskell
---

With the help of GHC's many extensions, we can encode simple forms of dependent
types, allowing us to enforce more expressive invariants in our programs at
compile time.

In this post, I will walk you through an implementation of heterogeneous lists
to demonstrate the features and techniques commonly associated with the current
flavor of "dependent Haskell".

My Literate Haskell blog posts render the whole
[source](https://bitbucket.org/lyxia/blog.poisson.chat/src?at=master),
including the extensions.
In this post, I will mention most of them when they are used, and explain them
a bit.

\begin{code}
{-# LANGUAGE
    AllowAmbiguousTypes,
    ConstraintKinds,
    DataKinds,
    FlexibleContexts,
    FlexibleInstances,
    GADTs,
    InstanceSigs,
    MultiParamTypeClasses,
    PolyKinds,
    RankNTypes,
    ScopedTypeVariables,
    TypeApplications,
    TypeFamilies,
    TypeOperators,
    UndecidableInstances #-}

module HLists where
\end{code}

As for those that won't be mentioned later, let's take care of them now briefly.

- `InstanceSigs` allows type signatures to appear in instance declarations, so
  that we don't need to go back to the type class to remember what is being
  defined.
  This is also consistent with the common practice of annotating all toplevel
  bindings.

- `ConstraintKinds`, `FlexibleContexts`, `FlexibleInstances`,
  `ScopedTypeVariables` and `UndecidableInstances` lift restrictions
  that are mostly historical.
  They are quite benign extensions that might be unnoticeable when enabled if
  you don't already know about them.

The GHC user guide also documents
[all the available extensions](https://downloads.haskell.org/~ghc/latest/docs/html/users_guide/lang.html).


A type for heterogeneous lists
==============================

We will construct lists using the infix pair type below as a cons, and the unit
type `()` as a nil.
The infix type constructor `(:*)` is allowed by the `TypeOperators` extension
(not to be confused with the identically-named data constructor `(:*)`,
which is allowed by the standard).

\begin{code}
data a :* b = a :* b deriving Show

infixr 1 :*
\end{code}

Another common candidate for heterogeneous lists is a GADT indexed by a list of
types, but I prefer `(:*)` for its simplicity.

Here is an example of a list of three elements:

\begin{code}
hlistExample1 :: Int :* String :* String :* ()
hlistExample1 =  1   :* "One"  :* "1"    :* ()
\end{code}

You might wonder, why even have a nil, since there can be any type to the right
of `(:*)`? This is clearly shorter:

\begin{code}
hlistExample2 :: Int :* String :* String
hlistExample2 =  1   :* "One"  :* "1"
\end{code}

The problem is that it introduces an odd corner case, where the last element of
a list can never be a heterogeneous list, since `(:*)` will be interpreted as a
tail of the list.
Is the above list a list of three elements, or is it a list of two (one `Int`
and one `String :* String`)?

Such a choice would be reflected in the rest of the implementation as an
unnecessary complication compared to having lists be clearly terminated by
`()`.

Hence, it is possible to accidentally construct these ill-formed lists, but
something will break at compile time anyway, so that's okay.

Task: get an element by type
============================

We will implement a function to extract an element of a given type in the list.
It is declared as part of the following two-parameter type class.
This requires the `MultiParamTypeClasses` extension.

\begin{code}
class Get a bs where
  get :: bs -> a
\end{code}

For example, we can get the string out of this triple as follows:

\begin{code}
getExample1 :: String
getExample1 =
  get @String ((1 :: Int) :* "One" :* "1" :* ())
-- "One"
\end{code}

In the simple examples of this post, we can always infer the output type of
`get` from the context where it is applied.
But in general, an explicit annotation will often be necessary, and that is
nicely done with the `TypeApplications` extension as shown in the above example.
`get` has two type arguments, in the order of the type class arguments.[^mptcta]
Here we explicitly apply it to its first type argument, which is the type
of the element we want to extract.

[^mptcta]: I don't know whether they can be reordered without changing the
  order of the class arguments.

We'll go through three progressively more elaborate implementations for `Get`.
To avoid conflicts between these attempts, we will declare a new copy of that
class at the beginning of each section.

Conventional approach
---------------------

\begin{code}
class Get0 a bs where
  get0 :: bs -> a
\end{code}

The simplest solution is to write two overlapping instances.
First, when the type of the head of the list doesn't match, we keep looking in
the tail, calling `get0` recursively.

\begin{code}
instance Get0 a bs => Get0 a (b :* bs) where
  get0 :: (b :* bs) -> a
  get0 (_ :* ys) = (get0 :: bs -> a) ys
\end{code}

Second, when the types match, we return the head of the list.

\begin{code}
instance {-# OVERLAPPING #-} Get0 a (a :* bs) where
  get0 :: (a :* bs) -> a
  get0 (x :* _) = x
\end{code}

By default, overlapping instances are forbidden: often enough, they are caused
by a mistake.
We indicate that the overlap is intentional using the `OVERLAPPING` pragma on
the *more specific* instance.[^overlap]
The instance `(Get0 a (a :* bs))` is more specific than `(Get0 a (b :* bs))`
because we can substitute variables in the latter to obtain the former: replace
`b` with `a`.

[^overlap]: There are two more variants, `OVERLAPPABLE` and `OVERLAPS`.
  You can read more about them in the
  [GHC user guide](https://downloads.haskell.org/~ghc/latest/docs/html/users_guide/glasgow_exts.html#overlapping-instances).

Before going in more details, let's give this implementation a try.
We can reproduce the above example successfully:

\begin{code}
get0Example1 :: String
get0Example1 =
  get0 @String ((1 :: Int) :* "One" :* "1" :* ())
-- "One"
\end{code}

What about this more abstract operation: get the third element of any
sufficiently long list.

```haskell
getThird0 :: (a :* b :* c :* ds) -> c
getThird0 = get0
-- Type error!
```

The constraint solver gets stuck on solving `Get0 c (a :* b :* c :* ds)`
because it cannot determine whether `a` is equal to `c`,
so it can't choose one of the above instances.

If instances are allowed to overlap, which instance should it select?
I won't go into the rationale here, but the rule is to always prefer the most
specific instance, and only pick a less specific one when there is no way to
instantiate type variables in the environment to make the other more specific
instance(s) match.
In this case, since `a` can be made equal to `c`, the `OVERLAPPING` instance
can still potentially match, hence the error.

The GHC user guide actually has
[a section on overlapping instances](https://downloads.haskell.org/~ghc/latest/docs/html/users_guide/glasgow_exts.html#overlapping-instances)
which is a pretty good reference about this algorithm if you can get past the
jargon.

One way out is to add the unresolved constraint to the signature of
`getThird0`, and let it be resolved at use sites with concrete types.

\begin{code}
getThird0
  :: Get0 c (a :* b :* c :* ds)
  => (a :* b :* c :* ds)
  -> c
getThird0 = get0
\end{code}

However, if `c` is equal to `a` or `b`, this function won't be doing what its
name and type advertise!

\begin{code}
-- a, b, c all equal to String, ds ~ (String :* ())
get0Example2 :: String
get0Example2 =
  getThird0 ("One" :* "Two" :* "Three" :* "Four" :* ())
-- "One"
-- We would like "Three"
\end{code}

This problem is of the kind that has many solutions, and the best one would really
depend on the purpose of this `get` function.
But the one I want to share here is to write the constraint that `c` is not
equal to `a` or `b`. This makes the type of `getThird` less general to allow
the `Get` constraint above to be solved at the definition of `getThird`.

Type disequality constraints
----------------------------

\begin{code}
class Get1 a bs where
  get1 :: bs -> a
\end{code}

Immediately, we face an obstacle: there is an equality constraint `(~)`, but no
primitive disequality constraint "`(/~)`", or any general way to negate a
constraint (such a thing would be incompatible with the open-world principle
of type classes).

Fortunately, we can define equality differently: as a boolean-valued
closed `TypeFamily`.
(Are we playing language extensions bingo?)

The type-level function `(==)` has two clauses, it is equal to `True` if the
operands are equal, `False` otherwise.

\begin{code}
type family a == b :: Bool where
  a == a = 'True
  a == b = 'False
\end{code}

Note that type families allow *nonlinear pattern-matching*: the first clause
matches twice on the same variable. This is not allowed at the value level,
because there is no universal way of comparing values, especially
infinite values, functions, and values of abstract types such as `IO`.[^1]
But at the type level, it is possible.

[^1]: We could imagine using an `Eq` constraint to implement nonlinear
  pattern-matching; I haven't really considered the implications.

Data constructors such as `True` and `False` are allowed at (or *promoted to*)
the type level by the `DataKinds` extension.
They are disambiguated from type constructors using the single-quote prefix,
since they can use the same names even in a single module.
`DataKinds` is the kind[^heh] of extension that is so intuitive one doesn't
even notice they're using.

[^heh]: The fact that "type", "kind" and "sort" are commonly used in this area
  of programming languages makes it sometimes difficult to talk about things.

Now we can match on the outcome of that comparison operation.
The constraint `'False ~ (a == b)` holds if and only if `a` and `b` are not
equal. Conversely, one could also write `'True ~ (a == b)` in the case of an
equality, but the more common `a ~ b` works as well, if not better.[^2]
Note that `a ~ b` implies `'True ~ (a == b)`, but the type checker is
not aware of the converse! From the type checker's point of view, `(==)` is a
type-level function like any other, and it doesn't make any particular effort
to reason about its output.

[^2]: That type family is also defined in `base`:
  [`Data.Type.Equality.(==)`](https://hackage.haskell.org/package/base-4.11.1.0/docs/Data-Type-Equality.html).
  However, its definition has recently changed (since `base 4.11`, i.e., GHC
  8.4). I don't like that it is not reflexive anymore, but I haven't gathered
  any concrete data about the pros and cons yet.
  ([Previous version](https://hackage.haskell.org/package/base-4.10.1.0/docs/Data-Type-Equality.html#t:-61--61-),
  [changelog](https://hackage.haskell.org/package/base-4.11.1.0/changelog)
  (Ctrl-F "Equality").)

We introduce a new type class `GetIf`, with one more parameter to carry the
comparison result.
The superclass constraint is a minor safety net, ensuring there's only one way
to use that type class: we must set the boolean `aeqb` to `a == b`,
and instances must also satisfy that constraint.

\begin{code}
class (aeqb ~ (a == b)) => GetIf aeqb a b bs where
  getIf :: (b :* bs) -> a
\end{code}

We have two cases, depending on the value of the boolean `aeqb`.
Either `a` is equal to `b`, then we get the head of the list.

\begin{code}
instance (a ~ b) => GetIf 'True a b bs where
  getIf :: (a :* bs) -> a
  getIf (x :* _) = x
\end{code}

Or `a` is not equal to `b`, then we keep looking in the tail. Since instances
must satisfy their superclass constraints, we must add `'False ~ (a == b)`.

\begin{code}
instance ('False ~ (a == b), Get1 a bs)
  => GetIf 'False a b bs where
  getIf :: (b :* bs) -> a
  getIf (_ :* ys) = get1 ys
\end{code}

Finally, `Get1` and `GetIf` are connected by this instance of `Get1`
which immediately defers to `GetIf`.

\begin{code}
instance GetIf (a == b) a b bs => Get1 a (b :* bs) where
  get1 = getIf
\end{code}

The main benefit of this technique over the previous one is that it avoids
overlapping instances, which can be difficult to understand.
The overlap still exists, as part of the definition of `(==)`, but that is
contained in a general and reusable construct, and the rule of matching clauses
sequentially for closed type families may be more intuitive.[^3]

[^3]: It's a bit more complex than that in general, for example
  [`Data.Type.Bool`](https://hackage.haskell.org/package/base-4.11.1.0/docs/Data-Type-Bool.html)
  defines the type-level boolean `(&&)` and `(||)` in a way that simplifies
  ideally: `True && a = a = a && True`.

For clarity, we can define a "class synonym" for type disequality.
For constraints, the advantage of this method over type synonyms is that
type synonyms can't be partially applied, while "class synonyms" can.

\begin{code}
class    ('False ~ (a == b)) => a /~ b
instance ('False ~ (a == b)) => a /~ b
\end{code}

We can thus give `getThird` the following type, ensuring that the `c` we
get is indeed the third element in the list.

\begin{code}
getThird1 :: (c /~ a, c /~ b) => (a :* b :* c :* ds) -> c
getThird1 = get1
\end{code}

Now using `getThird1` with types for the first or second element equal to the third
results in a type error.
Whether that is good or bad depends on what you actually want to do with those
heterogeneous lists.

```haskell
getThird1Example :: String
getThird1Example =
  getThird1 @String ("One" :* "Two" :* "Three" :* "Four" :* ())
-- Type error!
```

Type-level conditionals
-----------------------

One last issue to address about that solution is that it is quite cumbersome
to implement.
We have to define a new type class, and the original class does nothing but
call the new one immediately.
Conceptually, all that work is only to match on a boolean, one of the simplest
data types (or, data kinds?).
We'd like a similarly simple abstraction to do that.
How about `if`? We can certainly make it a type family[^4]:

[^4]: [`Data.Type.Bool.If`](https://hackage.haskell.org/package/base-4.11.1.0/docs/Data-Type-Bool.html#t:If)
  in `base`.

\begin{code}
type family If (b :: Bool) (c :: k) (d :: k) :: k where
  If 'True  c _ = c
  If 'False _ d = d
\end{code}

This family is polykinded, which is just another name for polymorphism, just
for type-level constructs: `If :: forall k. Bool -> k -> k -> k`.
(`PolyKinds` extension; kinds are to types as types are to terms.)

It will take a bit of setup to be able to use `If`, so let's put it aside for
the moment.

We also need a type class to pattern match on the type-level boolean and decide
what to do *at run time*, as opposed to type families, which only live
at compile time.

Here's a first attempt.

\begin{code}
class IsBool0 b where
  _If0 :: forall r. r -> r -> r

instance IsBool0 'True where
  _If0 x _ = x

instance IsBool0 'False where
  _If0 _ y = y
\end{code}

Note that `b` does not appear in the type of `_If0`, meaning that `b` cannot be
inferred from the context where `_If0` is applied.
Historically, this would always result in ambiguity errors, thus, such a type
was forbidden, forcing us to resolve the ambiguity by adding a trivial argument
or tagging the function somehow.

The `AllowAmbiguousTypes` extension tells the compiler to accept definitions
like `_If0` above, keeping signatures tidy;
the ambiguity can be resolved at use sites with the `TypeApplications`
extension, as it makes type arguments explicit (corresponding to those
variables under `forall`).

Some examples of `_If0` in action:

\begin{code}
_If0Examples :: [String]
_If0Examples =
  [ _If0 @'True "This" "That"
    -- "This"

  , _If0 @'False "This" "That"
    -- "That"

  , _If0 @(Int == Bool) "Int is equal to Bool" "Int is not equal to Bool"
    -- "Int is not equal to Bool"
  ]
\end{code}

However we will have trouble implementing `Get`.
To see why, below is what the final instance will roughly look like.
There are two cases as always.
If the type `a` we are looking for is equal to `b`, then we return the head `y`
of the list, otherwise we keep looking in the tail `ys`.

```haskell
instance (???) => Get a (b :* bs) where
  get :: b :* bs -> a
  get (y :* ys) =
    _If @(a == b)
      y         -- When (a == b) ~ 'True,  i.e., a  ~ b
      (get ys)  -- When (a == b) ~ 'False, i.e., a /~ b
```

The two branches of `_If` make assumptions that the type checker (currently)
rejects.
In the `True` branch, we return `y :: b` when the expected type is `a`,
this assumes that `a` is equal to `b`.
In the `False` branch, we call `get` on the tail, which requires a
`Get a bs` constraint.
We could add it to the context (`(???)` above), but that would imply a
traversal of the whole type, whereas the behavior of the previous
implementations was to stop as soon as we found the element we are looking for.

One way to view this problem is that the type of `_If` doesn't encode the
condition that the boolean is `True` in one branch, and `False` in the other.
It turns out we can apply that intuition quite literally in order to fix `_If`:

\begin{code}
class IsBool b where
  _If
    :: forall r
    .  (('True  ~ b) => r)
    -> (('False ~ b) => r)
    -> r
\end{code}

The `RankNTypes` extension allows quantifiers and constraints to occur
in a type signature in more locations than only the beginning.[^forall]
Thus, the two arguments of `_If` are now parameterized by constraints.
The function `_If` can only use its first argument if `b` is `True`, and its
second argument if `b` is `False`, whereas those arguments can use the
constraints to deduce other useful facts locally.
Interestingly, there is thus exactly one way to write each of the two `IsBool`
instances:

[^forall]: Both `RankNTypes` and `ScopedTypeVariables` enable the
  `forall` quantifier/keyword, that allows us to explicitly bind type
  variables. Otherwise, the quantifier gets inserted implicitly
  at the beginning of a type signature.

\begin{code}
instance IsBool 'True where
  _If :: forall r. r -> (('False ~ 'True) => r) -> r
  _If x _ = x

instance IsBool 'False where
  _If :: forall r. (('True ~ 'False) => r) -> r -> r
  _If _ y = y
\end{code}

The last piece of the puzzle is to complete the `(???)` context in the `Get`
instance sketched above.

- `_If` requires an `IsBool` instance in any case.

- We shall use the `If` type family we defined previously to construct a
  context which depends on the value of `(a == b)`.

In each branch of `_If`, `(a == b)` is assumed to be either `True` or `False`,
which allows the compiler to evaluate `If (a == b) _ _`, uncovering the
constraint that each case exactly needs, `(a ~ b)` in one, `(Get a bs)` in the
other.

We define a type synonym `If'` to collapse the `IsBool` and `If` constraints
together.

\begin{code}
type If' b c d = (IsBool b, If b c d)

instance If' (a == b) (a ~ b) (Get a bs)
  => Get a (b :* bs) where
  get :: b :* bs -> a
  get (y :* ys) =
    _If @(a == b)
      y         -- (If 'True (a ~ b) _)     becomes (a ~ b)
      (get ys)  -- (If 'False _ (Get a bs)) becomes (Get a bs)
\end{code}

We're now reaching the end of this heterogeneous list example.
From the outside, `get` should behave identically to `get1`,
but the definition of `get` was refactored to a single instance.
Do you find that easier to read than the previous versions?

Appendix: Dependently typed programming with singletons
=======================================================

A central reference in Haskell's dependently-typed landscape is
the [`singletons`](https://hackage.haskell.org/package/singletons) library.
One common point between this blog post and singletons is that, in fact,
the class `IsBool` is the Church encoding of the `Bool` singleton.

A singleton is a type with a single inhabitant. A useful class of singletons
can be defined as Generalized Algebraic Data Types (`GADTs` extension).
GADTs are types whose parameters depend on the constructors, and vice versa.

The parameter `b` of `SBool` below is tied to the constructor:
`STrue` is the unique inhabitant of `SBool 'True` and `SFalse` is the unique
inhabitant of `SBool 'False`. The point of such a type is that
by pattern matching on an `SBool b`, we can refine the value of `b`
in each branch, similarly to the `_If` combinator.

\begin{code}
data SBool (b :: Bool) where
  STrue  :: SBool 'True
  SFalse :: SBool 'False
\end{code}

There is an isomorphism between `SBool` and `IsBool` instances, that we can
witness by desugaring `IsBool` instances to the polymorphic functions
that they contain.

\begin{code}
-- Desugar IsBool by unwrapping _If
type IsBool_ b
  =  forall r
  .  (('True  ~ b) => r)
  -> (('False ~ b) => r)
  -> r

_SBool_to_IsBool :: forall b. SBool b -> IsBool_ b
_SBool_to_IsBool sb = case sb of
  STrue  -> (\x _ -> x)
  SFalse -> (\_ y -> y)

_IsBool_to_SBool :: forall b. IsBool_ b -> SBool b
_IsBool_to_SBool _If = _If STrue SFalse
\end{code}

It is easy to check that `_IsBool_to_SBool . _SBool_to_IsBool = id`.
The converse `_SBool_to_IsBool . _IsBool_to_SBool = id` is also true, but
the proof relies on a more involved argument (parametricity, free theorems).

The "Church encoding" claim above can be made more explicit with the
following equivalent[^box] reformulation of `SBool`. This also shows another
characteristic of GADTs: constructors can be given arbitrary function types,
especially polymorphic functions with constraints, as long as the result
matches the type being defined. The function constraints and arguments
become constructor fields.

[^box]: Up to internal boxing shenanigans.

\begin{code}
data SBool' (b :: Bool) where
  STrue'  :: ('True  ~ b) => SBool' b
  SFalse' :: ('False ~ b) => SBool' b
\end{code}

It should be compared to the `Either` data type (which can be defined using
GADT notation to make explicit the types of its constructors)
and its Church encoding.

```haskell
data Either a b where
  Left  :: a -> Either a b
  Right :: b -> Either a b

type Either_ a b = forall r. (a -> r) -> (b -> r) -> r
```

---

On the same topic
=================

- [Dependent types in Haskell](https://www.youtube.com/watch?v=wNa3MMbhwS4),
  talk by Stephanie Weirich.
- [Practical dependent types in Haskell](https://blog.jle.im/entry/practical-dependent-types-in-haskell-1.html),
  blog post by Justin Le.
