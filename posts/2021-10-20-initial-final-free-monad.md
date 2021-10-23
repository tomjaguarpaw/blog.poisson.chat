---
title: Initial and final encodings of free monads
keywords: ["haskell", "coq", "theory"]
alectryon: []
alectryon-cache: "posts/2021-10-20/"
---

Free monads are often introduced as [an algebraic data type][free-adt], an initial encoding:

```haskell
data Free f a = Pure a | Free (f (Free f a))
```

[free-adt]: https://hackage.haskell.org/package/free-5.1.7/docs/Control-Monad-Free.html#t:Free

Thanks to that, the term "free monads" tends to be confused with that encoding,
even though "free monads" originally refers to a representation-independent
idea. Dually, there is a final encoding of free monads:

```haskell
type Free' f a = (forall m. MonadFree f m => m a)
```

where [`MonadFree`][monadfree] is the following class:

```haskell
class Monad m => MonadFree f m where
  free :: f (m a) -> m a
```

[monadfree]: https://hackage.haskell.org/package/free-5.1.7/docs/Control-Monad-Free.html#t:MonadFree

The two types `Free` and `Free'` are isomorphic.
An explanation *a posteriori* is that free monads are unique up to isomorphism.
In this post, we will prove that they are isomorphic more directly,[^iceland]
in Coq.

[^iceland]: Answering [*Iceland_Jack*'s question on Twitter](https://twitter.com/Iceland_jack/status/1446971908445065221).

In other words, there are two functions:

```haskell
fromFree' :: Free' f a -> Free f a
toFree' :: Free f a -> Free' f a
```

such that, for all `u :: Free f a`,

```haskell
fromFree' (toFree' u) = u  -- easy
```

and for all `u :: Free' f a`,

```haskell
toFree' (fromFree' u) = u  -- hard
```

(Also, these functions are monad morphisms.)

The second equation is hard to prove because it relies on a subtle
fact about polymorphism. If you have a polymorphic function `forall m ...`,
it can only interact with `m` via operations provided as parameters---in the
`MonadFree` dictionary. The equation crashes down if you can perform
some kind of case analysis on types, such as `isinstanceof` in certain
languages. This idea is subtle because, how do you turn this negative property
"does not use `isinstanceof`" into a positive, useful fact about the functions
of a language?

Parametricity is the name given to such properties. You can get a good
intuition for it with some practice. For example, most people can convince
themselves that `forall a. a -> a` is only inhabited by the identity function.
But formalizing it so you can validate your intuition is a more mysterious art.

= Proof sketch

First, unfolding some definitions, the equation
we want to prove will simplify to the following:

```haskell
foldFree (u @(Free f)) = u @m
```

where `u :: forall m. MonadFree f m => m a` is specialized at `Free f` on the
left, at an arbitrary `m` on the right, and `foldFree :: Free f a -> m a`
is a certain function we do not need to look into for now.

The main idea is that those different specializations of `u` are *related*
by a *parametricity theorem* (aka. [*free theorem*][tff]).

<blockquote>
For all monads `m1`, `m2` that are instances of `MonadFree f`, and for any
relation `r` between `m1` and `m2`,
if `r` satisfies `$CERTAIN_CONDITIONS`, then `r` relates `u @m1` and `u @m2`.
</blockquote>

In this case, we will let `r` relate `u1 :: Free f a` and `u2 :: m a` when:

```haskell
foldFree u1 = u2
```

As it turns out, `r` will satisfy `$CERTAIN_CONDITIONS`, so that the
parametricity theorem above applies. This
yields exactly the desired conclusion:

```haskell
foldFree (u @(Free f)) = u @m
```

It is going to be a **gnarly** exposition of definitions before we can even get
to the proof, and the only reason I can think of to stick around is morbid
curiosity. But I had the proof and I wanted to do something
with it.[^alectryon]

[^alectryon]: Also an excuse to integrate [Alectryon](https://plv.csail.mit.edu/blog/alectryon.html#alectryon) in my blog.

= Formalization in Coq

<details class="code-details">
  <summary>Imports and setting options</summary>

```alectryon
From Coq Require Import Morphisms.

Set Implicit Arguments.
Set Contextual Implicit.
```
</details>

== Initial free monads

Right off the bat, the first hurdle is that we cannot actually write the initial `Free` in Coq.
To guarantee that all functions terminate and to prevent logical
inconsistencies, Coq imposes restrictions about what recursive types can be
defined. Indeed, `Free` could be used to construct an infinite loop by instantiating
it with a contravariant functor `f`. The following snippet shows how we can
inhabit the empty type `Void`, using only non-recursive definitions, so it's
fair to put the blame on `Free`:

```haskell
newtype Cofun b a = Cofun (a -> b)

omicron :: Free (Cofun Void) Void -> Void
omicron (Pure y) = y
omicron (Free (Cofun z)) = z (Free (Cofun z))

omega :: Void
omega = omicron (Free (Cofun omicron))
```

To bypass that issue, we can tweak the definition of `Free` into what you might
know as [the *freer monad*][freer], or [the *operational monad*][operational].
The key difference is that the recursive occurrence of `Free f a` is no longer
under an abstract `f`, but a concrete `(->)` instead.

[freer]: https://okmij.org/ftp/Haskell/extensible/more.pdf
[operational]: https://apfelmus.nfshost.com/articles/operational-monad.html

```alectryon
Inductive Free (f : Type -> Type) (a : Type) : Type :=
| Pure : a -> Free f a
| Bind : forall e, f e -> (e -> Free f a) -> Free f a
.
```

=== Digression on containers

With that definition, it is no longer necessary for `f` to be a functor---it's
even undesirable because of size issues. Instead, `f` should rather be thought
of as a type of "shapes", containing "positions" of type `e`, and that induces
a functor by assigning values to those positions (via the function `e -> Free
f a` here); such an `f` is also known as a ["container"][containers].

[containers]: https://citeseer.ist.psu.edu/viewdoc/download?doi=10.1.1.120.9567&rep=rep1&type=pdf

For example, the `Maybe` functor consists of two "shapes": `Nothing`, with no
positions (indexed by `Void`), and `Just`, with one position (indexed by `()`).
Those shapes are defined by the following GADT, the `Maybe` container:

```haskell
data PreMaybe _ where
  Nothing_ :: PreMaybe Void
  Just_ :: PreMaybe ()
```

A container extends into a functor, using a construction that some call [`Coyoneda`][coyoneda]:

```haskell
data Maybe' a where
  MkMaybe' :: forall a e. PreMaybe e -> (e -> a) -> Maybe' a

data Coyoneda f a where
  Coyoneda :: forall f a e. f e -> (e -> a) -> Coyoneda f a
```

`Freer f a` (where `Freer` is called `Free` here in Coq) coincides with
`Free (Coyoneda f) a` (for the original definition of `Free` at the top).
If `f` is already a functor, then it is observationally equivalent to `Coyoneda f`.

[coyoneda]: https://hackage.haskell.org/package/kan-extensions-5.2.3/docs/Data-Functor-Coyoneda.html#t:Coyoneda

== `Monad` and `MonadFree`

The `Monad` class hides no surprises. For simplicity we skip the `Functor` and `Applicative`
classes. Like in C, `return` is a keyword in Coq, so we have to settle for another name.

```alectryon
Class Monad (m : Type -> Type) : Type :=
  { pure : forall {a}, a -> m a
  ; bind : forall {a b}, m a -> (a -> m b) -> m b
  }.
(* The braces after `forall` make the arguments implicit. *)
```

Our `MonadFree` class below is different than in Haskell because of the switch
from functors to containers (see previous section).
In the original `MonadFree`, the method `free` takes an argument of type `f (m
a)`, where the idea is to "interpret" the outer layer `f`, and "carry on" with
a continuation `m a`. Containers encode that outer layer without the
continuation.[^no-cont]

[^no-cont]: That idea is also present in [Kiselyov and Ishii's paper][freer].

```alectryon
Class MonadFree {f m : Type -> Type} `{Monad m} : Type :=
  { free : forall {x}, f x -> m x }.

(* Some more implicit arguments nonsense. *)
Arguments MonadFree f m {_}.
```

Here comes the final encoding of free monads. The resemblance to the
Haskell code above should be apparent in spite of some funny syntax.

```alectryon
Definition Free' (f : Type -> Type) (a : Type) : Type :=
  forall m `(MonadFree f m), m a.
```

Type classes in Coq are simply types with some extra type inference rules to
infer dictionaries. Thus, the definition of `Free'` actually desugars to
a function type `forall m, Monad m -> MonadFree f m -> m a`.
A value `u : Free' f a` is a function whose arguments are a type
constructor `m`, followed by two dictionaries of the `Monad` and `MonadFree` classes.
We specialize `u` to a monad `m` by writing `u m _ _`, applying `u` to the type
constructor `m` and two holes (underscores) for the dictionaries, whose
contents will be inferred via type class resolution.
See for example `fromFree'` below.

While we're at it, we can define the instances of `Monad` and `MonadFree` for
the initial encoding `Free`.

```alectryon
Fixpoint bindFree {f a b} (u : Free f a) (k : a -> Free f b) : Free f b :=
  match u with
  | Pure a => k a
  | Bind e h => Bind e (fun x => bindFree (h x) k)
  end.

Instance Monad_Free f : Monad (Free f) :=
  {| pure := @Pure f
  ;  bind := @bindFree f
  |}.

Instance MonadFree_Free f : MonadFree f (Free f) :=
  {| free A e := Bind e (fun a => Pure a)
  |}.
```

== Interpretation of free monads

To show that those monads are equivalent, we must exhibit a mapping going both ways.

The easy direction is from the final `Free'` to the initial `Free`: with the
above instances of `Monad` and `MonadFree`, just monomorphize the polymorph.

```alectryon
Definition fromFree' {f a} : Free' f a -> Free f a :=
  fun u => u (Free f) _ _.
```

The other direction is obtained via a [fold][fold] of `Free f`, which allows us to interpret it
in any instance of `MonadFree f`: replace `Bind` with `bind`, interpret the
first operand with `free`, and recurse in the second operand.

[fold]: http://www.cs.nott.ac.uk/~pszgmh/fold.pdf

```alectryon
Fixpoint foldFree {f m a} `{MonadFree f m} (u : Free f a) : m a :=
  match u with
  | Pure a => pure a
  | Bind e k => bind (free e) (fun x => foldFree (k x))
  end.

Definition toFree' {f a} : Free f a -> Free' f a :=
  fun u M _ _ => foldFree u.
```

== Equality

In everyday mathematics, equality is a self-evident notion that we take for granted.
But if you want to minimize your logical foundations, you do not need equality
as a primitive. Equations are just equivalences, where the equivalence relation
is kept implicit.

Who even decides what the rules for reasoning about equality are anyway?
You decide, by picking the underlying equivalence relation.
[^eq]

[^eq]: Those who do know Coq will wonder, what about `eq` ("intensional equality")?
It is a fine default relation for first-order data (`nat`, pairs, sums, lists,
ASTs without HOAS). But it is too strong for computations (functions and
coinductive types) and proofs (of `Prop`s). Then a common approach is to
introduce extensionality axioms, postulating that "extensional equality implies
intensional equality". But you might as well just stop right after proving
whatever extensional equality you wanted.

Here is a class for equality. It is similar to `Eq` in Haskell,
but it is propositional (`a -> a -> Prop`) rather than boolean (`a -> a -> Bool`),
meaning that equality doesn't have to be decidable.

```alectryon
Class PropEq (a : Type) : Type :=
  propeq : a -> a -> Prop.

Notation "x = y" := (propeq x y) : type_scope.
```

For example, for inductive types, a common equivalence can be defined as
another inductive type which equates constructors and their fields recursively.
Here it is for `Free`:

```alectryon
Inductive eq_Free f a : PropEq (Free f a) :=
| eq_Free_Pure x : eq_Free (Pure x) (Pure x)
| eq_Free_Bind p (e : f p) k1 k2
  : (forall x, eq_Free (k1 x) (k2 x)) ->
    eq_Free (Bind e k1) (Bind e k2)
.

(* Register it as an instance of PropEq *)
Existing Instance eq_Free.
```

Having defined equality for `Free`, we can state and prove one half of the
isomorphism between `Free` and `Free'`.

```alectryon
Theorem to_from f a (u : Free f a)
  : fromFree' (toFree' u) = u.
```

The proof is straightforward by induction, case analysis (which is performed as
part of induction), and simplification.

```alectryon
Proof.
  induction u. all: cbn. all: constructor; auto.
Qed.
```

== Equality on final encodings, naive attempts

To state the other half of the isomorphism (`toFree' (fromFree' u) = u`),
it is less obvious what the right equivalence relation on `Free'` should be.
When are two polymorphic values ``u1, u2 : forall m `(MonadFree f m), m a`` equal?
A fair starting point is that all of their specializations must be equal.
"Equality" requires an instance of `PropEq`, which must be introduced as an
extra parameter.

```alectryon
(* u1 and u2 are "equal" when all of their specializations
   (u1 m _ _) and (u2 m _ _) are equal. *)
Definition eq_Free'_very_naive f a (u1 u2 : Free' f a) : Prop :=
  forall m `(MonadFree f m) `(forall x, PropEq (m x)),
    u1 m _ _ = u2 m _ _.
```

That definition is flagrantly inadequate: so far, a `PropEq` instance can be
any relation, including the empty relation (which never holds), and the `Monad` instance
(as a superclass of `MonadFree`) might be unlawful. In our
desired theorem, `toFree' (fromFree' u) = u`, the two sides use *a priori*
different combinations of `bind` and `pure`, so we expect to rely on laws to
be able to rewrite one side into the other.

In programming, we aren't used to proving that implementations satisfy their laws,
so there is always the possibility that a `Monad` instance is unlawful.
In math, the laws are in the definitions; if something doesn't satisfy the
monad laws, it's not a monad. Let's irk some mathematicians and
say that a *lawful monad* is a monad that satisfies the monad laws.
Thus we will have one `Monad` class for the operations only, and one
`LawfulMonad` class for the laws they should satisfy.
Separating code and proofs that way helps to organize things.
Code is often much simpler than the proofs about it, since the latter
necessarily involves dependent types.

```alectryon
Class LawfulMonad {m} `{Monad m} `{forall a, PropEq (m a)} : Prop :=
  { Equivalence_LawfulMonad :> forall a, Equivalence (propeq (a := m a))
  ; propeq_bind : forall a b (u u' : m a) (k k' : a -> m b),
      u = u' -> (forall x, k x = k' x) -> bind u k = bind u' k'
  ; bind_pure : forall a (u : m a),
      bind u (pure (a := a)) = u
  ; pure_bind : forall a b (x : a) (k : a -> m b),
      bind (pure x) k = k x
  ; bind_bind : forall a b c (u : m a) (k : a -> m b) (h : b -> m c),
      bind (bind u k) h = bind u (fun x => bind (k x) h)
  }.
```

The three monad laws should be familiar (`bind_pure`, `pure_bind`, `bind_bind`).
In those equations, "`=`" denotes a particular equivalence relation, which is now a
parameter/superclass of the class. Once you give up on equality as a primitive notion,
algebraic structures must now carry their own equivalence relations.
The requirement that it is an *equivalence relation* also becomes an explicit law
(`Equivalence_LawfulMonad`), and we expect that operations (in this case, `bind`)
preserve the equivalence (`propeq_bind`). Practically speaking, that last fact
allows us to rewrite subexpressions locally, otherwise we could only apply the
monad laws at the root of an expression.

A less naive equivalence on `Free'` is thus to restrict the quantification
to lawful instances:

```alectryon
Definition eq_Free'_naive f a (u1 u2 : Free' f a) : Prop :=
  forall m `(MonadFree f m) `(forall x, PropEq (m x)) `(!LawfulMonad (m := m)),
    u1 m _ _ = u2 m _ _.
```

That is a quite reasonable definition of equivalence for `Free'`. In other circumstances,
it could have been useful. Unfortunately, it is too strong here:
we cannot prove the equation `toFree' (fromFree' u) = u` with that interpretation of `=`.
Or at least I couldn't figure out a solution.
We will need more assumptions to be able to apply the parametricity theorem of
the type `Free'`. To get there, we must formalize Reynolds' relational interpretation of types. 

== Types as relations

The core technical idea in [Reynolds' take on parametricity][reynolds] is to
interpret a type `t` as a relation `Rt : t -> t -> Prop`. Then, the
**parametricity theorem** is that all terms `x : t` are related to themselves
by `Rt` (`Rt x x` is true).
If `t` is a polymorphic type, that theorem connects different specializations
of a same term `x : t`, and that allows us to formalize arguments that rely on
"parametricity" as a vague idea.

[reynolds]: https://people.mpi-sws.org/~dreyer/tor/papers/reynolds.pdf

For example, if `t = (forall a, a -> a)`, then `Rt` is the following relation,
which says that two functions `f` and `f'` are related if for any relation `Ra`
(on any types), `f` and `f'` send related inputs (`Ra x x'`) to related outputs
(`Ra (f a x) (f' a' x')`).

```
Rt f f' =
  forall a a' (Ra : a -> a' -> Prop),
  forall x x', Ra x x' -> Ra (f a x) (f' a' x')
```

If we set `Ra x x'` to mean "`x` equals an arbitrary constant `z0`"
(ignoring `x'`, i.e., treating `Ra` as a unary relation), the above relation
`Rt` amounts to saying that `f z0 = z0`, from which we deduce that `f` must be
the identity function.

The fact that `Rt` is a relation is not particularly meaningful to the parametricity
theorem, where terms are simply related to themselves, but it is a feature of
the construction of `Rt`: the relation for a composite type `t1 -> t2` combines
the relations for the components `t1` and `t2`, and we could not get the same result
with only unary predicates throughout.[^well] More formally, we define
a relation `R[t]` by induction on `t`, between the types `t` and `t'`,
where `t'` is the result of renaming all variables `x` to `x'` in `t`
(including binders). The two most interesting cases are:

- `t` starts with a quantifier `t = forall a, _`, for a type variable `a`.
  Then the relation `R[forall a, _]` between the polymorphic `f` and `f'` takes
  two arbitrary types `a` and `a'` to specialize `f` and `f'` with, and
  a relation `Ra : a -> a' -> Prop`, and relates `f a` and `f' a'` (recursively),
  using `Ra` whenever recursion reaches a variable `a`.

- `t` is an arrow `t1 -> t2`, then `R[t1 -> t2]` relates functions that send
  related inputs to related outputs.

[^well]: Well, if you tried you would end up with the unary variant of the
parametricity theorem, but it's much weaker than the binary version shown here.
n-ary versions are also possible and even more general, but you have to look hard
to find legitimate uses.

In summary:

```
R[forall a, t](f, f') = forall a a' Ra, R[t](f a)(f' a')
R[a](f, f')           = Ra(f, f')
                        -- Ra should be in scope when a is in scope.
R[t1 -> t2](f, f')    = forall x x', R[t1](x, x') -> R[t2](f x, f' x')
```

That explanation was completely unhygienic, but refer to
[Reynolds' paper][reynolds] or [Wadler's *Theorems for free!*][tff] for more formal details.

[tff]: https://people.mpi-sws.org/~dreyer/tor/papers/wadler.pdf

For sums (`Either`/`sum`) and products (`(,)`/`prod`), two values are related if
they start with the same constructor, and their fields are related (recursively).
This can be deduced from the rules above applied to the Church encodings of
sums and products.

== Type constructors as relation transformers

While types `t : Type` are associated to relations `Rt : t -> t -> Prop`,
type constructors `m : Type -> Type` are associated to relation transformers
(functions on relations) `Rm : forall a a', (a -> a' -> Prop) -> (m a -> m a' -> Prop)`.
It is usually clear what's what from the context, so we will often
refer to "relation transformers" as just "relations".

For example, the initial `Free f a` type gets interpreted to the relation `RFree Rf Ra`
defined as follows. Two values `u1 : Free f1 a1` and `u2 : Free f2 a2` are related by `RFree`
if either:

- `u1 = Pure x1`, `u2 = Pure x2`, and `x1` and `x2` are related (by `Ra`); or
- `u1 = Bind e1 k1`, `u2 = Bind e2 k2`, `e1` and `e2` are related, and `k1` and `k2` are related (recursively).

We thus have one rule for each constructor (`Pure` and `Bind`)
in which we relate each field (`Ra x1 x2` in `RFree_Pure`; `Rf _ _ _ y1 y2` and `RFree Rf Ra (k1 x1) (k2 x2)` in `RFree_Bind`).
Let us also remark that the existential type `e` in `Bind` becomes an existential relation `Re` in `RFree_Bind`.

```alectryon
Inductive RFree {f₁ f₂ : Type -> Type}
    (Rf : forall a₁ a₂ : Type, (a₁ -> a₂ -> Prop) -> f₁ a₁ -> f₂ a₂ -> Prop)
    {a₁ a₂ : Type} (Ra : a₁ -> a₂ -> Prop) : Free f₁ a₁ -> Free f₂ a₂ -> Prop :=
  | RFree_Pure : forall (x₁ : a₁) (x₂ : a₂),
      Ra x₁ x₂ -> RFree Rf Ra (Pure x₁) (Pure x₂)
  | RFree_Bind : forall (e₁ e₂ : Type) (Re : e₁ -> e₂ -> Prop) (y₁ : f₁ e₁) (y₂ : f₂ e₂),
      Rf e₁ e₂ Re y₁ y₂ ->
      forall (k₁ : e₁ -> Free f₁ a₁) (k₂ : e₂ -> Free f₂ a₂),
      (forall (x₁ : e₁) (x₂ : e₂),
        Re x₁ x₂ -> RFree Rf Ra (k₁ x₁) (k₂ x₂)) ->
      RFree Rf Ra (Bind y₁ k₁) (Bind y₂ k₂).
```

Inductive relations such as `RFree`, indexed by types with existential
quantifications such as `Free`, are a little terrible to work with
out-of-the-box---especially if you're allergic to UIP.
Little "inversion lemmas" like the following make them a bit nicer by
reexpressing those relations in terms of some standard building blocks which
leave less of a mess when decomposed.

```alectryon
Definition inv_RFree {f₁ f₂} Rf {a₁ a₂} Ra (u₁ : Free f₁ a₁) (u₂ : Free f₂ a₂)
  : RFree Rf Ra u₁ u₂ ->
    match u₁, u₂ return Prop with
    | Pure a₁, Pure a₂ => Ra a₁ a₂
    | Bind y₁ k₁, Bind y₂ k₂ =>
      exists Re, Rf _ _ Re y₁ y₂ /\
        (forall x₁ x₂, Re x₁ x₂ -> RFree Rf Ra (k₁ x₁) (k₂ x₂))
    | _, _ => False
    end.
Proof.
  intros []; eauto.
Qed.
```

Type classes, which are (record) types, also get interpreted in the same way.
Since `Monad` is parameterized by a type constructor `m`, the relation `RMonad` between `Monad`
instances is parameterized by a relation between two type
constructors `m1` and `m2`. 
Two instances of `Monad`, i.e., two values of type `Monad m` for some `m`, are related
if their respective fields, i.e., `pure` and `bind`, are related.
`pure` and `bind` are functions, so two instances are related when they send related inputs
to related outputs.

```alectryon
Record RMonad (m₁ m₂ : Type -> Type)
    (Rm : forall a₁ a₂ : Type, (a₁ -> a₂ -> Prop) -> m₁ a₁ -> m₂ a₂ -> Prop)
    `{Monad m₁} `{Monad m₂} : Prop :=
  { RMonad_pure : forall (t₁ t₂ : Type) (Rt : t₁ -> t₂ -> Prop) (x₁ : t₁) (x₂ : t₂),
      Rt x₁ x₂ -> Rm t₁ t₂ Rt (pure x₁) (pure x₂)
  ; RMonad_bind : forall (t₁ t₂ : Type) (Rt : t₁ -> t₂ -> Prop) 
      (u₁ u₂ : Type) (Ru : u₁ -> u₂ -> Prop) (x₁ : m₁ t₁) (x₂ : m₂ t₂),
      Rm t₁ t₂ Rt x₁ x₂ ->
      forall (k₁ : t₁ -> m₁ u₁) (k₂ : t₂ -> m₂ u₂),
      (forall (x₁ : t₁) (x₂ : t₂),
         Rt x₁ x₂ -> Rm u₁ u₂ Ru (k₁ x₁) (k₂ x₂)) ->
      Rm u₁ u₂ Ru (bind x₁ k₁) (bind x₂ k₂)
  }.
```

`MonadFree` also gets translated to a relation `RMonadFree`. Related inputs, related outputs.

```alectryon
Record RMonadFree (f₁ f₂ : Type -> Type)
    (Rf : forall a₁ a₂ : Type, (a₁ -> a₂ -> Prop) -> f₁ a₁ -> f₂ a₂ -> Prop)
    (m₁ m₂ : Type -> Type)
    (Rm : forall a₁ a₂ : Type, (a₁ -> a₂ -> Prop) -> m₁ a₁ -> m₂ a₂ -> Prop)
    `{MonadFree f₁ m₁} `{MonadFree f₂ m₂} : Prop :=
  { RMonadFree_free : forall (a₁ a₂ : Type) (Ra : a₁ -> a₂ -> Prop) (x₁ : f₁ a₁) (x₂ : f₂ a₂),
      Rf a₁ a₂ Ra x₁ x₂ -> Rm a₁ a₂ Ra (free x₁) (free x₂)
  }.
```

Note that `RMonad` and `RMonadFree` are "relation transformer transformers", since they
take relation transformers as arguments, to produce a relation between class dictionaries.

We can now finally translate the final `Free'` to a relation.
Two values `u1 : Free' f1 a1` and `u2 : Free' f2 a2` are related
if, for any two monads `m1` and `m2`, with a relation transformer `Rm`,
whose `Monad` and `MonadFree` instances are related by `RMonad` and `RMonadFree`,
`Rm` relates `u1 m1 _ _` and `u2 m2 _ _`.

```alectryon
Definition RFree' {f₁ f₂} Rf {a₁ a₂} Ra (u₁ : Free' f₁ a₁) (u₂ : Free' f₂ a₂) : Prop :=
  forall m₁ m₂ `(MonadFree f₁ m₁) `(MonadFree f₂ m₂) Rm
    (pm : RMonad Rm) (pf : RMonadFree Rf Rm),
    Rm _ _ Ra (u₁ m₁ _ _) (u₂ m₂ _ _).
```

The above translation of types into relations can be automated by a tool such as
[*paramcoq*][paramcoq]. However *paramcoq* currently constructs relations in
`Type` instead of `Prop`, which got me stuck in universe inconsistencies.
That's why I'm declaring `Prop` relations the manual way here.

[paramcoq]: https://github.com/coq-community/paramcoq

The parametricity theorem says that any `u : Free' f a` is related to itself
by `RFree'` (for some canonical relations on `f` and `a`). It is a theorem about
the language Coq which we can't prove within Coq. Rather than postulate it,
we will simply add the required `RFree' _ _ u u` assumption to our proposition
(`from_to` below).
Given a concrete `u`, it should be straightforward to prove that assumption
case-by-case in order to apply that proposition.

These "relation transformers" are a bit of a mouthful to spell out,
and they're usually guessable from the type constructor (`f` or `m`),
so they deserve a class, that's a higher-order counterpart to `PropEq`
(like `Eq1` is to `Eq` in Haskell).

```alectryon
Class PropEq1 (m : Type -> Type) : Type :=
  propeq1 : forall a₁ a₂, (a₁ -> a₂ -> Prop) -> m a₁ -> m a₂ -> Prop.
```

Given a `PropEq1 m` instance, we can apply it to the relation `eq`
to get a plain relation which seems a decent enough default for `PropEq (m a)`.

```alectryon
Instance PropEq_PropEq1 {m} `{PropEq1 m} {a} : PropEq (m a) := propeq1 eq.
```

== Really lawful monads

We previously defined a "lawful monad" as a monad with an equivalence relation
(`PropEq (m a)`). To use parametricity, we will also need a monad `m` to provide
a relation transformer (`PropEq1 m`), which subsumes `PropEq` with the instance
just above.[^arbitrary] This extra structure comes with additional laws,
extending our idea of monads to "really lawful monads".

[^arbitrary]: To be honest, that decision was a little arbitrary. But I'm not
sure making things more complicated by keeping `EqProp1` and `EqProp` separate
buys us very much.

```alectryon
Class Trans_PropEq1 {m} `{PropEq1 m} : Prop :=
  trans_propeq1 : forall a₁ a₂ (r : a₁ -> a₂ -> Prop) x₁ x₁' x₂ x₂',
    x₁ = x₁' -> propeq1 r x₁' x₂ -> x₂ = x₂' -> propeq1 r x₁ x₂'.

Class ReallyLawfulMonad m `{Monad m} `{PropEq1 m} : Prop :=
  { LawfulMonad_RLM :> LawfulMonad (m := m)
  ; Trans_PropEq1_RLM :> Trans_PropEq1 (m := m)
  ; RMonad_RLM : RMonad (propeq1 (m := m))
  }.

Class ReallyLawfulMonadFree f `{PropEq1 f} m `{MonadFree f m} `{PropEq1 m} : Prop :=
  { ReallyLawfulMonad_RLMF :> ReallyLawfulMonad (m := m)
  ; RMonadFree_RLMF : RMonadFree (propeq1 (m := f)) (propeq1 (m := m))
  }.
```

We inherit the `LawfulMonad` laws from before.
The relations `RMonad` and `RMonadFree`,
defined earlier, must relate `m`'s instances of `Monad` and `MonadFree`,
for the artificial reason that that's roughly what `RFree'` will require.
We also add a generalized transitivity law, which allows us to rewrite
either side of a heterogeneous relation `propeq1 r` using the homogeneous
one `=` (which denotes `propeq1 eq`).

It's worth noting that there is some redundancy here, that could be avoided
with a bit of refactoring. That generalized transitivity law `Trans_PropEq1` implies
transitivity of `=`, which is part of the claim that `=` is an equivalence
relation in `LawfulMonad`. And the `bind` component of `RMonad` implies
`propeq_bind` in `LawfulMonad`, so these `RMonad` and `RMonadFree` laws
can also be seen as generalizations of congruence laws to heterogeneous
relations, making them somewhat less artificial than they may seem
at first.

Restricting the definition of equality on the final free monad `Free'` to
quantify only over really lawful monads yields the right notion of equality
for our purposes, which is to prove the `from_to` theorem below, validating the
isomorphism between `Free` and `Free'`.

```alectryon
Instance eq_Free' f `(PropEq1 f) a : PropEq (Free' f a) :=
  fun u₁ u₂ =>
    forall m `(MonadFree f m) `(PropEq1 m) `(!ReallyLawfulMonadFree (m := m)),
      u₁ m _ _ = u₂ m _ _.
```

---

Quickly, let's get the following lemma out of the way, which says
that `foldFree` commutes with `bind`. We're really saying that `foldFree` is
a monad morphism but no time to say it properly. The proof of the
next lemma will need this, but it's also nice to look at this on its own.

```alectryon
Lemma foldFree_bindFree {f m} `{MonadFree f m} `{forall a, PropEq (m a)} `{!LawfulMonad (m := m)}
    {a b} (u : Free f a) (k : a -> Free f b)
  : foldFree (bindFree u k) = bind (foldFree u) (fun x => foldFree (k x)).
Proof.
  induction u; cbn [bindFree foldFree].
  - symmetry. apply pure_bind with (k0 := fun x => foldFree (k x)).
  - etransitivity; [ | symmetry; apply bind_bind ].
    eapply propeq_bind.
    * reflexivity.
    * auto.
Qed.
```

== Finally the proof

Our goal is to prove an equation in terms of `eq_Free'`, which gives us
a really lawful monad as an assumption. We open a section to set up
the same context as that and to break down the proof into more digestible pieces.

```alectryon
Section ISOPROOF.

Context {f m} `{MonadFree f m} `{PropEq1 m} `{!ReallyLawfulMonad (m := m)}.
```

As outlined earlier, parametricity will yield an assumption `RFree' _ _ u u`,
and we will specialize it with a relation `R` which relates `u1 : Free f a` and `u2 : m a`
when `foldFree u1 = u2`. However, `RFree'` actually expects a relation
transformer rather than a relation, so we instead define `R` to relate
`u1 : Free f a1` and `u2 : Free f a2` when `propeq1 Ra (foldFree u1) u2`,
where `Ra` is a relation given between `a1` and `a2`.

```alectryon
Let R := (fun a₁ a₂ (Ra : a₁ -> a₂ -> Prop) u₁ u₂ => propeq1 Ra (foldFree u₁) u₂).
```

The following two lemmas are the "`$CERTAIN_CONDITIONS`" mentioned earlier,
that `R` must satisfy, i.e., we prove that `R`, via `RMonad` (resp.
`RMonadFree`), relates the `Monad` (resp. `MonadFree`) instances for `Free f`
and `m`.

```alectryon
Lemma RMonad_foldFree : RMonad (m₁ := Free f) R.
Proof.
  constructor; intros.
  - cbn. apply RMonad_RLM; auto.
  - unfold R. eapply trans_propeq1.
    + apply foldFree_bindFree.
    + eapply RMonad_RLM; eauto.
    + reflexivity.
Qed.

Context (Rf : PropEq1 f).
Context (RMonadFree_m : RMonadFree propeq1 propeq1).

Lemma RMonadFree_foldFree : RMonadFree Rf R.
Proof.
  constructor; intros.
  - unfold R.
    eapply trans_propeq1.
    + apply bind_pure.
    + apply RMonadFree_m. eassumption.
    + reflexivity.
Qed.

End ISOPROOF.
```

Here comes the conclusion, which completes our claim that `toFree'`/`fromFree'` is
an isomorphism (we proved the other half `to_from` on the way here).
This equation is under an assumption which parametricity promises to
fulfill, but we will have to step out of the system if we want it right now. 

```alectryon
Theorem from_to f (Rf : PropEq1 f) a (u : Free' f a)
  : RFree' Rf eq u u ->
    toFree' (fromFree' u) = u.
```

In the proof, we get the assumption `H : RFree' Rf eq u u`, which we apply
to the above lemmas, `RMonad_foldFree` and `RMonadFree_foldFree`,
using the `specialize` tactic. That yields exactly our desired goal.

```alectryon
Proof.
  do 2 red; intros.
  unfold toFree', fromFree'.
  red in H.
  specialize (H (Free f) m _ _ _ _ _ RMonad_foldFree (RMonadFree_foldFree RMonadFree_RLMF)).
  apply H.
Qed.
```

= Conclusion

If you managed to hang on so far, treat yourself to some chocolate.

To formalize a parametricity argument in Coq, I had to move the goalposts
quite a bit throughout the experiment:

- Choose a more termination-friendly encoding of recursive types.
- Relativize equality.
- Mess around with heterogeneous relations without crashing into UIP.
- Reinvent the definition of a monad, again.
- Come to terms with the externality of parametricity.

It could be interesting to see a "really lawful monad" spelled out fully.

Another similar but simpler exercise is to prove the equivalence between
initial and final encodings of lists. It probably wouldn't involve "relation
transformers" as much. There are also at least two different variants: is your
final encoding "`foldr`"- or "`fold`"-based (the latter mentions monoids, the
former doesn't)?

I hope that machinery can be simplified eventually, but given the technical
sophistication that is currently necessary, prudence is advised when navigating
around claims made "by parametricity".

---

= Related reading

- [Church encodings, inductive types, and relational parametricity](https://semantic-domain.blogspot.com/2020/12/church-encodings-are-inductive-types.html), by Neel Krishnaswami

- [Final algebra semantics is observational equivalence](https://prl.ccs.neu.edu/blog/2017/09/27/final-algebra-semantics-is-observational-equivalence/), by Max New

- [Relational parametricity for higher kinds](https://bentnib.org/fomega-parametricity.pdf) (PDF), by Robert Atkey

- [Free theorems involving type constructor classes](https://www.janis-voigtlaender.eu/papers.html#Voi09b) (PDF), by Janis Voigtländer

- [Parametricity, type equality and higher-order polymorphism](https://www.cis.upenn.edu/~sweirich/papers/gparam-jfp2.pdf) (PDF), by Dimitrios Vytiniotis and Stephanie Weirich

- [Unary parametricity vs binary parametricity](https://cstheory.stackexchange.com/questions/11541/unary-parametricity-vs-binary-parametricity/11637), on TCS StackExchange

- [`(F r -> r) -> r` gives an initial algebra of `F`](https://cs.stackexchange.com/questions/131901/how-to-prove-that-the-church-encoding-forall-r-f-r-r-r-gives-an-initi), on CS StackExchange
