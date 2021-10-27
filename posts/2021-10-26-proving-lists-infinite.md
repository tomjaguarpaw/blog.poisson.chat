---
title: On proving lists infinite
keywords: [coq, theory]
alectryon: []
alectryon-cache: "posts/2021-10-26"
---

It's obvious what an infinite list is. But when formalizing things,
we must be picky about definitions to not get tangled up in a messy
web of concepts.
This post will present some ways of saying that "a list is infinite"
formally in Coq.[^ziplist]

[^ziplist]: Which I've used recently in a proof that [there is no ZipList monad][ziplist].

[ziplist]: https://gist.github.com/Lysxia/b105bcb2f2ba835012476ab7fe37ae87

= Coinductive lists

<details class="code-details">
<summary>Imports and options</summary>
```alectryon
From Coq Require Import Arith Lia.

Set Primitive Projections.
Set Implicit Arguments.
Set Maximal Implicit Insertion.
Set Contextual Implicit.
```
</details>

First, define the type of lists.
Lists are made of `Cons` (`::`) and `Nil`. As it is a recursive type, we
also have to decide whether to make it *inductive*, so that only finite lists
can be constructed, or *coinductive*, so that lists might also be infinite
sequences of `Cons`. We start by introducing the type's *base functor*
`ColistF a _`, presenting the two list constructors without recursion.
We obtain the coinductive type `Colist a` as a fixed point of
`ColistF a : Type -> Type`.

```alectryon
Inductive ColistF (a : Type) (x : Type) :=
| Nil : ColistF a x
| Cons : a -> x -> ColistF a x
.

CoInductive Colist (a : Type) : Type :=
  Delay { force : ColistF a (Colist a) }.
```

Thus the type `Colist a` has a destructor
`force : Colist a -> ColistF a (Colist a)` (the final coalgebra of `ColistF a`)
and a constructor `Delay : ColistF a (Colist a) -> Colist a`.
This ceremony may look all mysterious if you're new to this; after living with
coinductive types for a while, you will assimilate their philosophy of
"*destructors* first"---unlike inductive types' "*constructors* first".

<details class="code-details">
<summary>Notation prep</summary>
```alectryon
Add Printing Constructor Colist.

Declare Scope colist_scope.
Delimit Scope colist_scope with colist.
Local Open Scope colist_scope.
```
</details>

Some familiar notations, `[]` for `Nil` and `::` for `Cons`.

```alectryon
Notation "'[' ']'" := Nil : colist_scope.
Notation "x :: xs" := (Cons x xs) : colist_scope.
```

== Some simple definitions

Recursive definitions involving lists mostly look as you would expect in
Coq as in any functional programming language,
but every output list is wrapped in an explicit `Delay`, and every input
list of a `match` is wrapped in a `force`. It's as if you were
handling lazy data structures in an eagerly evaluated programming language.
Coq is a pure and total language, so evaluation order doesn't
matter as much as in partial languages, but the operational semantics
is still careful to not reduce coinductive definitions unless they are
forced.

Here is the `map` function that any self-respecting type of list must provide.

```alectryon
CoFixpoint map {a b} (f : a -> b) (xs : Colist a) : Colist b := Delay
  match force xs with
  | [] => []
  | x :: xs => f x :: map f xs
  end.
```

Another example is the list `nats` of all natural numbers.
It relies on the more general definition of lists of numbers
greater than an arbitrary natural number `n`.

```alectryon
CoFixpoint nats_from (n : nat) : Colist nat := Delay
  (n :: nats_from (S n)).

Definition nats := nats_from 0.
```

Let's put that aside for now. We will be needing `map` and `nats` later.

= Never-ending lists

We will now say "infinite lists" in an informal you-know-what-I-mean sense,
as we explore different ways of making it more formal, which will
have their own names.

A list is infinite when it never ends with a `Nil`. But in constructive mathematics
we never say never---it's not even obvious how you could even say it in
this instance. A list is infinite when it, and its tails, always evaluate to a `Cons`.

A more "incremental" rephrasing of the above is that a list `xs` is infinite
when `xs` evaluates to a `Cons`, and its tail is also infinite. That definition
of infinite lists is recursive, so that you can "unfold" it iteratively to
establish that every tail evaluates to a `Cons`. But because it is recursive,
it's not *a priori* well-defined.

Let us forget about "is infinite" for a second, and talk more generally about
properties `P` that somehow subscribe to that definition: if `xs` satisfies
`P`, then `xs` evaluates to a `Cons`, and the tail of `xs` satisfies `P`. Let
us call such a `P` a *never-ending invariant*.

```alectryon
Definition Neverending_invariant {a} (P : Colist a -> Prop) : Prop :=
  forall xs, P xs -> exists x xs', force xs = Cons x xs' /\ P xs'.
```

The intuition is that if `xs` satisfies any never-ending invariant `P`,
then `xs` must be infinite. This leads to our first characterization of
infinite lists, "never-ending" lists.

= Never-ending: definition

A list is *never-ending* when it satisfies some never-ending invariant. 

```alectryon
Definition Neverending {a} (xs : Colist a) : Prop :=
  exists (P : Colist a -> Prop),
    Neverending_invariant P /\ P xs.
```

The key property that makes the notion of never-ending lists
useful is the following *unfolding lemma*:
a never-ending list is a `Cons`, and its tail is never-ending.

**Note: you can hover and click on the tactics in proof scripts
(`Proof. ... Qed.`) to see the intermediate proof states.**[^alectryon]

[^alectryon]: Plugging [Alectryon](https://plv.csail.mit.edu/blog/alectryon.html#alectryon).

```alectryon
Lemma unfold_Neverending {a} (xs : Colist a)
  : Neverending xs ->
    exists x xs',
      force xs = Cons x xs' /\ Neverending xs'.
Proof.
  intros NE.
  unfold Neverending in NE.
  destruct NE as [P [NE Hxs]].
  unfold Neverending_invariant in NE.
  apply NE in Hxs.
  destruct Hxs as [x [xs' [Hxs Hxs']]].
  exists x, xs'.
  split; [assumption | ].
  unfold Neverending.
  exists P.
  split; [ | assumption ].
  exact NE.
Qed.
```

Doesn't that lemma's statement remind you of `Neverending_invariant` above?

That lemma means exactly that the property of "being never-ending" is itself
a never-ending invariant!

```alectryon
Lemma Neverending_invariant_Neverending {a}
  : Neverending_invariant (Neverending (a := a)).
Proof.
  unfold Neverending. (* This goal looks funny -> *)
  exact (@unfold_Neverending a).
Qed.
```

The definition of `Neverending` makes it the *weakest
never-ending invariant*: all never-ending invariants imply `Neverending`.

```alectryon
Lemma Neverending_weakest {a} (P : Colist a -> Prop) (xs : Colist a)
  : Neverending_invariant P -> P xs -> Neverending xs.
Proof.
  intros INV H.
  unfold Neverending.
  exists P.
  split; assumption.
Qed.
```

This is actually an instance of a pretty general way of defining recursive
properties (and recursive types, by Curry-Howard) without using recursion.
You introduce a class of "invariants" identified by the recursive definition,
and then you pick the strongest or weakest one, depending on the situation
(inductive or coinductive).[^nu]

[^nu]: This is a generalization of the types
[`Mu` and `Nu`](https://hackage.haskell.org/package/data-fix-0.3.2/docs/Data-Fix.html#t:Nu)
as they are named in Haskell. This is also how the [paco](https://github.com/snu-sf/paco)
library defines coinductive propositions.

= Lists with too many elements

This next property is sufficient but not necessary: a list must be infinite
if it contains infinitely many distinct elements. While this sounds circular,
we care only about defining "infinite lists", and for that we can
leverage other "infinities" already lying around, like the natural numbers.
Note that an infinite list may not satisfy that property by repeating the same
finitely many elements (*e.g.*, `repeat 0`).

One way to show that a set is infinite is to exhibit an *injective* function
from the natural numbers (or any other infinite set): distinct elements are
mapped to distinct elements, or conversely, every image element has a unique
antecedent.

```alectryon
Definition injective {a b} (f : a -> b) : Prop :=
  forall x y, f x = f y -> x = y.
```

Now we need to tie those elements to a list, using the *membership relation*
`In`. That relation is defined inductively: an element `x` is in a list `xs` if
either `x` is the head of `xs` or `x` is in the tail of the list.

<details class="code-details">
<summary>Snip</summary>
```alectryon
Unset Elimination Schemes. (* Don't generate induction principles for us. *)
```
</details>

```alectryon
Inductive In {a : Type} (x : a) (xs : Colist a) : Prop :=
| In_split y ys : force xs = Cons y ys -> x = y \/ In x ys -> In x xs
.
```

<details class="code-details">
<summary>Snip</summary>
```alectryon
Lemma In_ind (a : Type) (x : a) (P : Colist a -> Prop)
    (H : forall xs (y : a) (ys : Colist a),
         force xs = y :: ys -> x = y \/ (In x ys /\ P ys) -> P xs)
  : forall xs, In x xs -> P xs.
Proof.
  fix SELF 2; intros xs [].
  eapply H; eauto.
  destruct H1; [ left | right ]; auto.
Qed.

Lemma not_In_Nil {a} (x : a) xs : force xs = [] -> In x xs -> False.
Proof.
  intros ? []; congruence.
Qed.
#[global] Hint Resolve not_In_Nil : core.
```
</details>

Naturally, an element cannot be in an empty list. Two distinct elements
cannot be in a list of length one. And so on. So if we can prove that
infinitely many elements are in a list, then the list must be infinite.
Let us call this property "surnumerable", since it means that
we can enumerate a subset of its elements.

== Surnumerability: definition

A list `xs` is *surnumerable* if there is some injective function
`f : nat -> a` such that `f i` is in `xs` for all `i`.

```alectryon
Definition Surnumerable {a} (xs : Colist a) : Prop :=
  exists f : nat -> a,
    injective f /\ forall i, In (f i) xs.
```

== `Surnumerable` implies `Neverending`

A simple approach is to prove that `Surnumerable` is a never-ending invariant,
but that requires decidable equality on `a`.
A more general solution considers the invariant satisfied by lists `xs`
such that `Surnumerable (ys ++ xs)` for some finite `ys`.
The pigeonhole reasoning for that proof seems challenging,
so I haven't done it myself.

```alectryon
Theorem Surnumerable_Neverending {a} (xs : Colist a)
  : Surnumerable xs -> Neverending xs.
Proof.
  (* Exercise for the reader. *)
Abort.
```

Injectivity is not very "constructive", you have to use a lot of tricks to
recover useful information from it.
In a proof that surnumerability implies never-ending-ness,
a big part of it is to prove that surnumerability of a list `Cons x xs`
implies (more or less) surnumerability of its tail `xs`.
In other words, given `f` which describes an infinite set of elements in
`Cons x xs`, and we must construct a new `f2` which describes an infinite
set of elements all in `xs`.
The challenge is thus to "remove" the head `x` from the given injective
function---if `x` occurs at all in `f`.
This would be easier if we had a pseudo-inverse function to point to its
antecedent by `f`. The existence of a pseudo-inverse is equivalent
to injectivity classically, but it is stronger constructively.
In category theory, a function `f` with a pseudo-inverse is called a
[*split mono(morphism)*](https://ncatlab.org/nlab/show/split+monomorphism).

```alectryon
Definition splitmono {a b} (f : a -> b) : Prop :=
  exists g : b -> a, forall x, g (f x) = x.
```

We obtain a variant of `Surnumerable` using `splitmono` instead of `injective`.

```alectryon
Definition SplitSurnumerable {a} (xs : Colist a) : Prop :=
  exists (f : nat -> a),
    splitmono f /\ forall i, In (f i) xs.
```

The pseudo-inverse makes the proof of never-ending-ness much simpler.

```alectryon
Theorem SplitSurnumerable_Neverending {a} (xs : Colist a)
  : SplitSurnumerable xs -> Neverending xs.
Proof.
  intros PN. unfold SplitSurnumerable in PN.
  destruct PN as (f & Hf & Hincl).
  unfold Neverending.
  (* Here is the never-ending invariant. *)
  exists (fun xs => exists n, forall i, n <= i -> In (f i) xs).
  split.
  - unfold Neverending_invariant.
    intros xs_ [n Hn].
    destruct (force xs_) as [ | x xs'] eqn:Hforce.
    + exfalso. eauto using not_In_Nil.
    + exists x, xs'; split; [ auto | ].
      destruct Hf as [g Hf].
      exists (max n (S (g x))).
      intros i Hi.
      specialize (Hn i (Nat.max_lub_l _ _ _ Hi)).
      destruct Hn.
      rewrite H in Hforce; inversion Hforce; subst; clear Hforce.
      destruct H0.
      * exfalso. rewrite <- H0 in Hi. rewrite Hf in Hi. lia.
      * assumption.
  - exists 0. auto.
Qed.
```

Surnumerability may be easier to prove than never-ending-ness
in some situations. A proof that a list is never-ending essentially "walks
through" the evaluation of the list, but in certain situations the list
might be too abstract to inspect, for example when reasoning by
parametricity,[^param] and we can only prove the membership of individual
elements one by one.

[^param]: Like in the [no-ziplist-monad proof][ziplist].

= Enumerability

Our last idea is that infinite lists (with element type `a`) are in bijection
with functions `nat -> a`. So we can show that a list is infinite by proving
that it corresponds to a function `nat -> a` via such a bijection.
We shall use the obvious bijection that sends `f` to `map f nats`---and
conversely sends an infinite list `xs` to a function `index xs : nat -> a`.
We will thus say that a list `xs` is *enumerable* if it can be written as
`map f nats` for some `f`.

== Equality of colists

Before we can state the equation `xs = map f nats`, we must choose a notion of
equality. One can be readily obtained via the following coinductive relation,
which corresponds to the *relational interpretation* of the type `Colist`
*à la Reynolds*.[^prev] It interprets the type constructor `Colist : Type -> Type`
as a relation transformer `RColist : (a -> b -> Prop) -> (Colist a -> Colist b -> Prop)`,
which can be specialized to an equivalence relation `RColist eq`;
we will write it in infix notation as `==` in the rest of the post.

[^prev]: See also [my previous post](./2021-10-20-initial-final-free-monad.html#types-as-relations).

```alectryon
Inductive RColistF {a b} (r : a -> b -> Prop) xa xb (rx : xa -> xb -> Prop)
  : ColistF a xa -> ColistF b xb -> Prop :=
| RNil : RColistF r rx [] []
| RCons x xs y ys : r x y -> rx xs ys -> RColistF r rx (Cons x xs) (Cons y ys)
.

CoInductive RColist {a b} (r : a -> b -> Prop) (xs : Colist a) (ys : Colist b) : Prop :=
  RDelay { Rforce : RColistF r (RColist r) (force xs) (force ys) }.

Notation "x == y" := (RColist eq x y) (at level 70) : colist_scope.
```

== Enumerability: definition

We can now say formally that `xs` is *enumerable* by `f` if `xs == map f nats`.

```alectryon
Definition Enumerable_by {a} (f : nat -> a) (xs : Colist a) : Prop :=
  xs == map f nats.

Definition Enumerable {a} (xs : Colist a) : Prop :=
  exists f, Enumerable_by f xs.
```

As mentioned earlier, the equation `xs == map f nats` exercises one half of the
bijection between infinite lists and functions on `nat`. Formalizing the other
half takes more work, and it will actually let us prove that `Neverending`
implies `Enumerable`.

= `Neverending` implies `Enumerable`

Essentially, we need to define an indexing function `index : Colist a -> nat -> a`.
However, this is only well-defined for infinite lists. A better type
will be a dependent type `index : forall (xs : Colist a), Neverending xs -> nat -> a`,
where the input list `xs` must be never-ending.

Start with a naive definition having the simpler type, which
handles partiality with a default value:

```alectryon
Fixpoint index_def {a} (def : a) (xs : Colist a) (i : nat) : a :=
  match force xs, i with
  | Cons x _, O => x
  | Cons _ xs, S i => index_def def xs i
  | Nil, _ => def
  end.
```

Given a never-ending list, we are able to extract an arbitrary value as
a default---which will be passed to `index_def` but never actually be used.
It takes a bit of dependently typed programming, which we dispatch with
tactics. And since we don't actually care about the result we can keep
the definition opaque with `Qed` (instead of `Defined`).

```alectryon
Definition head_NE {a} (xs : Colist a) (NE : Neverending xs) : a.
Proof.
  destruct (force xs) as [ | x xs' ] eqn:Hxs.
  - exfalso. apply unfold_Neverending in NE. destruct NE as [? [? []]]. congruence.
  - exact x.
Qed.
```

Combining `index_def` and `head_NE`, we obtain our `index` function.

```alectryon
Definition index {a} (xs : Colist a) (NE : Neverending xs) (i : nat) : a :=
  index_def (head_NE NE) xs i.
```

The remaining code in this post proves that a never-ending list `xs` is enumerated by `index xs`.

This first easy lemma says that `index_def` doesn't depend on the default value
if the list is never-ending.

```alectryon
Lemma index_def_Neverending {a} (def def' : a) (xs : Colist a) (i : nat)
  : Neverending xs -> index_def def xs i = index_def def' xs i.
Proof.
  revert xs; induction i; intros * NE; cbn.
  all: apply unfold_Neverending in NE.
  all: destruct NE as [x [xs' [Hxs NE]]]. 
  all: rewrite Hxs.
  all: auto.
Qed.
```

The next lemma does the heavy lifting, constructing an "equality invariant"
(or "bisimulation") that must hold between all respective tails of `xs` and
`map (index xs) nats`, which then implies `==`.

Note that instead of `index xs`, we actually write `index NE` where `NE` is
a proof of `Neverending xs`, since `index` requires that argument, and `xs`
can be deduced from `NE`'s type.

```alectryon
Lemma Neverending_Enumerable_ {a} (xs : Colist a) (NE : Neverending xs)
    (f : nat -> a) (n : nat)
  : (forall i, f (n+i) = index NE i) ->
    xs == map f (nats_from n).
Proof.
  revert xs NE n; cofix SELF; intros * Hf.
  constructor.
  assert (NE' := NE).
  apply unfold_Neverending in NE'.
  destruct NE' as [x [xs' [Hxs NE']]].
  rewrite Hxs; cbn.
  constructor.
  - specialize (Hf 0).
    cbn in Hf. rewrite Nat.add_0_r, Hxs in Hf. auto.
  - apply SELF with (NE := NE'); clear SELF.
    intros i. specialize (Hf (S i)).
    cbn in Hf. rewrite Nat.add_succ_r, Hxs in Hf.
    cbn; rewrite Hf. unfold index.
    apply index_def_Neverending. auto.
Qed.
```

Here's the final result. A never-ending list `xs` is enumerated by `index xs`.

```alectryon
Theorem Neverending_Enumerable_by {a} (xs : Colist a) (NE : Neverending xs)
  : Enumerable_by (index NE) xs.
Proof.
  unfold Enumerable_by, nats.
  apply Neverending_Enumerable_ with (NE0 := NE) (n := 0).
  reflexivity.
Qed.
```

We can repackage the theorem to hide the enumeration function,
more closely matching the English sentence "never-ending-ness implies
enumerability".

```alectryon
Corollary Neverending_Enumerable {a} (xs : Colist a)
  : Neverending xs -> Enumerable xs.
Proof.
  intros NE; eexists; apply Neverending_Enumerable_by with (NE0 := NE).
Qed.
```

The converse holds this time. The main insight behind the proof is that the
property "`xs == map f (nats_from n)` for some `n`" is a never-ending
invariant.

```alectryon
Theorem Enumerable_Neverending {a} (xs : Colist a)
  : Enumerable xs -> Neverending xs.
Proof.
  unfold Enumerable, Enumerable_by. intros [f EB].
  unfold Neverending.
  exists (fun xs => exists n, xs == map f (nats_from n)).
  split.
  - unfold Neverending_invariant. intros xs_ [n EB_].
    destruct EB_ as [EB_]. cbn in EB_. inversion EB_; subst.
    exists (f n), xs0. split; [ auto | ].
    exists (S n). assumption.
  - exists 0; assumption.
Qed.
```

== Reasoning with enumerability

I think `Neverending` is the most intuitive characterization of infinite lists,
but `Enumerable` can be easier to use.
To illustrate the point, let us examine a minimized version of my use case.

Consider an arbitrary function from lists of lists to lists:
`join : Colist (Colist a) -> Colist a`.

Try to formalize the statement

<blockquote>
When `join` is applied to a square matrix, *i.e.*, a list
of lists all of the same length, it computes the diagonal.
</blockquote>

(NB: An infinite list of infinite lists is considered a square.)

The literal approach is to introduce two functions `length` (in the
extended naturals) and `diagonal`, so we can translate the above sentence as
follows:

```coq
forall (xs : Colist (Colist a)),
  (forall row, In row xs -> length row = length xs) ->
  join xs == diagonal xs. 
```

However, this is unwieldly because the definition of `diagonal` is not
completely trivial. One will have to prove quite a few propositions about
`diagonal` in order to effectively reason about it.

A more parsimonious solution relies on the idea that the "diagonal" is simple
to define on functions `f : b -> b -> a`, as `diagonal f := fun x => f x x`.
That leads to the following translation:

```coq
forall (f : b -> b -> a) (xs : Colist b),
  join (map (fun x => map (f x) xs) xs) = map (fun x => f x x) xs
```

It takes a bit of squinting to recognize the original idea, but the upside
is that this is now a purely equational fact, without side conditions.

Rather than constrain a general list of lists to be a square,
we generate squares from a binary function `f : b -> b -> a` and a list `xs : Colist b`
representing the "sides" of the square, containing "coordinates" along one axis.
In particular, we can use `xs := nats` as the side of an "infinite square",
and `nats` arises readily from `Enumerable` lists.
Any square can be extensionally rewritten in that way.
This theorem requires no ad-hoc definition like a separate `diagonal` function,
and instead we can immediately use general facts about `map` both to prove and to use
such a theorem.

---

- **Surnumerable**: the list contains infinitely many distinct elements
  (two versions, based on classical injections and split monos).
- **Never-ending**: the list never terminates with `Nil`---always evaluates to `Cons`. 
- **Enumerable**: the list identifies with some function on `nat`.

```alectryon
Print SplitSurnumerable.
(*      ⇓      *)
Print Surnumerable.
(*      ⇓      *)
Print Neverending.
(*      ⇕      *)
Print Enumerable.
```

---

Can you think of other characterizations of infinite lists?
