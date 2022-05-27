---
title: "Formalizing finite sets"
keywords: ["coq", "theory", "combinatorics"]
alectryon: []
alectryon-cache: "posts/2022-05-27/"
---

Combinatorics studies mathematical structures by counting. Counting may seem like
a benign activity, but the same rigor necessary to prevent double- or under-counting
mistakes arguably underpins all of mathematics.[^undercount]

[^undercount]: Ironically, when making restaurant reservations, I still
  occasionally forget to count myself.

Combining my two favorite topics, I've always wanted to mechanize combinatorics
in Coq.[^bijou]
An immediate challenge is to formalize the idea of "set".[^settheory] We have
to be able to define the set of things we want to count. It turns out that
there are at least two ways of encoding sets in type theory: sets as
types, and sets as predicates. They are suitable for defining different classes
of operations: sums (disjoint union) are a natural operation on types, while
unions and intersections are a naturally defined on predicates.

[^bijou]: The code from this post is part of this project I've started
  [here][bijou]. Also check out Brent Yorgey's thesis:
  [*Combinatorial Species and Labelled Structures*][yorgey] (2014).

[bijou]: https://gitlab.com/lysxia/bijou

[yorgey]: http://ozark.hendrix.edu/~yorgey/pub/thesis.pdf

[^settheory]:
  Speaking of sets, it's important to distinguish *naive set theory* from *axiomatic
  set theory*.
  Naive set theory is arguably what most people think of when they hear "set".
  It is a semi-formal system for organizing mathematics: there are sets,
  they have elements, and there are various operations to construct and analyze
  sets, but overall we don't think too hard about what sets *are* (hence,
  "semi-formal"). When this blog post talks about sets, it is in the context of
  naive set theory. Axiomatic set theory is formal, with rules that are clear
  enough to be encoded in a computer. The name "axiomatic set theory" is
  a stroke of marketing genius, establishing it as the "standard" way of
  formalizing naive set theory,  and thus, all of mathematics, as can be seen
  in most introductory courses on formal logic. Historically, Zermelo's set
  theory was formulated at around the same time as Russell's type theory,
  and type theory is at the root of currently very active areas of programming
  language theory and formal methods.

The interplay between these two notions of sets, and finiteness, will then let
us prove the standard formula for the cardinality of unions, aka. the binary
inclusion-exclusion formula:

```
#|X ∪ Y| = #|X| + #|Y| - #|X ∩ Y|
```

<details>
  <summary>Imports and options</summary>
```alectryon
From Coq Require Import ssreflect ssrbool.

Set Implicit Arguments.
```
</details>

= Sets as types

The obvious starting point is to view a type as the set of its inhabitants.

How do we count its inhabitants?
We will say that a set `A` has cardinality `n` if there is a bijection between
`A` and the set `{0 .. n-1}` of natural numbers between `0` and `n-1`.

== Bijections

A bijection is a standard way to represent a one-to-one correspondence
between two sets, with a pair of inverse functions.
We define the type `bijection A B` as a record containing the two functions
and a proof of their inverse relationship.

```alectryon
Record is_bijection {A B} (to : A -> B) (from : B -> A) : Prop :=
  { from_to : forall a, from (to a) = a
  ; to_from : forall b, to (from b) = b }.

Record bijection (A B : Type) : Type :=
  { bij_to : A -> B
  ; bij_from : B -> A
  ; bij_is_bijection :> is_bijection bij_to bij_from }.

Infix "<-->" := bijection (at level 90) : type_scope.
```

We say that `A` and `B` are isomorphic when there exists a bijection between
`A` and `B`. Isomorphism is an equivalence relation: reflexive, symmetric,
transitive.[^groupoid]

[^groupoid]: Bijections actually form a groupoid (a "proof-relevant equivalence relation").

```alectryon
Definition bijection_refl {A} : A <--> A.
Admitted. (* Easy exercise *)

Definition bijection_sym {A B} : (A <--> B) -> (B <--> A).
Admitted. (* Easy exercise *)

Definition bijection_trans {A B C} : (A <--> B) -> (B <--> C) -> (A <--> C).
Admitted. (* Easy exercise *)

Infix ">>>" := bijection_trans (at level 40).
```

== Finite sets

Our "bijective" definition of cardinality shall rely on a primitive,
canonical family of finite types `{0 .. n-1}` that is taken for granted.
We can define them as the following sigma type, using the familiar set
comprehension notation, also known as [`ordinal` in *math-comp*][ordinal]:

[ordinal]: https://math-comp.github.io/htmldoc/mathcomp.ssreflect.fintype.html#ordinal

```alectryon
Definition fin (n : nat) : Type := { p | p < n }.
```

An inhabitant of `fin n` is a pair of a `p : nat` and
a proof object of `p < n`. Such proofs objects are unique for a given
`p` and `n`, so the first component uniquely determines the second component,
and `fin n` does have exactly `n` inhabitants.[^ordinal]

[^ordinal]:
    We could also have defined `fin` as the inductive type of bounded naturals,
    which is named `Fin.t` in the standard library. Anecdotal experience suggests
    that the sigma type is more beginner-friendly. But past a certain level
    of familiarity, I think they are completely interchangeable.

    ```alectryon
    Inductive fin' : nat -> Type :=
    | F0 : fin' 1
    | FS : forall n, fin' n -> fin' (S n).
    ```

    The definition of `fin` as a sigma type relies on details of the definition of
    the order relation `_ < _`. Other definitions may allow the proposition `p < n`
    to be inhabited by multiple proof objects, causing `fin n` to have "more" than
    `n` inhabitants unless they are collapsed by proof irrelevance.

=== Finiteness

We can now say that a type `A` has cardinality `n` if there is a bijection
between `A` and `fin n`, *i.e.*, there is an inhabitant of `A <--> fin n`.
Note that this only defines finite cardinalities, which is fine for doing
finite combinatorics. Infinity is really weird so let's not think about it.

As a sanity check, you can verify the cardinalities of the usual suspects,
`bool`, `unit`, and `Empty_set`.

```alectryon
Definition bijection_bool : bool <--> fin 2.
Admitted. (* Easy exercise *)

Definition bijection_unit : unit <--> fin 1.
Admitted. (* Easy exercise *)

Definition bijection_Empty_set : Empty_set <--> fin 0.
Admitted. (* Easy exercise *)
```

A type `A` is finite when it has some cardinality `n : nat`.
When speaking informally, it's common to view finiteness as a property,
a thing that a set either *is* or *is not*. To prove finiteness
is merely to exhibit the relevant data: a number to be the cardinality,
and an associated bijection (which we call an *enumeration* of `A`,
`enum` for short).
Hence we formalize "finiteness" as the type of that data.

```alectryon
Record is_finite (A : Type) : Type :=
  { card : nat
  ; enum : A <--> fin card }.
```

Further bundling `is_finite A` proofs with their associated set `A`, we obtain
a concept aptly named "finite type".[^mathcompfintype] A finite type is a type `A` paired with
a proof of `is_finite A`.

[^mathcompfintype]: *math-comp* has a different but equivalent definition of [`fintype`][mcft].

[mcft]: https://math-comp.github.io/htmldoc/mathcomp.ssreflect.fintype.html

```alectryon
Record finite_type : Type :=
  { ft_type :> Type
  ; ft_is_finite :> is_finite ft_type }.
```

We leverage coercions (indicated by `:>`) to lighten the notation of
expressions involving `finite_type`.

The first coercion `ft_type` lets us use a `finite_type` as a `Type`.
So if `E : finite_type`, we can write the judgement that
"`e` is an element of `E`" as `e : E`, which implicitly expands to
the more cumbersome `e : ft_type E`.

Similarly, the second coercion `ft_is_finite` lets us access
the evidence of finiteness without naming that field. In particular,
we can write the cardinality of `E : finite_type` as `card E`,
as if `card` were a proper field of `E` rather than the nested record it
actually belongs to. This is a convenient mechanism for overloading,
letting us reuse the name `card`(inality) even though records technically
cannot have fields with the same name.
With that, we define `#|A|` as sugar for `card A`:

```alectryon
Notation "'#|' A '|'" := (card A).
```


<details>
<summary>Some notation boilerplate</summary>

```alectryon
Declare Scope fintype_scope.
Delimit Scope fintype_scope with fintype.
Bind Scope fintype_scope with finite_type.
```
</details>

=== Uniqueness of cardinality

The phrase "cardinality of a set" suggests that cardinality is an inherent
property of sets. But now we've defined "finite type" essentially as a tuple
where the cardinality is just one component. What's to prevent us from
putting a different number there, for the same underlying type?

We can prove that this cannot happen. Cardinality is unique: any two finiteness
proofs for the same type must yield the same cardinality.

(The proof is a little tedious and technical.)

```alectryon
Theorem card_unique {A} (F1 F2 : is_finite A) : card F1 = card F2.
Admitted. (* Intermediate exercise *)
```

A slightly more general result is that isomorphic types (*i.e.*, related by
a bijection) have the same cardinality. It can first be proved
in terms of `is_finite`, from which a corollary in terms of `finite_type`
follows.

```alectryon
Theorem card_bijection {A B} (FA : is_finite A) (FB : is_finite B)
  : (A <--> B) -> card FA = card FB.
Admitted. (* Like card_unique *)

Theorem card_bijection_finite_type {A B : finite_type}
  : (A <--> B) -> #|A| = #|B|.
Proof.
  apply card_bijection.
Qed.
```

The converse is also true and useful: two types with the same cardinality are
isomorphic.

```alectryon
Theorem bijection_card {A B} (FA : is_finite A) (FB : is_finite B)
  : card FA = card FB -> (A <--> B).
Admitted. (* Easy exercise *)

Theorem bijection_card_finite_type {A B : finite_type}
  : #|A| = #|B| -> (A <--> B).
Proof.
  apply bijection_card.
Qed.
```

== Operations on finite sets

=== Sum

The sum of sets is also known as the disjoint union.

```coq
Inductive sum (A B : Type) : Type :=
| inl : A -> A + B
| inr : B -> A + B
where "A + B" := (sum A B) : type_scope.
```

`sum` is a binary operation on types. We must work to
make it an operation on finite types.

There is a bijection between `fin n + fin m` (sum of sets)
and `fin (n + m)` (sum of nats).

```alectryon
Definition bijection_sum_fin {n m} : fin n + fin m <--> fin (n + m).
Admitted. (* Intermediate exercise *)
```

The sum is a bifunctor.

```alectryon
Definition bijection_sum {A A' B B'}
  : (A <--> B) -> (A' <--> B') -> (A + A' <--> B + B').
Admitted. (* Easy exercise *)
```

Combining those facts, we can prove that the sum of two finite sets is finite (`finite_sum`),
and the cardinality of the sum is the sum of the cardinalities (`card_sum`).

```alectryon
Definition is_finite_sum {A B} (FA : is_finite A) (FB : is_finite B)
  : is_finite (A + B) :=
  {| card := #|FA| + #|FB|
  ;  enum := bijection_sum (enum FA) (enum FB) >>> bijection_sum_fin |}.

Definition finite_sum (A B : finite_type) : finite_type :=
  {| ft_type := A + B ; ft_is_finite := is_finite_sum A B |}.

Infix "+" := finite_sum : fintype_scope.
```

```alectryon
Theorem card_sum {A B : finite_type} : #|(A + B)%fintype| = #|A| + #|B|.
Proof.
  reflexivity.
Qed.
```

=== Product

The cartesian product has structure dual to the sum.

```coq
Inductive prod (A B : Type) : Type :=
| pair : A -> B -> A * B
where "A * B" := (prod A B) : type_scope.
```

- There is a bijection `fin n * fin m <--> fin (n * m)`.
- The product is a bifunctor.
- The product of finite sets is finite.
- The cardinality of the product is the product of the cardinalities.

<details>
  <summary>Coq code</summary>
```alectryon
Definition bijection_prod_fin {n m} : fin n * fin m <--> fin (n * m).
Admitted. (* Intermediate exercise *)

Definition bijection_prod {A A' B B'}
  : (A <--> B) -> (A' <--> B') -> (A * A' <--> B * B').
Admitted. (* Easy exercise *)

Definition is_finite_prod {A B} (FA : is_finite A) (FB : is_finite B)
  : is_finite (A * B) :=
  {| card := #|FA| * #|FB|
  ;  enum := bijection_prod (enum FA) (enum FB) >>> bijection_prod_fin |}.

Definition finite_prod (A B : finite_type) : finite_type :=
  {| ft_type := A * B ; ft_is_finite := is_finite_prod A B |}.

Infix "*" := finite_prod : fintype_scope.

Theorem card_prod {A B : finite_type} : #|(A * B)%fintype| = #|A| * #|B|.
Proof.
  reflexivity.
Qed.
```
</details>

= Sets as predicates

Two other common operations on sets are union and intersection.
However, those operations don't fit in the view of sets as types.
While set membership `x ∈ X` is a proposition, type inhabitation `x : X` is
a judgement, which is a completely different thing,[^judge] so we need a different
approach.

[^judge]: ... if you know what those words mean.

The idea of set membership `x ∈ X` as a proposition presumes that `x`
and `X` are entities that exist independently of each other. This suggests
that there is some "universe" that elements `x` live in, and the
sets `X` under consideration are subsets of that same universe.
We represent the universe by a type `A`, and sets (*i.e.*, "subsets of the universe")
by predicates on `A`.

```alectryon
Definition set_of (A : Type) := (A -> bool).
```

Hence, if `x : A` is an element of the universe, and `X : set A` is a set
(subset of the universe), we will denote set membership `x ∈ X` simply as `X x`
(`x` satisfies the predicate `X`).

Those predicates are boolean, *i.e.*, decidable. This is necessary in several
constructions and proofs here, notably to prove that the union or intersection
of finite sets is finite. We rely on a coercion to implicitly convert booleans
to `Prop`: `is_true : bool >-> Prop`, which is exported by `ssreflect`.

== Union, intersection, complement

Those common set operations correspond to the usual logical connectives.

```alectryon
Section Operations.

Context {A : Type}.

Definition union' (X Y : set_of A) : set_of A := fun a => X a || Y a.
Definition intersection' (X Y : set_of A) : set_of A := fun a => X a && Y a.
Definition complement' (X : set_of A) : set_of A := fun a => negb (X a).

End Operations.
```

Define the familiar infix notation for union and intersection.

```alectryon
Declare Scope set_of_scope.
Delimit Scope set_of_scope with set_of.
Bind Scope set_of_scope with set_of.

Infix "∪" := union' (at level 40) : set_of_scope.
Infix "∩" := intersection' (at level 40) : set_of_scope.
```

== Finiteness

Again, we will characterize finite sets using bijections to `fin n`.
We first transform the set `X` into a type `to_type X`, so we can form
the type of bijections `to_type X <--> fin n`. Like `fin`, we define
`to_type A` as a sigma type. Thanks to the predicate `X` being boolean,
there is at most one proof `p : X a` for each `a`, so the type
`{ a : A | X a }` has exactly one inhabitant for each inhabitant `a : A`
satisfying `X a`.

```alectryon
Definition to_type {A : Type} (X : set_of A) : Type := { a : A | X a }.

Coercion to_type : set_of >-> Sortclass.
```

We obtain a notion of finite set by imitating the structure of `finite_type`.
The set-as-predicate `X` is finite if the set-as-type `to_type X` is finite.

```alectryon
Record finite_set_of (A : Type) : Type :=
  { elem_of :> set_of A
  ; fso_is_finite :> is_finite (to_type elem_of)
  }.
```

Similarly, a `finite_type_of` can be coerced to a `finite_type`.

```alectryon
Definition to_finite_type {A} (X : finite_set_of A) : finite_type :=
  {| ft_type := elem_of X
  ;  ft_is_finite := X |}.

Coercion to_finite_type : finite_set_of >-> finite_type.
```

== Finite unions and intersections

We then prove that the union and intersection of finite sets are finite.
This is actually fairly challenging, since proving finiteness means to
calculate the cardinality of the set and to construct the associated
bijection. Unlike sum and product, there is no simple formula for the
cardinality of union and intersection. One candidate may seem to be the binary
inclusion-exclusion formula:

```
#|X ∪ Y| = #|X| + #|Y| - #|X ∩ Y|
```

But that only gives the cardinality of the union in terms of the intersection,
or vice versa, and we don't know either yet.

Rather than constructing the bijections directly, we decompose the proof.
The intuition is that `X ∪ Y` and `X ∩ Y` can easily be "bounded" by known
finite sets, namely `X + Y` and `X` respectively. By "bounded", we mean that
there is an injection from one set to the other.

The standard definition of injectivity is via an implication
`f x = f y -> x = y`. However, a better definition for our purposes
comes from a one-sided inverse property: a function `f : A -> B` is
a section if there exists another function `g : B -> A` (called a retraction)
such that `g (f x) = x`.
Every section is an injection, but the converse requires the law of excluded
middle.

```alectryon
Record is_section {A B} (to : A -> B) (from : B -> A) : Prop :=
  { s_from_to : forall a, from (to a) = a }.

Record section (A B : Type) : Type :=
  { s_from : A -> B
  ; s_to : B -> A
  ; s_is_section : is_section s_from s_to }.
```

The point is that, given a section to a finite set, `section A (fin n)`,
we can construct a bijection `A <--> fin m` for some `m`, that is smaller than
`n`. We formalize this result with a proof-relevant sigma type.

```alectryon
Definition section_bijection (A : Type) (n : nat)
  : section A (fin n) -> { m & A <--> fin m }.
Admitted. (* Hard exercise *)
```

This construction is rather involved. It is much more general than when we
were looking specifically at union and intersection, but at the same time it
is easier to come up with as it abstracts away the distracting details of those
operations.

Now there is a section from `X ∪ Y` to `X + Y`,
and from `X ∩ Y` to `X`.

```alectryon
Definition section_union {A} (X Y : set_of A)
  : section (X ∪ Y)%set_of (X + Y).
Admitted. (* Easy exercise *)

Definition section_intersection {A} (X Y : set_of A)
  : section (X ∩ Y)%set_of X.
Admitted. (* Easy exercise *)
```

We can then rely on the finiteness of `X` and `X + Y` to extend those
sections to `fin n` for some `n` via the following theorem:

```alectryon
Theorem section_extend (A B C : Type)
  : section A B -> (B <--> C) -> section A C.
Admitted. (* Easy exercise *)

Definition section_union' {A} (X Y : finite_set_of A)
  : section (X ∪ Y)%set_of (fin (#|X| + #|Y|)).
Proof.
  eapply section_extend.
  - apply section_union.
  - apply is_finite_sum.
Qed.

Definition section_intersection' {A} (X Y : finite_set_of A)
  : section (X ∩ Y)%set_of (fin #|X|).
Proof.
  eapply section_extend.
  - apply section_intersection.
  - apply enum.
Qed.
```

Finally, by `section_bijection`, we obtain finiteness proofs of `union'` and
`intersection'`, which let us define `union` and `intersection` properly as operations
on finite sets.


```alectryon
Theorem is_finite_union {A} {X Y : set_of A}
    (FX : is_finite X) (FY : is_finite Y)
  : is_finite (X ∪ Y)%set_of.
Proof.
  refine {| enum := projT2 (section_bijection _) |}.
  eapply (section_extend (B := X + Y)%type).
  - apply section_union.
  - apply (is_finite_sum FX FY).
Qed.

Theorem is_finite_intersection {A} {X Y : set_of A}
    (FX : is_finite X) (FY : is_finite Y)
  : is_finite (X ∩ Y)%set_of.
Proof.
  refine {| enum := projT2 (section_bijection _) |}.
  eapply section_extend.
  - apply section_intersection.
  - apply (enum FX).
Qed.

Definition union {A} (X Y : finite_set_of A) : finite_set_of A :=
  {| fso_is_finite := is_finite_union X Y |}.

Definition intersection {A} (X Y : finite_set_of A) : finite_set_of A :=
  {| fso_is_finite := is_finite_intersection X Y |}.
```

```alectryon
Declare Scope fso_scope.
Delimit Scope fso_scope with fso.
Bind Scope fso_scope with finite_set_of.

Infix "∪" := union (at level 40) : fso_scope.
Infix "∩" := intersection (at level 40) : fso_scope.
```

Hereafter, `∪` and `∩` will denote finite unions and intersections.

```alectryon
#[local] Open Scope fso_scope.
```

= Inclusion-exclusion

```
#|X ∪ Y| = #|X| + #|Y| - #|X ∩ Y|
```

To prove that formula, it's probably not a good idea to look at how `∪` and `∩`
compute their cardinalities. A better idea is to construct a bijection, which
implies an equality of cardinalities by `card_bijection`.

To start, subtractions are bad, so we rewrite the goal:

```
#|X ∪ Y| + #|X ∩ Y| = #|X| + #|Y|
```

Now we look for a bijection `(X ∪ Y) + (X ∩ Y) <--> X + Y`.
It gets a bit tricky because of the dependent types.

```alectryon
Definition inclusion_exclusion_bijection {A} (X Y : finite_set_of A)
  : (X ∪ Y)%set_of + (X ∩ Y)%set_of <--> X + Y.
Admitted. (* Hard exercise *)
```

Isomorphic sets have the same cardinality (by theorem `card_bijection_finite_type`).
The resulting equation simplifies to the binary inclusion-exclusion identity,
because `#|A + B|` equals `#|A| + #|B|` definitionally.
So the proof consists simply of applying that theorem with the above bijection.

```alectryon
Theorem inclusion_exclusion {A} (X Y : finite_set_of A)
  : #|X ∪ Y| + #|X ∩ Y| = #|X| + #|Y|.
Proof.
  apply (@card_bijection_finite_type ((X ∪ Y) + (X ∩ Y)) (X + Y)).
  apply inclusion_exclusion_bijection.
Qed.
```

Conclusion
==========

To formalize mathematics, it's often useful to revisit our preconceptions about
fundamental concepts. To carry out even basic combinatorics in type theory, it's
useful to distinguish two views of the naive notion of set.

For example, when we say "union", we really mean one of two things depending on
the context. Either the sets are obviously disjoint, so we really mean "sum":
this corresponds to viewing sets as types. Or we implicitly know that the two
sets contain the same "type" of elements a priori, so the overlap is something
we have to worry about explicitly: this corresponds to viewing sets as
predicates on a given universe.
