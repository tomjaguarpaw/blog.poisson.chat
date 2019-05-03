---
title: Formalization of Reynolds's parametricity theorem in Coq
keywords: [polymorphism, parametricity, theory, formalization, coq]
---

[I wrote a little formalization of parametricity in
Coq.](https://github.com/Lysxia/system-F)

One of my motivations was to experiment with dependent types in the
formalization of a programming language. I was pretty convinced that it is a
nice way of doing such things, but I had actually never tried it. System F
is particularly interesting in this regard, because terms can abstract over
both types and terms, which makes contexts rather richly structured (and a
system with kinds or dependent types would go even further).

== Well-typed by construction

Whereas a traditional formalization of programming languages would define
separate grammars for types and terms, and relate them via logical
predicates...

```coq
Inductive ty : Type := (* ... *).

Inductive tm : Type := (* ... *).

Definition well_typed : ty -> tm -> Prop.
```

... we can instead parameterize each syntactic category (types and terms) by
its contexts, thus obviating the need for separate predicates for typing
judgements. Terms are well-typed by construction.

```coq
Inductive ty (n : nat) : Type := (* ... *).

Inductive tm (n : nat) (vs : list (ty n)) : ty n -> Type := (* ... *).
```

Thanks to that, denotational semantics can be defined as actual functions in
Coq, with pretty straightforward definitions. No proof terms to decompose or
absurd cases to prove impossible, because they simply don't exist.

```coq
(** Semantics of terms of type [t] as Coq values *)
Definition eval_tm0 {t : ty 0} : tm0 t -> eval_ty0 t.
```

I really like this approach. Everything is tightly coupled, which means the
type checker will be in the way until every piece is right.
This has its pros and cons. In order to not get stuck on every small detail,
it is quite useful to postpone them into small unimplemented auxiliary
functions. An axiom `TODO : forall a, a.` is especially useful to type check
some branches of `match` without having to implement all of them.

In the end I think it works well for self-contained projects like this one,
where I already had a precise mental picture of what I wanted, but such heavily
dependently-typed programming definitely has a steep learning curve.
Things might be easier in other systems than Coq (Agda, Idris?), with better
environments for type-driven programming (I haven't tried).

Actually, I believe one can be quite proficient at formalizing things in Coq
without knowing anything about dependent types. A lot of work can be done by
writing implementations ("stuff that computes") only in a fragment of Coq
without dependent types (as a variant of ML), and while typical specifications
("stuff in `Prop`") are technically dependent types, the details are quite well
hidden behind the tactic system. So I think it's worth pointing out that, by
those standards, the heavy use of dependent types in Coq makes this project
quite an outlier.

== Dependently-typed structures

The whole project relies on native dependent pattern-matching, without help
from Program or [Equations](https://github.com/mattam82/Coq-Equations),
and for that to work well, *indexed types* are to be used very sparely.

For example, the type of length-indexed lists I use is a
function `nat -> Type` which unfolds to a sequence of nested pairs:

```coq
(** Length-indexed lists (aka "vectors") *)
Fixpoint lilist (A : Type) (n : nat) : Type :=
  match n with
  | O => unit
  | S n => A * lilist A n
  end.
```

In contrast, the standard library defines it naively as an indexed type (named
`Vector`):

```coq
Inductive lilist (A : Type) : nat -> Type :=
| nil : lilist A O
| cons {n : nat} : A -> lilist A n -> lilist A (S n)
.
```

Basically, the issue is that with indexed types, the information you
get by pattern-matching "flows" from the indexed type to its indices,
but in the case of structures like lists you often want things to flow in the
opposite way. This makes pattern-matching awkward, for example, when multiple
types depend on the same index (e.g., lists of the same length), or when the
index is meant to reflect partial information about the indexed type (e.g.,
non-empty lists, with length `S n`).

This experience with length-indexed lists suggests a more general pattern, as
an alternative to indexed types in various situations, which is strongly
reminiscent of
[*ornaments*](https://personal.cis.strath.ac.uk/conor.mcbride/pub/OAAO/LitOrn.pdf).

The only indexed type in this project is the type of terms, which is indexed
by their type. Intuitively, this might work because the type system is
syntax-directed.

== Parametricity

Of course, another motivation for this project was to get a better grasp on the
parametricity theorem and the idea of *Theorems for free!* by Philip Wadler,
to apply parametricity to prove things about specific programs.

A noteworthy detail here is that the interpretation of types as relations
cannot be done in naive set theory[^sets]. But in Coq (*a* type theory, I
guess?), a naive formulation is happily accepted. Having mechanized the result
serves to confirm my high-level intuition of it, even if I'm not entirely
familiar with those more foundational details.

[^sets]: [*Polymorphism is not set-theoretic*](https://hal.inria.fr/inria-00076261/),
  by John C. Reynolds, in Semantics of Data Types, 1984.

The next thing I want to look at now is the question of parametricity for
functors. There is a folklore result (maybe to be found in one of Janis
Voigtländer's papers) that parametricity implies in particular that polymorphic
functions `forall a. f a -> g a`, with functors `f` and `g`, are natural
transformations. But if we define "functor" as a synonym for "lawful definition
of `fmap :: forall a b. (a -> b) -> (f a -> f b)`", I can't see a
straightforward connection to parametricity, as opposed to a different
definition in terms of polarity, "`a` occurs only positively in `f a`". I can
imagine that the latter implies the former, but the converse might not be
provable.

I have been interested in parametricity for quite a while, but this particular
endeavor was sparked by [my other project](github.com/Lysxia/coq-mtl) of
formalizing [laws for the *mtl* Haskell
library](https://github.com/haskell/mtl/issues/5), which at the moment consists
in finding as many relations as I can between transformers and *mtl* classes.
In particular, to relate properties of `StateT` to those of `ReaderT` and
`WriterT`, I found that "naturality laws", which follow from parametricity,
were explicitly required. While writing a blogpost on *mtl* laws, the section
on naturality ended up growing into a post of its own on parametricity. And to
confirm that I knew what I was talking about there, I finally decided to
formalize those ideas in Coq.
