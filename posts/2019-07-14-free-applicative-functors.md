---
title: Free applicative functors in Coq
keywords: [haskell, coq]
---

This is a long presentation of a short formalization of *free applicative
functors*. In summary, we prove the functor laws, and the associativity law of
applicative composition (or
["composition law"](https://hackage.haskell.org/package/base-4.12.0.0/docs/Control-Applicative.html)).

[The full Coq code is available here.](https://gist.github.com/Lysxia/548cd26205ee997f5642c9510d2a98a9)

The highlight of this formalization is that it is axiom-free, and the (only!)
two main functions are defined by simple structural induction, where previous
attempts[^faf] have relied on parametricity axioms and induction on an
auxiliary measure.
The proof scripts are short (5 lines each, 10 if you really like to spread out
tactics), and will be mostly omitted from this post.

[^faf]: Free Applicative Functors, by Paolo Capriotti and Ambrus Kaposi, in
MSFP 2014 ([arxiv](https://arxiv.org/abs/1403.0749)) (previously submitted to
ICFP 2013, to get the timeline right).

In spite of the apparent simplicity, the formalization involves crucial design
decisions that are detailed in this post, and making the wrong choice at
any point would jeopardize the highlighted features.

Admitting functional extensionality would certainly solve most of the
difficulties discussed here. It is perhaps the least controversial axiom to
admit, which also indicates that the subtleties at play may be hard to catch,
even by diving deep into the details. At any rate, I hope this will help to
better your understanding of the language Coq (or rather, Gallina), and
dependent types in general.

An important point to take away is that `=` in Coq (`eq`) is not "equality" as
we usually think of it. Deciding when to use `eq` or pointwise `eq` (or
something else) is a subtle balancing game, and even after the choice
is made and the proofs are done, it is perhaps still not clear what the
equalities mean.

---

The file starts with those two lines which mean that the variables
`f`, `a`, `b`, `c` have these types wherever they're bound.

```coq
Implicit Type f : Type -> Type.
Implicit Type a b c : Type.
```

= Free applicative functor

Here is the definition of the free applicative functor:

```coq
Inductive Free f a : Type :=
| Pure : a -> Free f a
| Ap {e} : f e -> Free f (e -> a) -> Free f a
.

(* Make the type arguments implicit. *)
Arguments Pure {f a}.
Arguments Ap {f a e}.
```

In other words, terms of type `Free f a` are lists of values `ti` of type `f ei`
with heterogeneous result types `ei` (i.e., each value can have a different
`ei`), terminated by a function which takes those results to produce a single
value `v`, of type `a`. Such a term looks like this, where `t1`, ..., `tn` are
terms, `x1`, ..., `xn` are variables to bind their results, and `v` is a term
which may use `x1`, ..., `xn`:

```coq
 Ap t1 (Ap t2 (... (Ap tn (Pure (
fun x1     x2  ...     xn => v))) ...))
```

== Comparison with other versions

This is the same definition as the "default" one [offered by the *free*
library](https://hackage.haskell.org/package/free-5.1.1/docs/Control-Applicative-Free.html)
by Edward Kmett in Haskell. The library also includes two other definitions
(`Free.Fast`, `Free.Final`) with much better asymptotic complexity.

Interestingly, the original paper which introduced
[free applicative functors](https://arxiv.org/abs/1403.0749),
by Paolo Capriotti and Ambrus Kaposi, mentions it first (under the name
`FreeAL`), but it is soon replaced with a different one (`FreeA`) where, in the
`Ap` constructor, the arrow type `b -> a` goes under `f` instead of `Free f`
(there is also a mostly inconsequential matter of left or right nesting):

```coq
Inductive FreeA f a : Type :=
| Pure : a -> FreeA f a
| Ap {b} : f (b -> a) -> FreeA f b -> FreeA f a
.
```

The reason given for choosing `FreeA` is that its `Functor` instance
(i.e., `fmap`) and `Applicative` instance (i.e., `pure` and, most importantly,
`(<*>)`) are easier to define. That is certainly the case for `fmap`,
since it doesn't need recursion, it simply peels off the first action
and uses the `Functor` instance of `f`. However, `ap` uses induction on size to
ensure termination; this complication is easily isolated on paper, but would
be exacerbated in Coq.

Furthermore, proving that `FreeA` is an applicative functor (i.e., it satisfies
the laws) requires an assumption of parametricity which sadly does not hold in
Coq. The conclusion of the paper explains this and one possible solution.
Another way would be to accept that `eq` is too fine a relation for this
purpose, and instead work with an ad-hoc but coarser notion of equivalence for
which the parametricity assumption is admissible, or even provable. Admittedly,
equivalence relations come with their own set of proof-engineering problems
down the line.

One more difference is that `Free` is *freer* than `FreeA`: `Free f` is an
applicative functor for any indexed type `f : Type -> Type`, not only functors.
It is the same difference as that between the "free monad" and
[the "freer monad"](http://okmij.org/ftp/Computation/free-monad.html)
(it's worth mentioning that both are free monads in the categorical sense, just
in different categories).
In Coq, `Free`, as opposed to `FreeA`, simplifies the formalization because
there is one fewer assumption to keep track of in proofs.

See also [Flavours of free applicative
functors](http://ro-che.info/articles/2013-03-31-flavours-of-free-applicative-functors.html),
by Roman Cheplyaka.

= Functor

As a warm up exercise, let's first show that `Free f` is a functor: we
implement `map : (a -> b) -> Free f a -> Free f b` and show that it commutes
with function composition.

The definition of `map` is straightforward. In the `Ap` case, the subterm
`ts : Free f (e -> a)` has a different type from the parameter
`ts0 : Free f a`, and that is taken care of by adapting the function argument
of `map`.

```coq
Fixpoint map {f a b} (h : a -> b) (ts0 : Free f a) : Free f b :=
  match ts0 with
  | Pure x => Pure (h x)
  | Ap t ts => Ap t (map (fun i x => h (i x)) ts)
  end.
```

As for the laws, there's two obvious ways to formulate them; only one leads
to provable statements.

If you look up a reference on category theory or [some other language's
documentation](https://hackage.haskell.org/package/base-4.12.0.0/docs/Data-Functor.html),
you'll find this:

```
     map id = id              (map_id_classic)
map (k ∘ h) = map k ∘ map h   (map_map_classic)
```

... with the usual definitions `id = (fun x => x)` and `k ∘ h = (fun x => k (h x))`.

It's a trap!

If we try to prove that, we are immediately stuck, there is simply no way
forward.

We can in fact show that no such proof exists, i.e., there are no *closed*
terms of type `map id = id`[^closed]. Terms in Coq have normal forms of the
same type (normalization and type preservation); the only possible closed
normal form of type `_ = _` is `eq_refl`, but for it to be well-typed the two
sides of the equality must be convertible[^convertible], and of course `map id`
is not convertible to `id`.
Note that the "closed term" assumption is key: we can prove nontrivial
equations by eliminating variables in the context, and this argument shows that
we're stuck if the context is empty.

That is a metalinguistic argument which cannot be carried out within Coq.
It would mean proving the negation of that equality, which cannot be
because that equality is in fact admissible. See also [this discussion of the
same topic on
SO](https://stackoverflow.com/questions/35157052/coq-identity-term-which-is-not-eq-refl).

[^closed]: `map id` hides some type arguments: `@map f a a id`,
so we're not actually in an empty context. This can be addressed with a longer
proof, or by specializing it `@map (fun x => x) nat nat id`, since a
general proof `map id = id` would imply this special case.

[^convertible]:
["Convertible"](https://coq.inria.fr/refman/language/cic.html#conversion-rules)
roughly means "β-equivalent", and anyone would understand if you use these
words as synonyms, but β is actually only a subset of convertibility. There are
more rules to unfold definitions and to handle constructs other than `fun`:
`match`, `let`, `fix`, `cofix`.

Those equations don't hold, does that mean `Free f` is not a functor? The
mismatch is actually in the notation `=`. When we write `=` on paper, we
pretend that there is such a thing as "equality" and that it has obvious
properties.
In mechanized formalization, the way I like to think about it is that there is
simply no canonical "equality". When we write `=` in Coq, it means `eq` by
default, an indexed type defined in Coq (i.e., not a primitive), and whether or
not it matches our mental picture of "equality" is a subjective matter.
Other definitions may also be worthy of the name "equality" depending on the
situation, and they don't even have to be expressible as types in Coq
(convertibility for example).
To take another language, Idris overloads the symbol `=` so it may denote
heterogeneous equality if the context requires it.
This cements my conviction that equality is merely a social construct.

So instead, we will show that the equations hold pointwise.
For all `u : Free f a`:

```
     map id u = u                 [map_id]
map (k ∘ h) u = map k (map h u)   [map_map]
```

Often, the `=` symbol on paper can be translated to an equivalence relation in
Coq, which has no reason to be `eq` a priori. In this case, we are interpreting
`=` from the original laws as pointwise `eq`, with its definition unfolded here.
It is also sometimes called *extensional equality for functions*, but that
terminology can become confusing when codomains of functions start carrying
their own relations, while "pointwise `eq`" is always precise.

```coq
Definition pointwise_eq {a b} (i j : a -> b) : Prop :=
  forall x, i x = j x.

Infix "=" := pointwise_eq : fun_scope.
Delimit Scope fun_scope with fun.
```

In Coq, we can redefine symbols such as `=`, which would allow us to write
something familiar like the following; the `%fun` annotations open a
scope in which `=` desugars to pointwise `eq` instead of plain `eq`:

```
     (map id = id)%fun              [map_id_pointwise]
(map (k ∘ h) = map k ∘ map h)%fun   [map_map_pointwise]
```

Looking at the categorical definition of a functor, once we reject "equality"
as a primitive notion, we have to review the very definition of a category,
which makes use of `=` ostensibly:

```
id ∘ k = k ∘ id = k
(i ∘ j) ∘ k = i ∘ (j ∘ k)
```

The definition of a category should now specify the equivalence relation
between arrows.[^2cat]
The definition of a functor also needs to be adjusted: it must not only
"commute with composition", it must also "preserve equivalences", although this
is trivial to prove if the domain category uses `eq` as the equivalence
relation.

[^2cat]: We're inches away from from 2-categories and higher category theory.

In this case, `map` makes `Free f : Type -> Type` a functor from the category
where objects are types, arrows are functions, and arrow equivalence is `eq`,
to the category with the same objects and arrows, but arrow equivalence is
`pointwise_eq`.

What if we change the domain category to also use `pointwise_eq` as the
equivalence relation? Things break again: `map` doesn't send pointwise-equal
functions to pointwise-equal functions.
Something fishy is going on, but let's postpone that for another day.

So much for warming up.

= Applicative

`Free` is a type of lists, [with a few
ornaments](https://personal.cis.strath.ac.uk/conor.mcbride/pub/OAAO/LitOrn.pdf).
In particular, `ap` is list concatenation, if we ignore the `a` and `b`
ornaments.

```
ap : Free f (a -> b) -> Free f a -> Free f b`,
```

That tells us the general shape of the function, but these ornaments still
matter a whole lot to the whole function.

Let's first try implementing `ap`. Here, by induction on `u`. In the `Pure`
case, we have `h : a -> b`, and `us : Free f a`, these types strongly hint at
`map`.

```coq
Fixpoint ap {f a b} (ts0 : Free f (a -> b)) (us : Free f a)
  : Free f b :=
  match ts0 with
  | Pure h => map h v
  | Ap t ts => Ap r _
  end.
```

The `Ap` case is puzzling... In the underscore (also called "typed hole"), we
expect to find `Free f (e -> b)`, for some fresh type `e` (which is the result
type of `r`). We have `ts : Free f (e -> a -> b)` and we can't directly apply
`ap` to it with `us : Free f a`. There is a cunning plan: we can flip `us` to
`map flip us : Free f (a -> e -> b)`, and `ap` that with `us`.

```coq
Definition flip {a b c} (f : a -> b -> c) : b -> a -> c :=
  fun x y => f y x.

Fixpoint ap {f a b} (ts0 : Free f (a -> b)) (us : Free f a)
  : Free f b :=
  match ts0 with
  | Pure h => map h v
  | Ap t ts => Ap t (ap (map flip ts) us)
  end.

(* But nope! *)
```

Nice try, but the `Fixpoint` police is watching: we can only `ap` to a subterm
of `ts0`, and `map flip ts` is not one. In the `match` branch with `Ap t ts`,
its subterms are `t` and `ts`. `t : f e` doesn't have the right type, so it
only makes sense to apply `ap` to `ts`, but we don't want to do that, which
leaves us right back where we started.

There are several workarounds, and I think the simplest one is to implement
`liftA2` instead.

```
liftA2 : (a -> b -> c) -> (Free f a -> Free f b -> Free f c)
```

The problem with `ap` was that it imposes a somewhat arbitrary structure on the
type indices of its arguments and result: `a -> b`, `a`, `b`. In contrast,
`liftA2` keeps the three indices loosely related through a separate function
`a -> b -> c`, so we have much more flexibility to write the recursive
application. Indeed, in the `Ap` case, the definition of `liftA2` follows the
structure of list concatenation (`++`, `app`) quite clearly, we only
need to fill the hole.

```
liftA2 h (Ap u us) vs = Ap u (liftA2 _ us vs)
   app (cons u us) vs = cons u (app us vs)
```

And the hole is uniquely determined by its context.

```coq
(* Given this context *)
h : a -> b -> c
============================= (* The Type-Tetris game *)
(e -> a) -> b -> (e -> c)
(* Implement that goal *)
```

This leads to the following definition:

```coq
Fixpoint liftA2 {f a b c}
    (h : a -> b -> c) (ts0 : Free f a) (us : Free f b)
  : Free f c :=
  match ts0 with
  | Pure x => map (h x) us
  | Ap t ts => Ap t (liftA2 (fun i y z => h (i z) y) ts us)
                            (* Type-Tetris here   *)
  end.
```

The `Ap` case doesn't need any call to `map`, that simplifies the
implementation, and thus the proofs.

== Applicative law: associativity

The most interesting applicative functor law here is the associativity law:

```
liftA2 _ (liftA2 _ ts us) vs = liftA2 _ ts (liftA2 _ us vs)
```

But what goes in the underscores? We will try different things. There are two
points to take into consideration for choosing the right theorem, they are
perhaps self-evident: the difficulty of the proof, and the generality of the
theorem. Despite appearances, these objectives don't necessarily conflict with
each other: the proof is most likely going to happen by induction over `ts`, so
some generalization is required to get a suitably strong induction hypothesis.
Often, that generalization is a perfectly fine theorem on its own: we get a
general theorem, and by design the first step of the proof is `induction`.

On one end of the spectrum, a first candidate is to put the results of `ts`,
`us`, and `vs` in tuples. The concreteness makes it easy to understand.

```
liftA2 snocpair (liftA2 pair ts us) vs
=
liftA2 conspair ts (liftA2 pair us vs)

[liftA2_liftA2_tuple]    <- name of the equation for reference

where
  pair = (fun x y => (x, y))
  snocpair = (fun '(x, y) z => (x, y, z))
  conspair = (fun x '(y, z) => (x, y, z))
```

Sadly, that doesn't pass the test of "is this a good induction hypothesis?".
Moreover, in practice most occurrences of `liftA2` in the wild don't use
`pair`, which makes that equation hard to apply. In that practical sense, it
lacks generality, although theoretically it is fully expressive in the presence
of a suitable "naturality lemma" which is useful to prove at any rate.

Another approach is to put variables in the left hand side, and then figure out
what right hand side matches.

```
liftA2 k (liftA2 h ts us) vs = liftA2 _ ts (liftA2 _ us vs)
```

On the right hand side, we need one function to combine the results of `us` and
`vs`, and another one to combine that with the result of `ts`.
There is very little to work with from the left hand side, which is unfortunate
because we are so constrained, but also fortunate because we are so
constrained. This looks like a canonical answer: wrap `us` and `vs` in a `pair`
so we can freely rearrange the results at the next level.

```
liftA2 k (liftA2 h ts us) vs
  = liftA2 (fun x '(y, z) => k (h x y) z) ts (liftA2 pair us vs)

[liftA2_liftA2_simple]
```

That is an easy proposition to prove by induction, modulo a few
details[^details]. Regarding generality, that equation also looks good because
it can be used to rewrite any expression with two left-associated `liftA2` into
a right-associated one.
By now it's clear I am nitpicky about this stuff: what about right-to-left
rewriting?

[^details]: Instead of pattern-matching on the pair, one should use projections
`fst` and `snd`.

=== A symmetric formulation

Symmetry is often something worth pondering in mathematics, both in ideas and
in notations. It's not necessarily bad to lack symmetry: `liftA2` does not have
a symmetric definition, privileging one *decreasing argument* `ts` over the
other `us`. Nevertheless, breaking or restoring symmetry can teach us new
insights.

In this case, a symmetric equation is obtained using different variables for
the function arguments on both sides.

```
liftA2 i (liftA2 h ts us) vs = liftA2 j ts (liftA2 k us vs)

[liftA2_liftA2]
```

Now, we need an extra assumption to relate `h`, `i`, `j`, `k`[^names].
From the structure of the above equation, or from the types of these functions,
it would be reasonable to suggest the following equation, for all `x`, `y`, and `z`:

```
i (h x y) z = j x (k y z)   [hyp_0]
```

[^names]: About the choice of variable names, these are the four letters after
`f` and `g`, which are already taken (of course `g` must be in the same
category as `f`); `h` looks like `k`, and `i` looks like `j`, so we can
fine-tune the symmetry further in notations; the alphabet is a fortunate thing
here.

So, the full theorem would look like this, to give you an idea of the actual
Coq code. Most of the space is taken by the signatures for the parameters, I
don't know whether we should be sad about it, but the last two lines are the
important ones.

```coq
Theorem almost_liftA2_liftA2 {f a1 a2 a3 b12 b23 c}
    (h : a1 -> a2 -> b12) (i : b12 -> a3 -> c)
    (j : a1 -> b23 -> c) (k : a2 -> a3 -> b23)
    (ts : Free f a1) (us : Free f a2) (vs : Free f a3)

  : forall (hyp_0 : forall x y z, i (h x y) z = j x (k y z)),

    liftA2 i (liftA2 h ts us) vs = liftA2 j ts (liftA2 k us vs).
```

Before `induction`, we should `revert` just about every parameter except `ts`
(actually, only about half of them, yet nothing goes wrong if there's more).
Such generalization is par for the course in formal proofs by induction.

We'll skip the base case (`ts = Pure x`), but suffice it to say that the gist
of it can be extracted into separate theorems about the interaction of `liftA2`
with `map`. I like to call them "naturality lemmas" because they show that
`liftA2` is a natural transformation (`map_liftA2`, `liftA2_map` in the Coq
source).

In the inductive case (`ts = Ap t ts'`), to use the induction hypothesis, we
instantiate `h`, `i` and `j` with a `fun` expression of *three* parameters,
as found in the definition of `liftA2`: `fun l y z => h (l z) y` (and replace
`h` with `i` and `j`, respectively); since all the functions in that
equation are applied to two arguments, we will be left with one `fun` on each
side. The induction hypothesis gives us the following obligation to prove, for
all `x'`, `y'`, `z'`:

```
(fun z0 => i (h (x' z0) y') z') = (fun z0 => j (x' z0) (k y' z'))
```

As you might have guessed, the `hyp_0` assumption, i.e.,
`i (h x y) z = j x (k y z)` (with `x := x' z0`, `y := y'`, `z := z'`),
cannot be applied to prove that.
Theoretically, the same argument as the one given earlier applies to
explain that no axiom-free proof is possible. Practically, we can see that the
subexpression we are trying to rewrite using `hyp_0` contains a bound variable,
`z0`. Indeed, the proof principle used for rewriting, which is a theorem
`m = n -> P m -> P n`, implicitly requires that the expressions `m` and `n`
have no variables bound in the "context" `P`.

With a lot of hand-waving, the idea is that the equation
`i (h x y) z = j x (k y z)` has too many free variables: to use that equation,
we must instantiate `x`, `y`, `z`, and the trouble starts when those
instantiations contain bound variables.
If that is indeed the problem, we can try to bind these variables so we don't
have to instantiate them. A normal reaction is to think that idea doesn't even
make sense. But hey, it works. Thus we bind `x`, `y`, and `z` with `fun` on
both sides we get the following equation `hyp_1` to replace `hyp_0`.

```
(fun x y z => i (h x y) z) = (fun x y z => j x (k y z))

[hyp_1]
```

Now this is the theorem we can actually prove.

```coq
Theorem liftA2_liftA2 {f a1 a2 a3 b12 b23 c}
    (h : a1 -> a2 -> b12) (i : b12 -> a3 -> c)
    (j : a1 -> b23 -> c) (k : a2 -> a3 -> b23)
    (ts : Free f a1) (us : Free f a2) (vs : Free f a3)

  : forall (hyp_1 : (fun x y => i (h x y)) = (fun x y z => j x (k y z))),

    liftA2 i (liftA2 h ts us) vs = liftA2 j ts (liftA2 k us vs).
```

After replaying the first steps of the proof, the goal given to us by the
induction hypothesis looks like this:

```
(fun x' y' z' z0 => i (h (x' z0) y') z')
=
(fun x' y' z' z0 => j (x' z0) (k y' z'))
```

At a glance, things don't look any better if you're used to thinking
that equations of the form `(fun ...) = (fun ...)` require functional
extensionality. But here we have specifically fixed our assumption `hyp_1` to
work around that. We only need to make the two functions of `hyp_1` appear in
the goal, which is a little exercise in β-expansion.

```
(fun x' y' z' z0 =>
  (fun x y z => i (h x y) z) (x' z0) y' z')
=
(fun x' y' z' z0 =>
  (fun x y z => j x (k y z)) (x' z0) y' z')
```

Actually, β-expansion in Coq can be tedious to do with tactics (I can't see a
concise way to do that, short of spelling out the desired goal). Instead, we
can manipulate the assumption `hyp_1` to obtain a proposition which β-reduces
to the goal. Start by representing the context common to both sides of the
β-expanded goal as a function:

```
fun l => (fun x' y' z' z0 => l (x' z0) y' z')
```

Then use the `f_equal` lemma to apply that function to both sides of `hyp_1`.
After β-reduction, we obtain exactly the goal.

```coq
  (* ... *)
  apply (@f_equal _ _ (fun l => (fun x' y' z' z0 => l (x' z0) y' z'))) in hyp_1.
  apply hyp_1.
Qed.


  (* Apply directly in the term and solve the goal with the result. *)
  apply (@f_equal _ _ (fun l => (fun x' y' z' z0 => l (x' z0) y' z')) _ _ hyp_1).
Qed.
```

The associativity of `liftA2` is now proved. Phew.

== Corollaries

The first two version of associativity we gave, `liftA2_liftA2_tuple` and
`liftA2_liftA2_simple`, are immediate corollaries of `liftA2_liftA2`: a proof
for both of them is literally `apply liftA2_liftA2; auto.`. The converse is not
difficult, but still a little less obvious. Although the statement of
`liftA2_liftA2` is not so easy to come up with, its proof is very similar to
the "more intuitive" `liftA2_liftA2_simple`.

Given `liftA2`, defining `ap` is as easy as `liftA2 (fun k x => k x)`,
and the associativity law expressed in terms of `ap` is a piece of cake using
`liftA2_liftA2` and naturality (`liftA2_map` in the source).

== What does the theorem really mean?

Hopefully I've made my point that `eq` is actually much stronger than it may
seem at first. The relation is hard to prove (e.g., `map id = id` is unprovable
when `=` is `eq`, but provable when `=` is `pointwise_eq`), and as an
assumption, for example `hyp_1`, it implies a lot.

Let's take another look at `hyp_1`. How might we prove such an equation, in
order to use `liftA2_liftA2`?

```
(fun x y z => i (h x y) z) = (fun x y z => j x (k y z))
```

The corollaries above provide some concrete examples. For example,
to prove `liftA2_liftA2_tuple`, we use the following instantiation.

```
i := fun xy z => (fst xy, snd xy, z)
j := fun x yz => (x, fst yz, snd yz)
h := fun x y => (x, y)   (* h = k = pair *)
k := fun x y => (x, y)
```

Then `hyp_1` simplifies to this, which is trivial by reflexivity.

```
(fun x y z => (x, y, z)) = (fun x y z => (x, y, z))
```

In fact, `reflexivity` is basically the only way to prove any
equation of the form `hyp_1`. Thus `hyp_1` could be said to be roughly an
encoding of the fact that `i (h x y) z` is *convertible* to `j x (k y z)`,
which flies in the face of the common wisdom that convertibility is not
expressible in Coq!

So `liftA2_liftA2` requires a "proof of convertibility", if we may say so,
which is quite a lot to ask for.
For example, setting all four of `i`, `j`, `h`, and `k` to
`add : nat -> nat -> nat`, i.e., `+` (or some other not-too-trivial associative
operation), we get this unprovable statement:

```
(fun x y z => (x + y) + z) = (fun x y z => x + (y + z))
```

As it turns out, the conclusion we would get from that with `liftA2_liftA2`
is also unprovable:

```
liftA2 add (liftA2 add ts us) vs = liftA2 add ts (listA2 add us vs)
```

Consequently, `liftA2_liftA2` makes a strong assumption which is not easily
weakened.

Still, programmers familiar with applicative functors would expect that last
equation above to hold: `liftA2 add` should be associative. When did we go
astray? The root of the problem is again `eq`. Our informal intuition
of "equality" is extensional. When are two `Free` computations the same? When
they perform the same actions and produce the same results.

Concretely, a `Free` term is a list of `Ap` nodes, terminated by a `Pure` node
holding a *function*.

```coq
 Ap t1 (Ap t2 (... (Ap tn (Pure (
fun x1     x2  ...     xn => v))) ...))
```

When we `eq`uate two such terms, such as we do above in the functor and
applicative laws, this implies `eq`uating the functions at the end of the
lists, and that spells trouble. It would be more intuitive to equate them
*pointwise*.

```
(fun x1 ... xn => v) = (fun x1 ... xn => w)   (* [eq]uality *)
forall x1 ... xn, v = w                       (* Pointwise [eq]uality *)
```

An extensional version of equality for `Free` terms is nontrivial to
define and prove to be an equivalence relation, but with it, we would be able
to show that `liftA2 add` is associative.

Introducing that relation opens up a whole new set of problems, especially
regarding what we mean when we say that `Free f` is an applicative functor
(the categories of interest are different), but let's stop at this because I
don't want to make this post much longer.

= Conclusion

To summarize the main results formalized in this post:

- the definition of the free applicative functor as an inductive type,
  which is the same as what can be found in existing literature and libraries,
  but in Coq;

- a proof that `Free f` is a functor, which made us refine the notion of
  categories to 2-categories;

- a definition of `liftA2` with a proof of its associativity, whose statement
  is not even obvious. From that we can derive `ap` and derive the laws in
  its terms.

However, that is not a complete demonstration that the "free applicative
functor" is worthy of the name. To finish it, the interested reader is invited
to investigate the following points:

- the identity laws of applicative functors;

- `Free` is indeed the *free* applicative functor: `Free` (not `Free f`) must
  be a functor satisfying a certain universal property.

---

Many thanks to Georgy Lukyanov for [the discussion on free applicative and
selective
functors](https://stackoverflow.com/questions/56942114/induction-on-a-datatype-with-non-uniform-type-parameters-produces-ill-typed-term)
which sparked this piece.
