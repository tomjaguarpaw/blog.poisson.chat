(* Free applicative functors *)

Implicit Type f : Type -> Type.
Implicit Type a b c : Type.

(* Same as https://hackage.haskell.org/package/free-5.1.1/docs/Control-Applicative-Free.html *)
Inductive Free f a : Type :=
| Pure : a -> Free f a
| Ap {b} : f b -> Free f (b -> a) -> Free f a
.

Arguments Pure {f a}.
Arguments Ap {f a b}.

(* [Free f] is a functor. *)

Fixpoint map {f a b} (h : a -> b) (ts0 : Free f a) : Free f b :=
  match ts0 with
  | Pure x => Pure (h x)
  | Ap t ts => Ap t (map (fun i x => h (i x)) ts)
  end.

Theorem map_id {f a} (ts : Free f a)
  : map (fun x => x) ts = ts.
Proof.
  induction ts; cbn.
  - reflexivity.
  - change (fun i x => i x) with (fun i : b -> a => i).
    rewrite IHts. reflexivity.
Qed.

Theorem map_map {f a b c} (h : a -> b) (i : b -> c) (ts : Free f a)
  : map i (map h ts) = map (fun x => i (h x)) ts.
Proof.
  revert b c h i.
  induction ts; cbn; intros.
  - reflexivity.
  - rewrite IHts. reflexivity.
Qed.

(* [Free f] is an applicative functor. *)
(* We focus on associativity. *)

Fixpoint liftA2 {f a b c} (h : a -> b -> c) (ts0 : Free f a) (us : Free f b) : Free f c :=
  match ts0 with
  | Pure x => map (h x) us
  | Ap t ts => Ap t (liftA2 (fun i y z => h (i z) y) ts us)
  end.

(* [eq]ual functions produce [eq]ual results. Useful to apply both sides of an
 * equality to a common argument. *)
Lemma funeq {A B} {h k : A -> B} (x : A) :
  h = k -> h x = k x.
Proof.
  intros []; reflexivity.
Qed.

(* Two "naturality" properties: [liftA2] "merges" with [map]. *)

Theorem liftA2_map {f a1 a2 b c}
  (h : a1 -> b) (i : b -> a2 -> c)
  (ts : Free f a1) (us : Free f a2)
  : liftA2 i (map h ts) us = liftA2 (fun x => i (h x)) ts us.
Proof.
  revert a2 b c h i us.
  induction ts; cbn; intros.
  - reflexivity.
  - f_equal. apply IHts.
Qed.

Theorem map_liftA2 {f a1 a2 b c}
  (h : b -> c) (i : a1 -> a2 -> b)
  (ts : Free f a1) (us : Free f a2)
  : map h (liftA2 i ts us) = liftA2 (fun x y => h (i x y)) ts us.
Proof.
  revert a2 b c h i us.
  induction ts; cbn; intros.
  - rewrite map_map. reflexivity.
  - f_equal. apply IHts.
Qed.

(* Associativity of [liftA2]. *)
Theorem liftA2_liftA2 {f a1 a2 a3 b12 b23 c}
  (h : a1 -> a2 -> b12) (i : b12 -> a3 -> c)
  (j : a1 -> b23 -> c) (k : a2 -> a3 -> b23)
  (ts : Free f a1) (us : Free f a2) (vs : Free f a3)
  : forall (hyp_1 : (fun x y => i (h x y)) = (fun x y z => j x (k y z))),
    liftA2 i (liftA2 h ts us) vs = liftA2 j ts (liftA2 k us vs).
Proof.
  revert a2 a3 b12 b23 c h i j k us vs.
  induction ts as [? x | ]; cbn; intros.
  - rewrite map_liftA2, liftA2_map. f_equal. apply (funeq x hyp_1).
  - f_equal. apply IHts.
    apply (@f_equal _ _ (fun k (x : b -> a) y2 y3 z => k (x z) y2 y3) _ _ hyp_1).
Qed.

(* An alternative statement of associativity. *)
Theorem liftA2_liftA2_simple {f a1 a2 a3 b12 c}
  (h : a1 -> a2 -> b12) (i : b12 -> a3 -> c)
  (ts : Free f a1) (us : Free f a2) (vs : Free f a3)
  : liftA2 i (liftA2 h ts us) vs
  = liftA2 (fun x yz => i (h x (fst yz)) (snd yz)) ts (liftA2 pair us vs).
Proof.
  (* One-line proof using [liftA2_liftA2]. *)
  apply liftA2_liftA2; auto; fail. (* [fail] is not reached because the goal is proved. *)
Restart.
  (* Proof from scratch. *)
  revert a2 a3 b12 c h i us vs.
  induction ts as [? x | ]; cbn; intros.
  - rewrite map_liftA2, liftA2_map. reflexivity.
  - f_equal. apply IHts.
Qed.

Definition snocpair {a b c} : (a * b) -> c -> (a * b * c) :=
  fun xy z => (fst xy, snd xy, z).

Definition conspair {a b c} : a -> (b * c) -> (a * b * c) :=
  fun x yz => (x, fst yz, snd yz).

(* Yet another one. *)
Theorem liftA2_liftA2_tuple {f a1 a2 a3 b12 c}
  (ts : Free f a1) (us : Free f a2) (vs : Free f a3)
  : liftA2 snocpair (liftA2 pair ts us) vs
  = liftA2 conspair ts (liftA2 pair us vs).
Proof.
  apply liftA2_liftA2; auto.
Qed.

(* Definition of [ap] from [liftA2]. *)
Definition ap {f a b} : Free f (a -> b) -> Free f a -> Free f b :=
  liftA2 (fun k x => k x).

Infix "<*>" := ap (at level 40, left associativity).

(* Associativity of [ap], also called "composition":
   https://hackage.haskell.org/package/base-4.12.0.0/docs/Control-Applicative.html
*)
Lemma ap_ap {f a b c} (ts : Free f (b -> c)) (us : Free f (a -> b)) (vs : Free f a)
  : map (fun k h x => k (h x)) ts <*> us <*> vs = ts <*> (us <*> vs).
Proof.
  unfold ap.
  rewrite liftA2_map.
  apply liftA2_liftA2.
  reflexivity.
Qed.

(* Unprovable variant of [liftA2_liftA2]. *)
Theorem almost_liftA2_liftA2 {f a1 a2 a3 b12 b23 c}
  (h : a1 -> a2 -> b12) (i : b12 -> a3 -> c)
  (j : a1 -> b23 -> c) (k : a2 -> a3 -> b23)
  (ts : Free f a1) (us : Free f a2) (vs : Free f a3)

  : forall (hyp_0 : forall x y z, i (h x y) z = j x (k y z)),

    liftA2 i (liftA2 h ts us) vs = liftA2 j ts (liftA2 k us vs).
Abort. (* Not provable *)
