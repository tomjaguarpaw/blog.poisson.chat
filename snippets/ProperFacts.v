(* Some proofs associated with the blogpost The pro-PER meaning of "proper" *)

From Coq Require Import Morphisms.

#[local] Open Scope signature_scope.

Class PER {A} (R : A -> A -> Prop) : Prop :=
  { PER_symmetry :> Symmetric R
  ; PER_transitivity :> Transitive R
  }.

Theorem Prim_and_Proper {A} (R : A -> A -> Prop) :
  PER R ->
  forall x, (R x x <-> exists y, R x y).
Proof.
  intros per x. split.
  - exists x; auto.
  - intros []; etransitivity; [ | symmetry ]; eauto.
Qed.

(* If `RD` and `RC` are PERs, then `RD ==> RC` is a PER on `D -> C` *)
Theorem respectful_PER {D C} (RD : D -> D -> Prop) (RC : C -> C -> Prop)
  : PER RD -> PER RC -> PER (RD ==> RC).
Proof.
  intros PERD PERC. constructor.
  - intros f g Ef x y Ex. symmetry; apply Ef; symmetry; apply Ex.
  - intros f g h Ef Eh x y Ex. etransitivity.
    + eapply Ef, Ex.
    + eapply Eh. apply (Prim_and_Proper _ _). exists x; symmetry; auto.
Qed.

Arguments pointwise_relation {A} {B}.

Notation pr := pointwise_relation.

Theorem pointwise_respectful {D C} (RD : D -> D -> Prop) (RC : C -> C -> Prop)
  : Reflexive RD -> Transitive RC ->
    forall f g, Proper (RD ==> RC) f -> Proper (RD ==> RC) g ->
    pointwise_relation RC f g <-> (RD ==> RC) f g.
Proof.
  intros REFL TRANS f g Hf Hg. split.
  - intros Hfg x y Exy.
    etransitivity; [ apply Hfg | apply Hg, Exy ].
  - intros Hfg x.
    apply Hfg; reflexivity.
Qed.

Definition compose {E D C} (f : D -> C) (g : E -> D) : E -> C :=
  fun x => f (g x).

Theorem not_Proper_compose :
  not
   (forall {E D C}
           (RD : D -> D -> Prop) (RC : C -> C -> Prop),
    Proper (pr RC ==> pr RD ==> pr RC)
           (compose (E := E))).
Proof.
  intros CONTRA.
  specialize (CONTRA bool bool bool (fun _ _ => True) eq (fun x => x) (fun x => x) (fun _ => eq_refl) (fun x => x) negb (fun _ => I) true).
  cbv in CONTRA. discriminate.
Qed.

Instance Proper_compose' {E D C} (RE : E -> E -> Prop)
    (RD : D -> D -> Prop) (RC : C -> C -> Prop) :
    Proper ((RD ==> RC) ==> (RE ==> RD) ==> (RE ==> RC))
           compose.
Proof.
  intros f f' Ef g g' Eg x y Ex.
  apply Ef, Eg, Ex.
Qed.

Definition RID (f g : forall A, A -> A) : Prop :=
  forall A (RA : A -> A -> Prop), (RA ==> RA) (f A) (g A).

(* If f satisfies its free theorem, then f is extensionally equal to the identity function. *)
Theorem unique_ID :
  forall f, RID f f ->
  forall A (x : A), f A x = x.
Proof.
  intros f PARAM A x.
  exact (PARAM A (fun x' _ => x' = x) x x eq_refl).
Qed.
