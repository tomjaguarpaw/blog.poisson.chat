Require Import List.
Import ListNotations.

Fixpoint reverse {A} (xs : list A) : list A :=
  match xs with
  | [] => []
  | x :: xs => reverse xs ++ [x]
  end.

Module DList.

Definition t (A : Type) := list A -> list A.

Definition empty {A : Type} : t A := id.
Definition singleton {A : Type} : A -> t A := cons.
Definition app {A : Type} (xs ys : t A) : t A := fun zs => xs (ys zs).
Definition to_list {A : Type} (xs : t A) : list A := xs [].

Definition rel {A} (xs : t A) (ys : list A) :=
  forall zs, xs zs = ys ++ zs.

Lemma p_empty {A} : @rel A empty nil.
Proof. cbv. reflexivity. Qed.

Lemma p_singleton {A} (a : A) : rel (singleton a) [a].
Proof. cbv. reflexivity. Qed.

Lemma p_app {A} (xs ys : t A) (xs' ys' : list A)
  : rel xs xs' ->
    rel ys ys' ->
    rel (app xs ys) (xs' ++ ys').
Proof.
  intros Hxs Hys zs.
  specialize (Hxs (ys zs)).
  specialize (Hys zs).
  rewrite <- app_assoc, <- Hys.
  apply Hxs.
Qed.

Lemma p_to_list {A} (xs : t A) (xs' : list A) :
  rel xs xs' -> to_list xs = xs'.
Proof. rewrite (app_nil_end xs') at 2; intros H; apply H. Qed.

End DList.

Delimit Scope app_scope with app.

Infix "++" := DList.app : app_scope.

Fixpoint reversed {A} (xs : list A) : DList.t A :=
  match xs with
  | [] => DList.empty
  | x :: xs => (reversed xs ++ DList.singleton x)%app
  end.

Definition reverse' {A} (xs : list A) : list A :=
  DList.to_list (reversed xs).

Lemma p_reversed {A} (xs : list A) : DList.rel (reversed xs) (reverse xs).
Proof.
  induction xs.
  - apply DList.p_empty.
  - cbn.
    apply DList.p_app; auto using DList.p_singleton.
Qed.

Theorem p_reverse' {A} (xs : list A) : reverse' xs = reverse xs.
Proof.
  apply DList.p_to_list, p_reversed.
Qed.
