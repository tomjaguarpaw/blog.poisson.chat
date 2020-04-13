Require Import List.
Import ListNotations.

(* Failure is isomorphic to True. *)
Inductive Failure : Prop := ERROR.

Definition list_unwrap {a} (xs : list a) (b : Type) : Type :=
  match xs with
  | [] => Failure
  | _ :: _ => b
  end.

Definition head {a} (xs : list a) : list_unwrap xs a :=
  match xs with
  | [] => ERROR
  | x :: _ => x
  end.

Definition tail {a} (xs : list a) : list_unwrap xs (list a) :=
  match xs with
  | [] => ERROR
  | _ :: xs => xs
  end.

Definition some_number : nat := head [1;2;3].
Compute some_number.
(* = 1 : nat *)

Definition some_list : list nat := tail [1;2;3].
Compute some_list.
(* = [2; 3] : list nat *)

Fail Definition not_a_number : nat := head [].
(* head []   has   actual type   Failure
                 expected type   nat *)

Definition option_unwrap {a} (ox : option a) (b : Type) : Type :=
  match ox with
  | None => Failure
  | Some _ => b
  end.

Definition fromSome {a} (ox : option a) : option_unwrap ox a :=
  match ox with
  | None => ERROR
  | Some x => x
  end.
