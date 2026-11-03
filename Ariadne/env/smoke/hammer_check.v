(* M0 smoke test: CoqHammer's ATP-backed hammer and its reconstruction
   tactics (sauto) both work in the image. *)
From Stdlib Require Import List.
From Hammer Require Import Tactics Hammer.
Import ListNotations.

Lemma app_nil_r' : forall (A : Type) (l : list A), l ++ [] = l.
Proof. induction l; sauto. Qed.

Lemma rev_length' : forall (A : Type) (l : list A),
  length (rev l) = length l.
Proof. hammer. Qed.
