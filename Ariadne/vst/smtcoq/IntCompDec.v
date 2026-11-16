(* A CompDec instance for CompCert's Int.int (ordered by Int.unsigned).
   SMTCoq only takes symbols whose argument and result types have a
   CompDec instance; it ships ones for Z, nat, bool, positive, N, Int63,
   bit vectors, and list/prod/option of those, but not for CompCert's
   Int.int or Values.val. *)
Require Import VST.floyd.proofauto.
From SMTCoq Require Import SMTCoq.

Definition int_lt (x y : Int.int) : Prop :=
  Int.unsigned x < Int.unsigned y.

Lemma int_eqb_spec : forall x y, Int.eq x y = true <-> x = y.
Proof.
  intros x y. split; intro H.
  - generalize (Int.eq_spec x y). rewrite H. auto.
  - subst. apply Int.eq_true.
Qed.

Lemma int_lt_trans : forall x y z,
  int_lt x y -> int_lt y z -> int_lt x z.
Proof. unfold int_lt. lia. Qed.

Lemma int_lt_neq : forall x y, int_lt x y -> x <> y.
Proof. unfold int_lt. intros x y H ->. lia. Qed.

Definition int_compare (x y : Int.int) :
  OrderedType.Compare int_lt eq x y.
Proof.
  destruct (Z_dec (Int.unsigned x) (Int.unsigned y)) as [[H|H]|H].
  - apply OrderedType.LT. exact H.
  - apply OrderedType.GT. unfold int_lt. lia.
  - apply OrderedType.EQ.
    rewrite <- (Int.repr_unsigned x), <- (Int.repr_unsigned y), H.
    reflexivity.
Defined.

#[export] Instance Int_compdec : CompDec Int.int :=
  CompDec_from Int.int Int.eq int_eqb_spec int_lt int_lt_trans
    int_lt_neq int_compare Int.zero.
