(* B1 side goals for SMTCoq.  Each goal is a pure fact that the VST
   proof of B1 (../b1/verif_b1.v) needs; there they are closed inside
   entailer!/forward_if (which call rep_lia/list_solve) or by
   discriminate/rewrite, never by a hand-written arithmetic proof.  Each
   is tried with the tactic VST uses (baseline) and SMTCoq's verit, cvc4
   and smt.  Output compared with expected_b1_side.txt by check.sh. *)
Require Import VST.floyd.proofauto.
(* SMTCoq exports its own `int` (Int63) and `val`, so CompCert's are
   written Int.int and Values.val below. *)
From SMTCoq Require Import SMTCoq.
Require Import SMT.Probe.
Require SMT.IntCompDec.  (* imported only in WithIntCompDec *)
From Stdlib Require String.  (* not imported: String.length *)
(* string_scope only for the probe labels; Z and list on top of it *)
Local Open Scope string_scope.
Local Open Scope Z_scope.
Local Open Scope list_scope.

Ltac smt_tacs n :=
  probe n "verit" ltac:(fun _ => verit);
  probe n "cvc4" ltac:(fun _ => cvc4);
  probe n "smt" ltac:(fun _ => smt).

(* Int.max_signed / Int.min_signed as numerals, as rep_lia sees them. *)
Ltac ints :=
  change Int.max_signed with 2147483647 in *;
  change Int.min_signed with (-2147483648) in *.

(* s1, loop 1 entry (verif_b1.v l.611: forward; Exists 0 nil; entailer!) *)
Goal forall n : Z, 0 <= n <= Int.max_signed -> 0 <= 0 <= n.
Proof. probe "s1" "lia" ltac:(fun _ => (intros; lia)). smt_tacs "s1". Abort.

(* s2, loop 1 body to continue (l.628 entailer!) *)
Goal forall k n : Z, 0 <= k <= n -> k < n -> 0 <= k < n.
Proof. probe "s2" "lia" ltac:(fun _ => (intros; lia)). smt_tacs "s2". Abort.

(* s3, loop 1 increment k + 1 (l.629 entailer!) *)
Goal forall k n : Z, 0 <= k < n -> 0 <= k + 1 <= n.
Proof. probe "s3" "lia" ltac:(fun _ => (intros; lia)). smt_tacs "s3". Abort.

(* s4, k++ does not overflow (tc_nobinover in forward at l.629) *)
Goal forall k n : Z, 0 <= k < n -> n <= Int.max_signed ->
  Int.min_signed <= k + 1 <= Int.max_signed.
Proof.
  probe "s4" "rep_lia" ltac:(fun _ => (intros; rep_lia)).
  smt_tacs "s4".
  probe "s4" "ints;verit" ltac:(fun _ => (intros; ints; verit)).
  probe "s4" "ints;smt" ltac:(fun _ => (intros; ints; smt)).
Abort.

(* s5, input[k] is in bounds (l.625 forward: Znth k contents) *)
Goal forall (contents : list Int.int) (k n : Z),
  Zlength contents = n -> 0 <= k < n -> 0 <= k < Zlength contents.
Proof.
  probe "s5" "lia" ltac:(fun _ => (intros; lia)). probe "s5" "list_solve" ltac:(fun _ => (intros; list_solve)).
  smt_tacs "s5".
Abort.

(* s6, length of the array contents (data_at of tarray tint n) *)
Goal forall (contents : list Int.int) (n : Z),
  Zlength contents = n -> Zlength (map Vint contents) = n.
Proof.
  probe "s6" "list_solve" ltac:(fun _ => (intros; list_solve)).
  smt_tacs "s6".
  probe "s6" "verit+Zlength_map" ltac:(fun _ => (verit (@Zlength_map Int.int Values.val Vint))).
Abort.

(* s7, the loop test k < n on Int.repr values (forward_if, l.614) *)
Goal forall k n : Z, 0 <= k <= n -> n <= Int.max_signed ->
  Int.signed (Int.repr k) = k.
Proof.
  probe "s7" "rep_lia" ltac:(fun _ => (intros; rewrite Int.signed_repr; rep_lia)).
  smt_tacs "s7".
  probe "s7" "ints;smt" ltac:(fun _ => (intros; ints; smt)).
Abort.

(* s8, a snoc is not nil (l.748 destruct a'; discriminate) *)
Goal forall (a : list (Values.val * Int.int)) (q : Values.val) (x : Int.int), a ++ [(q, x)] <> [].
Proof.
  probe "s8" "list_solve" ltac:(fun _ => (intros; list_solve)).
  probe "s8" "destruct" ltac:(fun _ => (intros; destruct a; discriminate)).
  smt_tacs "s8".
  probe "s8" "verit+app_cons_not_nil" ltac:(fun _ => (verit (@app_cons_not_nil (Values.val * Int.int)))).
Abort.

(* s9, the forward walk ends: s = s1 ++ [] (l.674 rewrite app_nil_r) *)
Goal forall s s1 : list (Values.val * Int.int), s = s1 ++ [] -> s = s1.
Proof.
  probe "s9" "list_solve" ltac:(fun _ => (intros; list_solve)).
  smt_tacs "s9".
  probe "s9" "verit+app_nil_r" ltac:(fun _ => (verit (@app_nil_r (Values.val * Int.int)))).
Abort.

(* s10, moving the walk's cursor (l.686 rewrite <- app_assoc) *)
Goal forall (s a b : list (Values.val * Int.int)) (q : Values.val) (x : Int.int),
  s = (a ++ [(q, x)]) ++ b -> s = a ++ (q, x) :: b.
Proof.
  probe "s10" "list_solve" ltac:(fun _ => (intros; list_solve)).
  smt_tacs "s10".
  probe "s10" "verit+app_assoc" ltac:(fun _ => (verit (@app_assoc (Values.val * Int.int)))).
Abort.

(* s8-s10 again over an abstract element type with SMTCoq's CompDec
   instance, to separate "list reasoning" from "no CompDec for val". *)
Section Abstract.
  Variable A : Type.
  Context {HA : CompDec A}.

  Goal forall (a : list A) (y : A), a ++ [y] <> [].
  Proof.
    smt_tacs "s8A".
    probe "s8A" "verit+app_cons_not_nil" ltac:(fun _ => (verit (@app_cons_not_nil A))).
  Abort.

  Goal forall s s1 : list A, s = s1 ++ [] -> s = s1.
  Proof.
    smt_tacs "s9A".
    probe "s9A" "verit+app_nil_r" ltac:(fun _ => (verit (@app_nil_r A))).
  Abort.

  Goal forall (s a b : list A) (y : A),
    s = (a ++ [y]) ++ b -> s = a ++ y :: b.
  Proof.
    smt_tacs "s10A".
    probe "s10A" "verit+app_assoc" ltac:(fun _ => (verit (@app_assoc A))).
  Abort.
End Abstract.

(* s5 and s6 again, with the CompDec instance for CompCert's Int.int
   from IntCompDec.v.  Without it, a symbol over list Int.int
   (Zlength contents) is outside what SMTCoq takes. *)
Section WithIntCompDec.
  Import SMT.IntCompDec.

  Goal forall (contents : list Int.int) (k n : Z),
    Zlength contents = n -> 0 <= k < n -> 0 <= k < Zlength contents.
  Proof. smt_tacs "s5I". Abort.

  Goal forall (contents : list Int.int) (n : Z),
    Zlength contents = n -> Zlength (map Vint contents) = n.
  Proof.
    smt_tacs "s6I".
    probe "s6I" "verit+Zlength_map"
      ltac:(fun _ => (verit (@Zlength_map Int.int Values.val Vint))).
  Abort.
End WithIntCompDec.
