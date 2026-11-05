(* Trust base: B1 side goals proved by SMTCoq with Qed, so the kernel
   re-checks SMTCoq's certificate checker run, then Print Assumptions.
   check.sh compares the output with expected_assumptions.txt. *)
Require Import VST.floyd.proofauto.
From SMTCoq Require Import SMTCoq.

(* s3, by veriT *)
Lemma s3_verit : forall k n : Z, 0 <= k < n -> 0 <= k + 1 <= n.
Proof. verit. Qed.

(* s4, by smt (veriT, then CVC4) after unfolding the Int bounds *)
Lemma s4_smt : forall k n : Z, 0 <= k < n -> n <= Int.max_signed ->
  Int.min_signed <= k + 1 <= Int.max_signed.
Proof.
  intros.
  change Int.max_signed with 2147483647 in *;
  change Int.min_signed with (-2147483648) in *.
  smt.
Qed.

(* s5, by veriT, with Zlength uninterpreted (needs CompDec Int.int) *)
Require Import SMT.IntCompDec.
Lemma s5_verit : forall (contents : list Int.int) (k n : Z),
  Zlength contents = n -> 0 <= k < n -> 0 <= k < Zlength contents.
Proof. verit. Qed.

Print Assumptions s3_verit.
Print Assumptions s4_smt.
Print Assumptions s5_verit.
