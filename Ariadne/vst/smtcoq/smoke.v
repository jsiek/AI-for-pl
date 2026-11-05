(* SMTCoq smoke test: small goals over Z, bool, nat and lists, each
   tried with lia (baseline) and SMTCoq's verit, cvc4 and smt tactics
   (verit_bool for goals stated in bool).  The output lines are
   compared with expected_smoke.txt by check.sh. *)
From Stdlib Require Import String.  (* first, so List.length wins *)
From Stdlib Require Import ZArith Lia List Bool.
From SMTCoq Require Import SMTCoq.
Require Import SMT.Probe.
Import ListNotations.

(* string_scope only for the probe labels; Z and list on top of it *)
Local Open Scope string_scope.
Local Open Scope Z_scope.
Local Open Scope list_scope.

Ltac all_tacs n :=
  probe n "lia" ltac:(fun _ => (intros; lia));
  probe n "verit" ltac:(fun _ => verit);
  probe n "cvc4" ltac:(fun _ => cvc4);
  probe n "smt" ltac:(fun _ => smt).

(* ---- Z: linear arithmetic ---- *)
Goal forall x y : Z, x < y -> x + 1 <= y.
Proof. all_tacs "z1 lt_succ". Abort.

Goal forall x y z : Z, x <= y -> y <= z -> x <= z.
Proof. all_tacs "z2 trans". Abort.

Goal forall x y : Z, 0 <= x < y -> y <= 2147483647 ->
  -2147483648 <= x + 1 <= 2147483647.
Proof. all_tacs "z3 no_overflow". Abort.

(* nonlinear: outside QF_LIA *)
Goal forall x y : Z, 0 <= x -> 0 <= y -> 0 <= x * y.
Proof. all_tacs "z4 nonlinear". Abort.

(* uninterpreted function + arithmetic *)
Goal forall (f : Z -> Z) (x y : Z), x = y + 1 -> f y = f (x - 1).
Proof. all_tacs "z5 uf_lia". Abort.

(* ---- bool ---- *)
Goal forall a b c : bool,
  (a || b || c) && (negb a || negb b || negb c) && (negb a || b)
  && (negb b || c) && (negb c || a) = false.
Proof.
  all_tacs "b1 sat". probe "b1 sat" "verit_bool" ltac:(fun _ => verit_bool). Abort.

Goal forall x y : Z, (x <? y) = true -> (y <=? x) = false.
Proof.
  all_tacs "b2 Zltb". probe "b2 Zltb" "verit_bool" ltac:(fun _ => verit_bool). Abort.

Goal forall (a b : bool) (x : Z), (if a then x else x) = x.
Proof. all_tacs "b3 if". Abort.

(* ---- nat (Trakt casts nat into Z) ---- *)
Goal forall n m : nat, (n < m)%nat -> (S n <= m)%nat.
Proof. all_tacs "n1 nat_lt". Abort.

Goal forall n m : nat, (n + m = m + n)%nat.
Proof. all_tacs "n2 nat_comm". Abort.

(* ---- lists: length and ++ are uninterpreted for the solver ---- *)
Goal forall l1 l2 : list Z, l1 = l2 -> length l1 = length l2.
Proof. all_tacs "l1 congruence". Abort.

Goal forall (l : list Z) (x : Z), length (x :: l) = S (length l).
Proof. all_tacs "l2 length_cons". Abort.

(* needs length_app: given to verit/smt as a lemma *)
Goal forall l1 l2 l3 : list Z,
  length (l1 ++ l2 ++ l3) = (length l1 + length l2 + length l3)%nat.
Proof.
  all_tacs "l3 length_app".
  probe "l3 length_app" "verit+length_app" ltac:(fun _ => (verit (@length_app Z))).
  probe "l3 length_app" "smt+length_app" ltac:(fun _ => (smt (@length_app Z))).
Abort.

Goal forall (l : list Z) (x : Z), l ++ [x] <> [].
Proof.
  all_tacs "l4 snoc_nonnil".
  probe "l4 snoc_nonnil" "verit+app_cons_not_nil" ltac:(fun _ => (verit (@app_cons_not_nil Z))).
Abort.
