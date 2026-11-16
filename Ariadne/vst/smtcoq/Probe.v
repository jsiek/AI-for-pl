(* probe g t k: runs the thunk k (k () is the tactic) on the goal and
   prints "OK g t" if it closes the goal within 60 s, else "NO g t".
   The goal is left unchanged (assert_succeeds), so several tactics can
   be tried on one goal.  The SMTCoq tactics used here (not the
   _no_check variants) run SMTCoq's certificate checker inside the
   tactic, so OK means the certificate was checked in Rocq. *)
Ltac probe g t k :=
  tryif assert_succeeds (timeout 60 (solve [k ()]))
  then idtac "OK" g t else idtac "NO" g t.
