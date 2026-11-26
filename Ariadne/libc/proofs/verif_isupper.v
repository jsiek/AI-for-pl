Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import Libc.isupper Libc.spec_isupper.

Definition Gprog : funspecs := ltac:(with_library prog [ isupper_spec ]).

Lemma body_isupper : semax_body Vprog Gprog f_isupper isupper_spec.
Proof.
  start_function.
  forward.
  Exists (Int.repr (if Int.ltu (Int.sub (Int.repr c) (Int.repr 65)) (Int.repr 26) then 1 else 0)).
  entailer!.
Qed.
