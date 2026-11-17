(* Is VST 2.17's logic affine: can a proof drop owned memory (a
   data_at, a malloc_token) that the postcondition does not mention?
   Run from this directory (after clightgen on probe.c):
     ../../../vst/run.sh clightgen -normalize probe.c
     ../../../vst/run.sh coqc -native-compiler no -Q . Probe probe.v
     ../../../vst/run.sh coqc -native-compiler no -Q . Probe verif_probe.v
   The file compiles iff every `Fail` below fails as expected and the
   TT variants are proved.  Result (2026-11-17): VST 2.17 does not drop
   memory: at `return`, Floyd leaves `data_at .. |-- emp` (and
   `data_at_ .. * malloc_token .. |-- emp`), which no tactic proves
   (VST's emp, msl/predicates_sl.v line 111, holds only of a world that
   extends an identity element).  A postcondition that contains TT
   absorbs anything (msl/log_normalize.v line 796, sepcon_TT:
   P |-- P * TT), so leaks are possible exactly through TT (or another
   absorbing predicate) in a postcondition. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import Probe.probe.

#[export] Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.
Local Open Scope logic.

Definition t_node := Tstruct _node noattr.

Definition drop_int_spec :=
 DECLARE _drop_int
  WITH p: val
  PRE [ tptr tint ]
    PROP () PARAMS (p) SEP (data_at Ews tint (Vint Int.zero) p)
  POST [ tvoid ]
    PROP () RETURN () SEP ().

Definition drop_node_spec :=
 DECLARE _drop_node
  WITH p: val
  PRE [ tptr t_node ]
    PROP () PARAMS (p)
    SEP (data_at_ Ews t_node p; malloc_token Ews t_node p)
  POST [ tvoid ]
    PROP () RETURN () SEP ().

(* the same functions, with TT in the postcondition *)
Definition drop_int_TT_spec :=
 DECLARE _drop_int
  WITH p: val
  PRE [ tptr tint ]
    PROP () PARAMS (p) SEP (data_at Ews tint (Vint Int.zero) p)
  POST [ tvoid ]
    PROP () RETURN () SEP (TT).

Definition drop_node_TT_spec :=
 DECLARE _drop_node
  WITH p: val
  PRE [ tptr t_node ]
    PROP () PARAMS (p)
    SEP (data_at_ Ews t_node p; malloc_token Ews t_node p)
  POST [ tvoid ]
    PROP () RETURN () SEP (TT).

Definition Gprog : funspecs :=
  ltac:(with_library prog [drop_int_spec; drop_node_spec]).

(* 1. Without TT: the return leaves the cell, and nothing proves it. *)
Lemma body_drop_int: semax_body Vprog Gprog f_drop_int drop_int_spec.
Proof.
  start_function.
  forward.
  match goal with |- data_at Ews tint _ _ |-- emp => idtac end.
  Fail solve [entailer!].
  Fail solve [cancel].
  Fail solve [auto with core].
Abort.

Lemma body_drop_node: semax_body Vprog Gprog f_drop_node drop_node_spec.
Proof.
  start_function.
  forward.
  match goal with
  | |- data_at_ Ews t_node _ * malloc_token Ews t_node _ |-- emp => idtac
  end.
  Fail solve [entailer!].
  Fail solve [cancel].
Abort.

(* 2. With TT: proved. *)
Lemma body_drop_int_TT:
  semax_body Vprog Gprog f_drop_int drop_int_TT_spec.
Proof. start_function. forward. Qed.

Lemma body_drop_node_TT:
  semax_body Vprog Gprog f_drop_node drop_node_TT_spec.
Proof. start_function. forward. Qed.
