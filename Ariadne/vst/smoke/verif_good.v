(* VST proof of good.c: every function is verified (semax_body) and
   the whole program is verified (semax_prog).  Memory safety,
   including the absence of use after free, follows from VST's
   soundness theorem w.r.t. CompCert Clight semantics. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import Smoke.good.

#[export] Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.

Definition t_cell := Tstruct _cell noattr.

Definition use_cell_spec :=
 DECLARE _use_cell
  WITH gv: globals
  PRE [ ]
    PROP () PARAMS () GLOBALS (gv) SEP (mem_mgr gv)
  POST [ tint ]
    EX r: Z,
    PROP (r = 0 \/ r = 1) RETURN (Vint (Int.repr r)) SEP (mem_mgr gv).

Definition main_spec :=
 DECLARE _main
  WITH gv: globals
  PRE [ ] main_pre prog tt gv
  POST [ tint ]
    EX r: Z, PROP () RETURN (Vint (Int.repr r)) SEP (TT).

Definition Gprog : funspecs :=
  ltac:(with_library prog [use_cell_spec; main_spec]).

Lemma body_use_cell: semax_body Vprog Gprog f_use_cell use_cell_spec.
Proof.
  start_function.
  forward_call (t_cell, gv).            (* p = malloc(sizeof *p); *)
  Intros p.
  forward_if                            (* if (!p) return 0; *)
    (PROP () LOCAL (temp _p p; gvars gv)
     SEP (mem_mgr gv; malloc_token Ews t_cell p; data_at_ Ews t_cell p)).
  - if_tac; entailer!.
  - forward. Exists 0. entailer!.
  - if_tac.
    + subst p. contradiction.
    + forward. entailer!.
  - forward.                            (* p->value = 1; *)
    forward.                            (* p->next = NULL; *)
    forward.                            (* r = p->value; *)
    forward_call (t_cell, p, gv).       (* free(p); *)
    { assert_PROP (isptr p) by entailer!.
      rewrite if_false by (intro; subst; contradiction). cancel. }
    forward.                            (* return r; *)
    Exists 1. entailer!.
Qed.

Lemma body_main: semax_body Vprog Gprog f_main main_spec.
Proof.
  start_function.
  sep_apply (create_mem_mgr gv).
  forward_call gv.
  Intros r.
  forward.
  Exists r. entailer!.
Qed.

#[export] Existing Instance NullExtension.Espec.

Lemma prog_correct: semax_prog prog tt Vprog Gprog.
Proof.
  prove_semax_prog.
  semax_func_cons body_malloc. apply semax_func_cons_malloc_aux.
  semax_func_cons body_free.
  semax_func_cons body_use_cell.
  semax_func_cons body_main.
Qed.

Print Assumptions prog_correct.
