(* VST on bad.c: each proof runs the same steps as verif_good.v up to
   the line marked BAD, and there the next Floyd step must fail.
   `Fail tac` succeeds only if `tac` fails, so this file compiles
   exactly when VST refuses every bad step.  After `free(p)` the
   precondition no longer holds `data_at ... p` (free's spec consumed
   it), so there is nothing that licenses the access. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import Smoke.bad.

#[export] Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.

Definition t_cell := Tstruct _cell noattr.

(* All three functions get the same, satisfiable, specification. *)
Definition spec (f: ident) :=
 DECLARE f
  WITH gv: globals
  PRE [ ]
    PROP () PARAMS () GLOBALS (gv) SEP (mem_mgr gv)
  POST [ tint ]
    EX r: Z, PROP () RETURN (Vint (Int.repr r)) SEP (mem_mgr gv).

Definition Gprog : funspecs :=
  ltac:(with_library prog
    [spec _use_after_free; spec _write_after_free_alias;
     spec _double_free]).

Ltac malloc_nonnull gv :=
  forward_call (t_cell, gv);
  let p := fresh "p" in
  Intros p;
  forward_if
    (PROP () LOCAL (temp _p p; gvars gv)
     SEP (mem_mgr gv; malloc_token Ews t_cell p; data_at_ Ews t_cell p));
  [ if_tac; entailer!
  | forward; Exists 0; entailer!
  | if_tac; [ subst p; contradiction | forward; entailer! ]
  | ].

Lemma body_use_after_free:
  semax_body Vprog Gprog f_use_after_free (spec _use_after_free).
Proof.
  start_function.
  malloc_nonnull gv.
  forward.                              (* p->value = 1; *)
  forward.                              (* p->next = NULL; *)
  forward_call (t_cell, p, gv).         (* free(p); *)
  { assert_PROP (isptr p) by entailer!.
      rewrite if_false by (intro; subst; contradiction). cancel. }
  (* BAD: return p->value; *)
  Fail forward.
Abort.

Lemma body_write_after_free_alias:
  semax_body Vprog Gprog f_write_after_free_alias
    (spec _write_after_free_alias).
Proof.
  start_function.
  malloc_nonnull gv.
  forward.                              (* q = p; *)
  forward_call (t_cell, p, gv).         (* free(p); *)
  { assert_PROP (isptr p) by entailer!.
      rewrite if_false by (intro; subst; contradiction). cancel. }
  (* BAD: q->value = 2; *)
  Fail forward.
Abort.

Lemma body_double_free:
  semax_body Vprog Gprog f_double_free (spec _double_free).
Proof.
  start_function.
  malloc_nonnull gv.
  assert_PROP (isptr p) by entailer!.   (* keep p <> NULL in context *)
  forward_call (t_cell, p, gv).         (* free(p); *)
  { rewrite if_false by (intro; subst; contradiction). cancel. }
  (* BAD: free(p); -- the second call's precondition needs
     malloc_token * data_at_ for p again, and the first free consumed
     both; the only way out would be p = NULL, which is false. *)
  forward_call (t_cell, p, gv).
  rewrite if_false by (intro; subst; contradiction).
  (* Goal: emp |-- malloc_token Ews t_cell p * data_at_ Ews t_cell p
                   * fold_right_sepcon Frame *)
  Fail solve [cancel].
  Fail solve [entailer!].
Abort.
