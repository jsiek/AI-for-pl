# Task: VST proofs of the frozen stage-1 spec of sglib's DL list

You are verifying C code with VST (Verifiable C 2.17, CompCert 3.17
clightgen, Rocq 9.0.1).  Files in this directory:

* `dllist.c`: the C code (sglib's doubly linked list: six functions).
  Do not change it.
* `spec_dllist.v`: the **frozen** public spec: representation
  predicates and the VST funspecs of the six functions, approved by the
  owner (digest ee6043a2f971a9f6).  Do not change it: it is write-protected and
  checked after the run.  It ends with six `Admitted` lemmas that only
  type-check the statements; your job is to prove them elsewhere.
* `SPEC.md`: the same spec in English, with the reason for each clause.
* `example/`: a small complete VST proof that is not this benchmark
  (`good.c`, `verif_good.v`), as a reference for the setup and style.

## What to produce

One file, `verif_dllist.v`, that starts with

    Require Import VST.floyd.proofauto.
    Require Import VST.floyd.library.
    Require Import SglibVST.dllist SglibVST.spec_dllist.

and proves, each ending in `Qed.`, these six lemmas with exactly these
names and statements (a `Section` with `Variable Rc : globals -> val ->
mpred.` gives the `forall Rc` form):

    Lemma body_add :
      forall Rc : globals -> val -> mpred, semax_body Vprog (Gprog Rc) f_sglib_dllist_add add_spec.
    Lemma body_get_first :
      forall Rc : globals -> val -> mpred, semax_body Vprog (Gprog Rc) f_sglib_dllist_get_first get_first_spec.
    Lemma body_get_last :
      forall Rc : globals -> val -> mpred, semax_body Vprog (Gprog Rc) f_sglib_dllist_get_last get_last_spec.
    Lemma body_it_init_on_equal :
      forall Rc : globals -> val -> mpred, semax_body Vprog (Gprog Rc) f_sglib_dllist_it_init_on_equal (it_init_on_equal_spec Rc).
    Lemma body_it_init :
      forall Rc : globals -> val -> mpred, semax_body Vprog (Gprog Rc) f_sglib_dllist_it_init it_init_spec.
    Lemma body_it_next :
      forall Rc : globals -> val -> mpred, semax_body Vprog (Gprog Rc) f_sglib_dllist_it_next (it_next_spec Rc).

No change to the funspecs.  Helper lemmas are fine (in
`verif_dllist.v`).

Tip: a function whose funspec has no `GLOBALS (gv)` may still call one
that has, by first adding `gvars gv` to its LOCAL clause: `apply
semax_pre with (EX gv: globals, PROP () LOCAL (gvars gv; ...) SEP
(...))` and, in the side goal after `go_lowerx`, `apply exp_right with
(globals_of_env rho)` (`gvars_denote gv rho` is `gv = globals_of_env
rho`).
