# Task: VST proof of stage-1 client {n} of sglib's DL list

You are verifying C code with VST (Verifiable C 2.17, CompCert 3.17
clightgen, Rocq 9.0.1).  Files in this directory:

* `client{n}.c`: the client program: sglib's six DL-list functions
  (verbatim), the client's driver and `main`.  Do not change it.
* `spec_client{n}.v`: the **frozen** public spec of the six library
  functions (digest ee6043a2f971a9f6), restated over this program (only its
  `Require Import` line differs from `spec_dllist.v`).  Do not change it.
* `SPEC.md`, `CLIENT_SURVEY.md`: the spec in English and the client
  survey ({where}).
* `lib_client{n}.v`: the **finished** proofs of the six library
  functions over this program: `body_add`, `body_get_first`,
  `body_get_last`, `body_it_init_on_equal`, `body_it_init`,
  `body_it_next`, each `forall Rc, semax_body Vprog (Gprog Rc) f spec`
  with `Vprog`, `Gprog` and the specs from `spec_client{n}.v`.  Use
  them; do not prove the library functions again.  Do not change it.
* `example/`: a small complete VST proof that is not this benchmark.

## What to produce

One file, `verif_client{n}.v`, that starts with

    Require Import VST.floyd.proofauto.
    Require Import VST.floyd.library.
    Require Import SglibVST.client{n} SglibVST.spec_client{n}.
    Require SglibVST.lib_client{n}.

and that

* defines `Rc_client : globals -> val -> mpred` (the comparator
  resource this program uses; any value if it uses no comparator);
* defines its own `Gprog`, in which each of the six library functions
  has exactly its frozen funspec instantiated at `Rc_client`.  The
  check proves, by `reflexivity`, `find_id i Gprog = find_id i
  (SglibVST.spec_client{n}.Gprog Rc_client)` for each library function
  `i`;
* declares `#[export] Existing Instance NullExtension.Espec.` (the
  check states `semax_prog` with it);
* writes funspecs for the client's own functions and `main`;
* proves `semax_body` for each of the client's own functions and
  `main`, and `prog_correct : semax_prog prog tt Vprog Gprog`, each
  ending in `Qed.`.  For a library function, derive its `semax_body`
  under your `Gprog` from the `lib_client{n}` lemma (e.g. with
  `semax_body_subsumption`).

Leak freedom (owner, 2026-11-17): no postcondition may contain `TT` or
an existential over `mpred` (also inside the predicates it uses), and
`main`'s postcondition is `mem_mgr gv` plus the program's globals (and
`has_ext tt`, which `main_pre` provides: VST's external-state token,
not memory).
