(* Test cases for post_lint.py: every good_* spec must pass and every
   bad_* spec must fail.  Includes the two spellings of Codex's review
   of PR #240 (4603843431: a parenthesised binder; 4603843442: POST
   followed by a line break). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Local Open Scope logic.

Definition _main : ident := 1%positive.
Definition cell (p: val) : mpred := mapsto Ews tint p (Vint Int.zero).

(* ---- good ---- *)

Definition good_spec : funspec :=
  WITH p: val, q: val
  PRE [ tptr tint ] PROP () PARAMS (p) SEP (cell p)
  POST [ tvoid ]
    EX v: val, EX n: Z,
    PROP (v = p; n = 0)
    RETURN ()
    SEP (!! (p = p) && cell p;
         if Val.eq q nullval then emp else emp).

Definition good_pair_spec : ident * funspec := (2%positive, good_spec).

Definition good_main_spec :=
 DECLARE _main
  WITH gv: globals
  PRE [ ] PROP () PARAMS () GLOBALS (gv) SEP (mem_mgr gv)
  POST [ tint ] EX r: int, PROP () RETURN (Vint r) SEP (mem_mgr gv).

(* ---- bad ---- *)

Definition bad_tt_spec : funspec :=
  WITH p: val
  PRE [ tptr tint ] PROP () PARAMS (p) SEP (cell p)
  POST [ tvoid ] PROP () RETURN () SEP (cell p; TT).

(* Codex 4603843431: a parenthesised binder *)
Definition bad_codex_paren_binder_spec : funspec :=
  WITH p: val
  PRE [ tptr tint ] PROP () PARAMS (p) SEP (cell p)
  POST [ tvoid ] PROP () RETURN ()
    SEP (cell p; exp (fun (R : mpred) => R)).

(* Codex 4603843442: POST, then a line break, then the return type *)
Definition bad_codex_post_newline_spec : funspec :=
  WITH p: val
  PRE [ tptr tint ] PROP () PARAMS (p) SEP (cell p)
  POST
  [ tint ] EX r: int, PROP () RETURN (Vint r) SEP (cell p; TT).

Definition bad_typed_binder_spec : funspec :=
  WITH p: val
  PRE [ tptr tint ] PROP () PARAMS (p) SEP (cell p)
  POST [ tvoid ] PROP () RETURN ()
    SEP (cell p; exp (fun R : mpred => R)).

Definition bad_ex_notation_spec : funspec :=
  WITH p: val
  PRE [ tptr tint ] PROP () PARAMS (p) SEP (cell p)
  POST [ tvoid ] EX R: mpred, PROP () RETURN () SEP (cell p; R).

Definition bad_exp_direct_spec : funspec :=
  WITH p: val
  PRE [ tptr tint ] PROP () PARAMS (p) SEP (cell p)
  POST [ tvoid ] PROP () RETURN ()
    SEP (cell p; @exp mpred _ mpred (fun R => R)).

Definition bad_ex_function_spec : funspec :=
  WITH p: val
  PRE [ tptr tint ] PROP () PARAMS (p) SEP (cell p)
  POST [ tvoid ] EX F: val -> mpred, PROP () RETURN () SEP (F p).

Definition hide : mpred := EX R: mpred, R.
Definition bad_hidden_ex_spec : funspec :=
  WITH p: val
  PRE [ tptr tint ] PROP () PARAMS (p) SEP (cell p)
  POST [ tvoid ] PROP () RETURN () SEP (cell p; hide).

Definition junk : mpred := TT.
Definition wrap (p: val) : mpred := cell p * junk.
Definition bad_tt_via_definitions_spec : funspec :=
  WITH p: val
  PRE [ tptr tint ] PROP () PARAMS (p) SEP (cell p)
  POST [ tvoid ] PROP () RETURN () SEP (wrap p).

Definition bad_prop_true_spec : funspec :=
  WITH p: val
  PRE [ tptr tint ] PROP () PARAMS (p) SEP (cell p)
  POST [ tvoid ] PROP () RETURN () SEP (cell p; !! True).

Definition bad_two_props_spec : funspec :=
  WITH p: val
  PRE [ tptr tint ] PROP () PARAMS (p) SEP (cell p)
  POST [ tvoid ] PROP () RETURN () SEP (cell p; !! True && !! (p = p)).

Definition bad_wand_spec : funspec :=
  WITH p: val
  PRE [ tptr tint ] PROP () PARAMS (p) SEP (cell p)
  POST [ tvoid ] PROP () RETURN () SEP (cell p -* cell p).

Definition bad_tt_pair_spec : ident * funspec := (3%positive, bad_tt_spec).

Definition bad_main_spec :=
 DECLARE _main
  WITH gv: globals
  PRE [ ] PROP () PARAMS () GLOBALS (gv) SEP (mem_mgr gv)
  POST [ tint ] EX r: int, PROP () RETURN (Vint r) SEP ().

Definition bad_main_tt_spec :=
 DECLARE _main
  WITH gv: globals
  PRE [ ] PROP () PARAMS () GLOBALS (gv) SEP (mem_mgr gv)
  POST [ tint ] EX r: int, PROP () RETURN (Vint r) SEP (mem_mgr gv; TT).

(* fail closed: a funspec with no body to examine *)
Parameter bad_opaque_spec : funspec.

(* fail closed: a funspec whose postcondition is not visible (an
   abstract funspec passed in) *)
Section Foreign.
Variable foreign: funspec.
Definition bad_foreign_spec : funspec := foreign.
End Foreign.
