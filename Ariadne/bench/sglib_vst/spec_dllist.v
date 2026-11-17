(* sglib's doubly linked list, stage 1 of plan M6: the public VST spec
   (DRAFT for the owner's review).  SPEC.md says the same in English;
   REVIEW.md lists where the two differ and what is still open.

   Instance: B1's dllist (dllist.c, from make_dllist.py).  The bodies
   are Admitted: this file only checks that the funspecs are well typed
   against clightgen's output.  No proof is claimed. *)

Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import SglibVST.dllist.

#[export] Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.

Local Open Scope logic.

Definition t_dl := Tstruct _dllist noattr.
Definition t_it := Tstruct _sglib_dllist_iterator noattr.
Definition t_cmp :=
  tptr (Tfunction (tptr t_dl :: tptr t_dl :: nil) tint cc_default).

(* ================================================================== *)
(* Representation predicates                                          *)
(* ================================================================== *)

(* A list is described by the sequence [s] of its node addresses
   n0 .. nk-1 and the sequence [ps] of their payloads (field i). *)

(* node i of s, or NULL off either end *)
Definition Znth_or_null (s: list val) (i: Z) : val :=
  if zle 0 i then if zlt i (Zlength s) then Znth i s else nullval
  else nullval.

(* Node j, owned: a live malloc'ed block (malloc_token) holding payload
   Znth j ps, ptr_to_next = n(j+1) (NULL for the last node) and
   ptr_to_previous = n(j-1) (NULL for the first). *)
Definition cell (s ps: list val) (j: Z) : mpred :=
  data_at Ews t_dl
    (Znth j ps, (Znth_or_null s (j+1), Znth_or_null s (j-1))) (Znth j s)
  * malloc_token Ews t_dl (Znth j s).

Fixpoint cellsN (s ps: list val) (lo: Z) (n: nat) : mpred :=
  match n with
  | O => emp
  | S n' => cell s ps lo * cellsN s ps (lo+1) n'
  end.

(* List segment: nodes lo .. hi-1 of the list s, each owned.  The links
   of the end nodes point at n(lo-1) and n(hi), which the segment does
   not own. *)
Definition cells (s ps: list val) (lo hi: Z) : mpred :=
  cellsN s ps lo (Z.to_nat (hi - lo)).
Arguments cells : simpl never.

(* Whole list: every node of s, with first node's ptr_to_previous and
   last node's ptr_to_next NULL.  The nodes are distinct because the
   cells are separate.  s = [] is the empty list (owns nothing). *)
Definition whole_list (s ps: list val) : mpred :=
  !! (Zlength ps = Zlength s) && cells s ps 0 (Zlength s).

(* "p is NULL and s is empty, or p is node j of s" *)
Definition at_node (s: list val) (j: Z) : Prop :=
  (s = [] /\ j = 0) \/ 0 <= j < Zlength s.

(* insertion of x at position j *)
Definition ins {A} {d: Inhabitant A} (j: Z) (x: A) (l: list A) : list A :=
  sublist 0 j l ++ x :: sublist j (Zlength l) l.

(* ------------------------------------------------------------------ *)
(* Iterator state.  Positions b, f with -1 <= b < f <= Zlength s:
   prevelem = n(b) (NULL when b = -1) and nextelem = n(f) (NULL when
   f = Zlength s).  The nodes still to be visited are n0 .. n(b) and
   n(f) .. n(k-1); between calls the iterator owns no node: the client
   lends it those two segments for each it_next call. *)
Definition it_rep (sh: share) (it: val) (s: list val) (b f: Z)
    (cur scp eqp: val) : mpred :=
  data_at sh t_it
    (cur, (Znth_or_null s b, (Znth_or_null s f, (scp, eqp)))) it.

(* One iterator step from window (b, f) to (b', f'), returning r: the
   window only widens (the nodes still to be visited only shrink), and
   r is NULL or a node that was still to be visited and is now inside
   the window.  No order or coverage is promised (Q4): in particular
   r = NULL need not mean that no node is left to visit. *)
Definition iter_step (s: list val) (b f b' f': Z) (r: val) : Prop :=
  -1 <= b' <= b /\ f <= f' <= Zlength s /\ b' < f' /\
  (r = nullval \/
   exists c, b' < c < f' /\ (c <= b \/ f <= c) /\ r = Znth c s).

(* The state after it_init(_on_equal) at node j: one step from the
   window (j, j+1) (sglib sets prevelem = list, nextelem = list->next
   and calls it_next), or from (-1, 0) on the empty list. *)
Definition init_step (s: list val) (j b f: Z) (r: val) : Prop :=
  (s = [] /\ iter_step s (-1) 0 b f r) \/
  (0 <= j < Zlength s /\ iter_step s j (j+1) b f r).

(* ================================================================== *)
(* Comparators (Q6).  A program fixes a state type CS and a predicate
   Rc on it; every comparator it passes to it_init_on_equal is proved
   against cmp_spec: it reads both nodes (returned unchanged), returns
   an int, may change its own state (Rc st to Rc st') and writes no
   node. *)
(* ================================================================== *)

Section Spec.
Context {CS: Type} (Rc: CS -> mpred).

Definition cmp_spec : funspec :=
  WITH sha: share, shb: share, a: val, b: val,
       va: val * (val * val), vb: val * (val * val), st: CS
  PRE [ tptr t_dl, tptr t_dl ]
    PROP (readable_share sha; readable_share shb)
    PARAMS (a; b)
    SEP (data_at sha t_dl va a; data_at shb t_dl vb b; Rc st)
  POST [ tint ]
    EX r: int, EX st': CS,
    PROP ()
    RETURN (Vint r)
    SEP (data_at sha t_dl va a; data_at shb t_dl vb b; Rc st').

(* What it_next needs to call the comparator: nothing when scp is NULL;
   otherwise scp satisfies cmp_spec, the client lends the equalto node
   (any readable share) and the comparator state. *)
Definition cmp_env (scp eqp: val) (sheq: share) (veq: val * (val * val))
    (st: CS) : mpred :=
  if Val.eq scp nullval then emp
  else !! readable_share sheq &&
       (func_ptr' cmp_spec scp * data_at sheq t_dl veq eqp * Rc st).

(* ================================================================== *)
(* Funspecs                                                           *)
(* ================================================================== *)

Definition add_spec :=
 DECLARE _sglib_dllist_add
  WITH sh: share, lp: val, e: val, ev: val, enp: val * val,
       s: list val, ps: list val, j: Z
  PRE [ tptr (tptr t_dl), tptr t_dl ]
    PROP (writable_share sh; at_node s j)
    PARAMS (lp; e)
    SEP (data_at sh (tptr t_dl) (Znth_or_null s j) lp;
         data_at Ews t_dl (ev, enp) e; malloc_token Ews t_dl e;
         whole_list s ps)
  POST [ tvoid ]
    PROP ()
    RETURN ()
    SEP (data_at sh (tptr t_dl) e lp;
         whole_list (ins j e s) (ins j ev ps)).

Definition get_first_spec :=
 DECLARE _sglib_dllist_get_first
  WITH s: list val, ps: list val, j: Z
  PRE [ tptr t_dl ]
    PROP (at_node s j)
    PARAMS (Znth_or_null s j)
    SEP (whole_list s ps)
  POST [ tptr t_dl ]
    PROP ()
    RETURN (Znth_or_null s 0)
    SEP (whole_list s ps).

Definition get_last_spec :=
 DECLARE _sglib_dllist_get_last
  WITH s: list val, ps: list val, j: Z
  PRE [ tptr t_dl ]
    PROP (at_node s j)
    PARAMS (Znth_or_null s j)
    SEP (whole_list s ps)
  POST [ tptr t_dl ]
    PROP ()
    RETURN (Znth_or_null s (Zlength s - 1))
    SEP (whole_list s ps).

Definition it_init_on_equal_spec :=
 DECLARE _sglib_dllist_it_init_on_equal
  WITH sh: share, it: val, s: list val, ps: list val, j: Z,
       scp: val, eqp: val, sheq: share, veq: val * (val * val), st: CS
  PRE [ tptr t_it, tptr t_dl, t_cmp, tptr t_dl ]
    PROP (writable_share sh; at_node s j)
    PARAMS (it; Znth_or_null s j; scp; eqp)
    SEP (data_at_ sh t_it it; whole_list s ps;
         cmp_env scp eqp sheq veq st)
  POST [ tptr t_dl ]
    EX b: Z, EX f: Z, EX r: val, EX st': CS,
    PROP (init_step s j b f r)
    RETURN (r)
    SEP (it_rep sh it s b f r scp eqp; whole_list s ps;
         cmp_env scp eqp sheq veq st').

Definition it_init_spec :=
 DECLARE _sglib_dllist_it_init
  WITH sh: share, it: val, s: list val, ps: list val, j: Z
  PRE [ tptr t_it, tptr t_dl ]
    PROP (writable_share sh; at_node s j)
    PARAMS (it; Znth_or_null s j)
    SEP (data_at_ sh t_it it; whole_list s ps)
  POST [ tptr t_dl ]
    EX b: Z, EX f: Z, EX r: val,
    PROP (init_step s j b f r)
    RETURN (r)
    SEP (it_rep sh it s b f r nullval nullval; whole_list s ps).

Definition it_next_spec :=
 DECLARE _sglib_dllist_it_next
  WITH sh: share, it: val, s: list val, ps: list val, b: Z, f: Z,
       cur: val, scp: val, eqp: val,
       sheq: share, veq: val * (val * val), st: CS
  PRE [ tptr t_it ]
    PROP (writable_share sh; Zlength ps = Zlength s;
          -1 <= b < f; f <= Zlength s)
    PARAMS (it)
    SEP (it_rep sh it s b f cur scp eqp;
         cells s ps 0 (b+1); cells s ps f (Zlength s);
         cmp_env scp eqp sheq veq st)
  POST [ tptr t_dl ]
    EX b': Z, EX f': Z, EX r: val, EX st': CS,
    PROP (iter_step s b f b' f' r)
    RETURN (r)
    SEP (it_rep sh it s b' f' r scp eqp;
         cells s ps 0 (b+1); cells s ps f (Zlength s);
         cmp_env scp eqp sheq veq st').

Definition Gprog : funspecs :=
  ltac:(with_library prog [add_spec; get_first_spec; get_last_spec;
                           it_init_on_equal_spec; it_init_spec;
                           it_next_spec]).

(* ================================================================== *)
(* Type check only: the statements below must elaborate; the proofs
   are the next step of M6. *)
(* ================================================================== *)

Lemma body_add: semax_body Vprog Gprog f_sglib_dllist_add add_spec.
Admitted.
Lemma body_get_first:
  semax_body Vprog Gprog f_sglib_dllist_get_first get_first_spec.
Admitted.
Lemma body_get_last:
  semax_body Vprog Gprog f_sglib_dllist_get_last get_last_spec.
Admitted.
Lemma body_it_init_on_equal:
  semax_body Vprog Gprog f_sglib_dllist_it_init_on_equal
    it_init_on_equal_spec.
Admitted.
Lemma body_it_init:
  semax_body Vprog Gprog f_sglib_dllist_it_init it_init_spec.
Admitted.
Lemma body_it_next:
  semax_body Vprog Gprog f_sglib_dllist_it_next it_next_spec.
Admitted.

End Spec.
