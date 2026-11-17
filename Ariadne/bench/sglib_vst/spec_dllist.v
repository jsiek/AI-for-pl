(* sglib's doubly linked list, stage 1 of plan M6: the public VST spec
   (approved by the owner on 2026-11-17 after a function-by-function
   walkthrough; frozen with the client survey: its digest, over this
   file and SPEC.md, is stated in SPEC.md and checked by check.sh).
   SPEC.md says the same in English, with a citation for every clause
   (owner, 2026-11-17: the goal is memory safety plus leak freedom, and
   public specs are minimal relative to the client survey); REVIEW.md
   lists where the two differ and the owner's decisions.

   Instance: B1's dllist (dllist.c, from make_dllist.py).  The bodies
   are Admitted: this file only checks that the funspecs are well typed
   against clightgen's output.  No proof is claimed.

   Line numbers "dllist.c:N" in the comments are the body lines that
   need a precondition clause. *)

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
(* Representation                                                     *)
(* ================================================================== *)

(* A list is described by the sequence [s] of its node addresses
   n0 .. nk-1 and the sequence [vs] of their contents
   (payload, (ptr_to_next, ptr_to_previous)).  Ownership is the
   separating conjunction of the nodes ([nodes]); the shape is a pure
   fact about the links ([prev_links], [next_links]), so each funspec
   asks for exactly the links its body follows.  No malloc_token: no
   function frees, so the client keeps the tokens of its nodes. *)

Definition node_v : Type := (val * (val * val))%type.
Definition pay (v: node_v) : val := fst v.
Definition nxt (v: node_v) : val := fst (snd v).
Definition prv (v: node_v) : val := snd (snd v).

(* node i of s, or NULL off either end *)
Definition Znth_or_null (s: list val) (i: Z) : val :=
  if zle 0 i then if zlt i (Zlength s) then Znth i s else nullval
  else nullval.

Fixpoint nodesN (sh: share) (s: list val) (vs: list node_v) (lo: Z)
    (n: nat) : mpred :=
  match n with
  | O => emp
  | S n' => data_at sh t_dl (Znth lo vs) (Znth lo s)
            * nodesN sh s vs (lo+1) n'
  end.

(* nodes lo .. hi-1 of s, at share sh, with contents vs *)
Definition nodes (sh: share) (s: list val) (vs: list node_v)
    (lo hi: Z) : mpred :=
  nodesN sh s vs lo (Z.to_nat (hi - lo)).
Arguments nodes : simpl never.

(* nodes lo .. hi-1 have ptr_to_previous = the node before (NULL for
   n0) / ptr_to_next = the node after (NULL for the last) *)
Definition prev_links (s: list val) (vs: list node_v) (lo hi: Z) : Prop :=
  forall i, lo <= i < hi -> prv (Znth i vs) = Znth_or_null s (i-1).
Definition next_links (s: list val) (vs: list node_v) (lo hi: Z) : Prop :=
  forall i, lo <= i < hi -> nxt (Znth i vs) = Znth_or_null s (i+1).

(* a whole list: every link consistent *)
Definition whole (s: list val) (vs: list node_v) : Prop :=
  Zlength vs = Zlength s /\
  prev_links s vs 0 (Zlength s) /\ next_links s vs 0 (Zlength s).

(* "p is node j of s, or p is NULL and s is empty" (p = Znth_or_null s j).
   A caller passing NULL takes s = [] and frames its other lists. *)
Definition at_node (s: list val) (j: Z) : Prop :=
  (s = [] /\ j = 0) \/ 0 <= j < Zlength s.

(* payloads lo .. hi-1 are initialised ints *)
Definition int_val (v: val) : Prop := exists i, v = Vint i.
Definition int_payloads (vs: list node_v) (lo hi: Z) : Prop :=
  forall i, lo <= i < hi -> int_val (pay (Znth i vs)).

(* insertion of x at position j *)
Definition ins {A} {d: Inhabitant A} (j: Z) (x: A) (l: list A) : list A :=
  sublist 0 j l ++ x :: sublist j (Zlength l) l.

(* ------------------------------------------------------------------ *)
(* Iterator state over the sequence s with window (b, f),
   -1 <= b < f <= Zlength s: prevelem = n(b) (NULL when b = -1) and
   nextelem = n(f) (NULL when f = Zlength s).  The nodes still to be
   visited are n0 .. n(b) and n(f) .. n(k-1); the client lends them to
   each it_next call.  currentelem is not described (no client reads
   it, and no body reads it). *)
Definition it_rep (sh: share) (it: val) (s: list val) (b f: Z)
    (scp eqp: val) : mpred :=
  EX cur: val,
  data_at sh t_it
    (cur, (Znth_or_null s b, (Znth_or_null s f, (scp, eqp)))) it.

(* The result r of a call that moves the window from (b, f) to
   (b', f').  SPEC.md cites a client for each clause.
   [step_any]: the window only widens (the client lends no node it may
   have freed); r is NULL or a node that was still to be visited and is
   now inside the window (the client owns r; r is never returned
   twice); NULL means no node is left to visit (R1, leak freedom).
   [step_exact], without a comparator: exactly r leaves the nodes still
   to be visited, from either end of the window (no order promised), so
   an iteration returns every node once (Q4 as amended 2026-11-17). *)
Definition step_any (s: list val) (b f b' f': Z) (r: val) : Prop :=
  -1 <= b' <= b /\ f <= f' <= Zlength s /\
  (r = nullval \/
   exists c, b' < c < f' /\ (c <= b \/ f <= c) /\ r = Znth c s) /\
  (r = nullval -> b' = -1 /\ f' = Zlength s).

Definition step_exact (s: list val) (b f b' f': Z) (r: val) : Prop :=
  (r = nullval /\ b = -1 /\ f = Zlength s /\ b' = b /\ f' = f) \/
  (0 <= b /\ r = Znth b s /\ b' = b - 1 /\ f' = f) \/
  (f < Zlength s /\ r = Znth f s /\ b' = b /\ f' = f + 1).

Definition iter_step (scp: val) (s: list val) (b f b' f': Z) (r: val)
    : Prop :=
  step_any s b f b' f' r /\ (scp = nullval -> step_exact s b f b' f' r).

(* After it_init(_on_equal): a window with r NULL or inside it, NULL
   meaning no node is left; without a comparator, r is the only node
   inside the window (and r is NULL only for the empty list). *)
Definition init_window (scp: val) (s: list val) (b f: Z) (r: val)
    : Prop :=
  -1 <= b < f /\ f <= Zlength s /\
  (r = nullval \/ exists c, b < c < f /\ r = Znth c s) /\
  (r = nullval -> b = -1 /\ f = Zlength s) /\
  (scp = nullval ->
   (r = nullval /\ s = [] /\ b = -1 /\ f = 0) \/
   (exists c, 0 <= c < Zlength s /\ r = Znth c s /\
              b = c - 1 /\ f = c + 1)).

(* ================================================================== *)
(* Comparators (Q6; owner, R2, 2026-11-17).  A program fixes one state
   predicate per comparator function pointer, Rc gv f (a Section
   parameter).  sglib's comparator type passes no context, so the state
   is reached through globals: Rc takes the program's globals gv, and
   cmp_spec, it_init_on_equal and it_next carry GLOBALS (gv) so that the
   comparator's body can address them.  The comparator f is proved
   against cmp_spec f: it takes Rc gv f and gives Rc gv f back; the
   state's value stays hidden inside (e.g. EX k, data_at .. (Vint k)
   (gv _count_f)), with no constraint on the new state.  The iterator never holds the state: the
   client lends Rc gv scp to each it_init_on_equal / it_next call that has
   a comparator ([cmp_state]) and gets it back after.  Comparators that
   share a global: the client converts between their predicates by
   entailment between calls. *)
(* ================================================================== *)

Section Spec.
Context (Rc: globals -> val -> mpred).

Definition cmp_spec (f: val) : funspec :=
  WITH gv: globals, sha: share, shb: share, a: val, b: val,
       va: node_v, vb: node_v
  PRE [ tptr t_dl, tptr t_dl ]
    PROP (readable_share sha; readable_share shb;
          int_val (pay va); int_val (pay vb))
    PARAMS (a; b) GLOBALS (gv)
    SEP (data_at sha t_dl va a; data_at shb t_dl vb b; Rc gv f)
  POST [ tint ]
    EX r: int,
    PROP ()
    RETURN (Vint r)
    SEP (data_at sha t_dl va a; data_at shb t_dl vb b; Rc gv f).

(* What a call that may compare needs besides the state: nothing when
   scp is NULL; otherwise scp satisfies cmp_spec scp, and the client
   lends the equalto node (any readable share, payload an int). *)
Definition cmp_env (scp eqp: val) (sheq: share) (veq: node_v) : mpred :=
  if Val.eq scp nullval then emp
  else !! (readable_share sheq /\ int_val (pay veq)) &&
       (func_ptr' (cmp_spec scp) scp * data_at sheq t_dl veq eqp).

(* The comparator state the client lends for the call: none without a
   comparator. *)
Definition cmp_state (gv: globals) (scp: val) : mpred :=
  if Val.eq scp nullval then emp else Rc gv scp.

(* with a comparator, the payloads it will be shown are ints *)
Definition cmp_payloads (scp: val) (vs: list node_v) (lo hi: Z) : Prop :=
  scp = nullval \/ int_payloads vs lo hi.

(* ================================================================== *)
(* Funspecs.  add: the position-exact form (owner, R9, 2026-11-17), a
   simplicity exception; the minimal form ("the old nodes plus elem, in
   some order") is recorded in REVIEW.md. *)
(* ================================================================== *)

Definition add_spec :=
 DECLARE _sglib_dllist_add
  WITH shl: share, lp: val, sh: share, e: val, ev: val, enp: val * val,
       s: list val, vs: list node_v, j: Z
  PRE [ tptr (tptr t_dl), tptr t_dl ]
    PROP (writable_share shl;       (* dllist.c:26,37 write *list *)
          writable_share sh;        (* :27,30-32,34 write links *)
          at_node s j;              (* :24,31 *list NULL or a node *)
          whole s vs)               (* :31,34 prev of *list; rest:
                                       simplicity exception, R8 *)
    PARAMS (lp; e)
    SEP (data_at shl (tptr t_dl) (Znth_or_null s j) lp;   (* :24 *)
         data_at sh t_dl (ev, enp) e;                     (* :27,30-31 *)
         nodes sh s vs 0 (Zlength s))                     (* :31-34 *)
  POST [ tvoid ]
    EX vs': list node_v,
    PROP (whole (ins j e s) vs';
          map pay vs' = ins j ev (map pay vs))
    RETURN ()
    SEP (data_at shl (tptr t_dl) e lp;
         nodes sh (ins j e s) vs' 0 (Zlength s + 1)).

Definition get_first_spec :=
 DECLARE _sglib_dllist_get_first
  WITH sh: share, s: list val, vs: list node_v, j: Z
  PRE [ tptr t_dl ]
    PROP (readable_share sh;                       (* dllist.c:46 *)
          at_node s j; Zlength vs = Zlength s;     (* :44-46 *)
          prev_links s vs 0 (Z.min (j+1) (Zlength s)))  (* :46 *)
    PARAMS (Znth_or_null s j)
    SEP (nodes sh s vs 0 (Z.min (j+1) (Zlength s)))     (* :46 *)
  POST [ tptr t_dl ]
    EX r: val,
    PROP (r = nullval \/ In r s)
    RETURN (r)
    SEP (nodes sh s vs 0 (Z.min (j+1) (Zlength s))).

Definition get_last_spec :=
 DECLARE _sglib_dllist_get_last
  WITH sh: share, s: list val, vs: list node_v, j: Z
  PRE [ tptr t_dl ]
    PROP (readable_share sh;                       (* dllist.c:59 *)
          at_node s j; Zlength vs = Zlength s;     (* :57-59 *)
          next_links s vs j (Zlength s))           (* :59 *)
    PARAMS (Znth_or_null s j)
    SEP (nodes sh s vs j (Zlength s))              (* :59 *)
  POST [ tptr t_dl ]
    EX r: val,
    PROP (r = nullval \/ In r s)
    RETURN (r)
    SEP (nodes sh s vs j (Zlength s)).

Definition it_init_on_equal_spec :=
 DECLARE _sglib_dllist_it_init_on_equal
  WITH gv: globals, sh: share, it: val, shl: share, s: list val,
       vs: list node_v, j: Z, scp: val, eqp: val, sheq: share, veq: node_v
  PRE [ tptr t_it, tptr t_dl, t_cmp, tptr t_dl ]
    PROP (writable_share sh;                 (* dllist.c:70-75 *)
          readable_share shl;                (* :75; it_next *)
          at_node s j; Zlength vs = Zlength s;            (* :72-75 *)
          prev_links s vs 0 (Z.min (j+1) (Zlength s));    (* :76 *)
          next_links s vs j (Zlength s);                  (* :75-76 *)
          cmp_payloads scp vs 0 (Zlength s))              (* :76 *)
    PARAMS (it; Znth_or_null s j; scp; eqp) GLOBALS (gv)
    SEP (data_at_ sh t_it it;                             (* :70-73 *)
         nodes shl s vs 0 (Zlength s);                    (* :75-76 *)
         cmp_env scp eqp sheq veq;                        (* :76 *)
         cmp_state gv scp)                                   (* :76 *)
  POST [ tptr t_dl ]
    EX b: Z, EX f: Z, EX r: val,
    PROP (init_window scp s b f r)
    RETURN (r)
    SEP (it_rep sh it s b f scp eqp;
         nodes shl s vs 0 (Zlength s);
         cmp_env scp eqp sheq veq; cmp_state gv scp).

Definition it_init_spec :=
 DECLARE _sglib_dllist_it_init
  WITH sh: share, it: val, shl: share, s: list val, vs: list node_v, j: Z
  PRE [ tptr t_it, tptr t_dl ]
    PROP (writable_share sh; readable_share shl;     (* dllist.c:79 *)
          at_node s j; Zlength vs = Zlength s;
          prev_links s vs 0 (Z.min (j+1) (Zlength s));
          next_links s vs j (Zlength s))
    PARAMS (it; Znth_or_null s j)
    SEP (data_at_ sh t_it it; nodes shl s vs 0 (Zlength s))
  POST [ tptr t_dl ]
    EX b: Z, EX f: Z, EX r: val,
    PROP (init_window nullval s b f r)
    RETURN (r)
    SEP (it_rep sh it s b f nullval nullval;
         nodes shl s vs 0 (Zlength s)).

Definition it_next_spec :=
 DECLARE _sglib_dllist_it_next
  WITH gv: globals, sh: share, it: val, shl: share, s: list val,
       vs: list node_v, b: Z, f: Z, scp: val, eqp: val,
       sheq: share, veq: node_v
  PRE [ tptr t_it ]
    PROP (writable_share sh;            (* dllist.c:85,96,99,110,112 *)
          readable_share shl;           (* :90,92,104,106 *)
          Zlength vs = Zlength s;
          -1 <= b < f; f <= Zlength s;  (* :84,98 NULL or a node *)
          prev_links s vs 0 (b+1);      (* :92,96 *)
          next_links s vs f (Zlength s);   (* :106,110 *)
          cmp_payloads scp vs 0 (b+1);     (* :90 *)
          cmp_payloads scp vs f (Zlength s))  (* :104 *)
    PARAMS (it) GLOBALS (gv)
    SEP (it_rep sh it s b f scp eqp;    (* :84,86-88,98,100-102 *)
         nodes shl s vs 0 (b+1);        (* :90,92,96 *)
         nodes shl s vs f (Zlength s);  (* :104,106,110 *)
         cmp_env scp eqp sheq veq;      (* :90,104 *)
         cmp_state gv scp)                 (* :90,104 *)
  POST [ tptr t_dl ]
    EX b': Z, EX f': Z, EX r: val,
    PROP (iter_step scp s b f b' f' r)
    RETURN (r)
    SEP (it_rep sh it s b' f' scp eqp;
         nodes shl s vs 0 (b+1); nodes shl s vs f (Zlength s);
         cmp_env scp eqp sheq veq; cmp_state gv scp).

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
