(* VST proof of benchmark B1a (b1.c): sglib's doubly linked list.
   Every function in b1.c is verified (semax_body) and the whole program
   is verified (semax_prog prog_correct).  Memory safety, including the
   absence of use after free and double free, follows from VST's
   soundness theorem w.r.t. CompCert Clight; the frees are of malloc'd
   blocks because free's spec needs the block's malloc_token.

   Contracts are restricted as in the Frama-C version
   (../../bench/b1/b1.c): the list pointer passed to add / it_init is
   the head (its predecessor is NULL), and the iterator is used without
   a subcomparator.  Values are not tracked beyond what the shape needs:
   no functional correctness. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import B1.b1.

#[export] Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.

(* ---------- Specification: representation predicate ---------- *)

Definition t_dll := Tstruct _dllist noattr.
Definition t_it := Tstruct _sglib_dllist_iterator noattr.

(* A list is given by its nodes: (address, value of field i).
   hd_or s t is the first address of s, or t if s is empty. *)

Definition hd_or (s: list (val * int)) (t: val) : val :=
  match s with nil => t | (p, _) :: _ => p end.
Definition hd_ptr (s: list (val * int)) : val := hd_or s nullval.

(* dlseg prev s t: the nodes of s, in order, each owning its cell and
   malloc token; node k's ptr_to_next is node k+1 (t after the last)
   and its ptr_to_previous is node k-1 (prev for the first).
   Disjointness of the nodes is implied by the separating conjunction. *)
Fixpoint dlseg (prev: val) (s: list (val * int)) (t: val) : mpred :=
  match s with
  | nil => emp
  | (p, x) :: s' =>
      (data_at Ews t_dll (Vint x, (hd_or s' t, prev)) p
      * malloc_token Ews t_dll p * dlseg p s' t)%logic
  end.

Lemma dlseg_cons: forall prev p x s t,
  dlseg prev ((p, x) :: s) t =
  (data_at Ews t_dll (Vint x, (hd_or s t, prev)) p
   * malloc_token Ews t_dll p * dlseg p s t)%logic.
Proof. reflexivity. Qed.

(* The head of a NULL-terminated segment is a pointer or NULL. *)
Lemma dlseg_local_facts: forall prev s,
  dlseg prev s nullval |-- !! is_pointer_or_null (hd_or s nullval).
Proof.
  intros. destruct s as [| [p x] s]; simpl; entailer!.
Qed.
#[export] Hint Resolve dlseg_local_facts : saturate_local.

(* The address of the last node of s, or prev if s is empty. *)
Fixpoint last_or (prev: val) (s: list (val * int)) : val :=
  match s with nil => prev | (p, _) :: s' => last_or p s' end.

Lemma hd_or_app: forall s1 p y t,
  hd_or (s1 ++ [(p, y)]) t = hd_or s1 p.
Proof. intros. destruct s1 as [| [] ]; reflexivity. Qed.

Lemma last_or_snoc: forall s1 prev p y,
  last_or prev (s1 ++ [(p, y)]) = p.
Proof.
  induction s1 as [| [q x] s1 IH]; intros; simpl; auto.
Qed.

(* Extending a segment by one node at its end (the forward walk). *)
Lemma dlseg_snoc: forall s1 prev p y t,
  dlseg prev s1 p
  * data_at Ews t_dll (Vint y, (t, last_or prev s1)) p
  * malloc_token Ews t_dll p
  |-- dlseg prev (s1 ++ [(p, y)]) t.
Proof.
  induction s1 as [| [q x] s1 IH]; intros; simpl.
  - cancel.
  - rewrite hd_or_app. sep_apply (IH q p y t). cancel.
Qed.

(* A NULL-terminated list whose first node's predecessor is prev
   (NULL for a whole list; a dangling pointer once the head is freed). *)
Definition dll (prev: val) (s: list (val * int)) : mpred :=
  dlseg prev s nullval.

Lemma dll_local_facts: forall prev s,
  dll prev s |-- !! is_pointer_or_null (hd_ptr s).
Proof. intros. apply dlseg_local_facts. Qed.
#[export] Hint Resolve dll_local_facts : saturate_local.

(* ---------- Specification: funspecs ---------- *)

(* add: *list is the head of a list s and elem a separate malloc'd node;
   afterwards *list = elem heads elem :: s. *)
Definition sglib_dllist_add_spec :=
 DECLARE _sglib_dllist_add
  WITH sh: share, list: val, elem: val, x: int, nx: val, pv: val,
       s: list (val * int)
  PRE [ tptr (tptr t_dll), tptr t_dll ]
    PROP (writable_share sh)
    PARAMS (list; elem)
    SEP (data_at sh (tptr t_dll) (hd_ptr s) list; dll nullval s;
         data_at Ews t_dll (Vint x, (nx, pv)) elem;
         malloc_token Ews t_dll elem)
  POST [ tvoid ]
    PROP () RETURN ()
    SEP (data_at sh (tptr t_dll) elem list; dll nullval ((elem, x) :: s)).

(* The iterator fields, in order: currentelem, prevelem, nextelem,
   subcomparator, equalto.  it_next is called in two states, both with
   no subcomparator and the iterator owning nothing but its struct:
   - prevelem == NULL, nextelem the head of the rest s (later calls,
     from the driver; s's predecessor q is arbitrary, possibly freed);
   - prevelem the head of the whole list s (q == NULL) and nextelem its
     successor (the call from it_init_on_equal).
   Either way it returns the head of s and leaves prevelem NULL and
   nextelem the head of tl s; the nodes are unchanged. *)
Definition iter_pre (pv nx q: val) (s: list (val * int)) : Prop :=
  (pv = nullval /\ nx = hd_ptr s)
  \/ (q = nullval /\ s <> nil /\ pv = hd_ptr s /\ nx = hd_ptr (tl s)).

Definition sglib_dllist_it_next_spec :=
 DECLARE _sglib_dllist_it_next
  WITH sh: share, it: val, cur: val, pv: val, nx: val, eqv: val, q: val,
       s: list (val * int)
  PRE [ tptr t_it ]
    PROP (writable_share sh; iter_pre pv nx q s)
    PARAMS (it)
    SEP (data_at sh t_it (cur, (pv, (nx, (nullval, eqv)))) it; dll q s)
  POST [ tptr t_dll ]
    PROP () RETURN (hd_ptr s)
    SEP (data_at sh t_it
           (hd_ptr s, (nullval, (hd_ptr (tl s), (nullval, eqv)))) it;
         dll q s).

(* The driver's iterator after it_init / it_next: current element cur,
   prevelem NULL, nextelem nx, no subcomparator, equalto NULL.  A
   definition because a data_at of a struct value written inline under
   EX in a loop invariant fails to elaborate (EX picks the mpred
   instance instead of environ -> mpred). *)
Definition it_val (cur nx: val) : val * (val * (val * (val * val))) :=
  (cur, (nullval, (nx, (nullval, nullval)))).
Definition iter_at (cur nx it: val) : mpred :=
  data_at Tsh t_it (it_val cur nx) it.

(* it_init_on_equal: restricted to subcomparator == NULL and list the
   head of a whole list; equalto is arbitrary. *)
Definition t_cmp :=
  tptr (Tfunction (tptr t_dll :: tptr t_dll :: nil) tint cc_default).

Definition sglib_dllist_it_init_on_equal_spec :=
 DECLARE _sglib_dllist_it_init_on_equal
  WITH sh: share, it: val, eqv: val, s: list (val * int)
  PRE [ tptr t_it, tptr t_dll, t_cmp, tptr t_dll ]
    PROP (writable_share sh)
    PARAMS (it; hd_ptr s; nullval; eqv)
    SEP (data_at_ sh t_it it; dll nullval s)
  POST [ tptr t_dll ]
    PROP () RETURN (hd_ptr s)
    SEP (data_at sh t_it
           (hd_ptr s, (nullval, (hd_ptr (tl s), (nullval, eqv)))) it;
         dll nullval s).

Definition sglib_dllist_it_init_spec :=
 DECLARE _sglib_dllist_it_init
  WITH sh: share, it: val, s: list (val * int)
  PRE [ tptr t_it, tptr t_dll ]
    PROP (writable_share sh)
    PARAMS (it; hd_ptr s)
    SEP (data_at_ sh t_it it; dll nullval s)
  POST [ tptr t_dll ]
    PROP () RETURN (hd_ptr s)
    SEP (data_at sh t_it
           (hd_ptr s, (nullval, (hd_ptr (tl s), (nullval, nullval)))) it;
         dll nullval s).

(* The driver: n readable ints at input.  The postcondition holds no
   list nodes; the proof gives each node back to free (no node is
   dropped by an entailment). *)
Definition b1_spec :=
 DECLARE _b1
  WITH gv: globals, sh: share, input: val, contents: list int, n: Z
  PRE [ tptr tint, tint ]
    PROP (readable_share sh; 0 <= n <= Int.max_signed;
          Zlength contents = n)
    PARAMS (input; Vint (Int.repr n)) GLOBALS (gv)
    SEP (mem_mgr gv; data_at sh (tarray tint n) (map Vint contents) input)
  POST [ tint ]
    EX r: int,
    PROP () RETURN (Vint r)
    SEP (mem_mgr gv; data_at sh (tarray tint n) (map Vint contents) input).

Definition main_spec :=
 DECLARE _main
  WITH gv: globals
  PRE [ ] main_pre prog tt gv
  POST [ tint ]
    EX r: int, PROP () RETURN (Vint r) SEP (TT).

Definition Gprog : funspecs :=
  ltac:(with_library prog
    [sglib_dllist_add_spec; sglib_dllist_it_init_on_equal_spec;
     sglib_dllist_it_init_spec; sglib_dllist_it_next_spec;
     b1_spec; main_spec]).

(* ---------- Proofs ---------- *)

Lemma body_sglib_dllist_add:
  semax_body Vprog Gprog f_sglib_dllist_add sglib_dllist_add_spec.
Proof.
  start_function.
  unfold dll.
  destruct s as [| [p y] s']; simpl dlseg; simpl hd_ptr.
  - forward.
    forward_if
      (PROP () LOCAL (temp _list list; temp _elem elem)
       SEP (EX v: val, data_at sh (tptr t_dll) v list;
            dlseg nullval [(elem, x)] nullval)).
    + forward. forward. forward. forward. forward. forward.
      Exists elem. simpl dlseg. entailer!.
    + contradiction.
    + Intros v. forward. entailer!.
  - Intros.
    forward.
    forward_if
      (PROP () LOCAL (temp _list list; temp _elem elem)
       SEP (EX v: val, data_at sh (tptr t_dll) v list;
            dlseg nullval ((elem, x) :: (p, y) :: s') nullval)).
    + assert_PROP (isptr p) by entailer!. subst p. contradiction.
    + forward. forward. forward. forward. forward. forward.
      forward. forward. forward_if.
      * discriminate.
      * forward. Exists p. simpl dlseg. entailer!.
    + Intros v. forward. entailer!.
Qed.

Lemma body_sglib_dllist_it_next:
  semax_body Vprog Gprog f_sglib_dllist_it_next sglib_dllist_it_next_spec.
Proof.
  start_function.
  unfold dll.
  destruct H as [[-> ->] | [-> [Hs [-> ->]]]].
  - (* prevelem == NULL: return nextelem *)
    destruct s as [| [p y] s']; simpl hd_ptr; simpl tl.
    + forward. forward. forward.
      forward_if (PROP () LOCAL (temp _ce nullval; temp _it it)
        SEP (data_at sh t_it (cur, (nullval, (nullval, (nullval, eqv)))) it;
             dlseg q [] nullval)).
      * discriminate.
      * forward. entailer!.
      * forward_if (PROP () LOCAL (temp _ce nullval; temp _it it)
          SEP (data_at sh t_it
                 (cur, (nullval, (nullval, (nullval, eqv)))) it;
               dlseg q [] nullval)).
        -- discriminate.
        -- forward. forward. forward.
           forward_if (PROP () LOCAL (temp _ce nullval; temp _it it)
             SEP (data_at sh t_it
                    (cur, (nullval, (nullval, (nullval, eqv)))) it;
                  dlseg q [] nullval)).
           ++ discriminate.
           ++ forward. entailer!.
           ++ forward_if.
              ** discriminate.
              ** forward. entailer!.
        -- forward. forward.
    + simpl dlseg. Intros.
      forward. forward. forward.
      forward_if (PROP () LOCAL (temp _ce nullval; temp _it it)
        SEP (data_at sh t_it (cur, (nullval, (p, (nullval, eqv)))) it;
             data_at Ews t_dll (Vint y, (hd_or s' nullval, q)) p;
             malloc_token Ews t_dll p; dlseg p s' nullval)).
      * discriminate.
      * forward. entailer!.
      * forward_if (PROP () LOCAL (temp _ce p; temp _it it)
          SEP (data_at sh t_it
                 (cur, (nullval, (hd_or s' nullval, (nullval, eqv)))) it;
               data_at Ews t_dll (Vint y, (hd_or s' nullval, q)) p;
               malloc_token Ews t_dll p; dlseg p s' nullval)).
        -- discriminate.
        -- forward. forward. forward.
           forward_if (PROP () LOCAL (temp _ce p; temp _it it)
             SEP (data_at sh t_it
                    (cur, (nullval, (nullval, (nullval, eqv)))) it;
                  data_at Ews t_dll (Vint y, (hd_or s' nullval, q)) p;
                  malloc_token Ews t_dll p; dlseg p s' nullval)).
           ++ discriminate.
           ++ forward. entailer!.
           ++ forward_if.
              ** forward. forward. entailer!.
              ** assert_PROP (isptr p) by entailer!.
                 subst p. contradiction.
        -- forward. forward.
           unfold dll, hd_ptr; simpl tl; rewrite dlseg_cons; entailer!.
  - (* prevelem is the head: return it *)
    destruct s as [| [p y] s']; [contradiction |].
    simpl hd_ptr; simpl tl; simpl dlseg.
    Intros.
    forward. forward. forward.
    forward_if (PROP () LOCAL (temp _ce p; temp _it it)
      SEP (data_at sh t_it
             (cur, (nullval, (hd_or s' nullval, (nullval, eqv)))) it;
           data_at Ews t_dll (Vint y, (hd_or s' nullval, nullval)) p;
           malloc_token Ews t_dll p; dlseg p s' nullval)).
    + discriminate.
    + forward. entailer!.
    + forward_if (PROP () LOCAL (temp _ce p; temp _it it)
        SEP (data_at sh t_it
               (cur, (nullval, (hd_or s' nullval, (nullval, eqv)))) it;
             data_at Ews t_dll (Vint y, (hd_or s' nullval, nullval)) p;
             malloc_token Ews t_dll p; dlseg p s' nullval)).
      * forward. forward. entailer!.
      * assert_PROP (isptr p) by entailer!.
        subst p. contradiction.
      * forward. forward.
        unfold dll, hd_ptr; simpl tl; rewrite dlseg_cons; entailer!.
Qed.

Lemma body_sglib_dllist_it_init_on_equal:
  semax_body Vprog Gprog f_sglib_dllist_it_init_on_equal
    sglib_dllist_it_init_on_equal_spec.
Proof.
  start_function.
  destruct s as [| [p y] s'].
  - forward. forward. forward. forward.
    forward_if (PROP () LOCAL (temp _it it)
      SEP (data_at sh t_it (Vundef, (nullval, (nullval, (nullval, eqv)))) it;
           dll nullval [])).
    + discriminate.
    + forward. entailer!.
    + forward_call (sh, it, Vundef, nullval, nullval, eqv, nullval,
                    @nil (val * int)).
      { left; auto. }
      forward.
  - unfold dll at 1. rewrite dlseg_cons. Intros. simpl hd_ptr.
    forward. forward. forward. forward.
    forward_if (PROP () LOCAL (temp _it it)
      SEP (data_at sh t_it (Vundef, (p, (hd_ptr s', (nullval, eqv)))) it;
           dll nullval ((p, y) :: s'))).
    + forward. forward. unfold dll. rewrite dlseg_cons. entailer!.
    + assert_PROP (isptr p) by entailer!. subst p. contradiction.
    + forward_call (sh, it, Vundef, p, hd_ptr s', eqv, nullval,
                    (p, y) :: s').
      { right; simpl; repeat split; auto; discriminate. }
      forward.
Qed.

Lemma body_sglib_dllist_it_init:
  semax_body Vprog Gprog f_sglib_dllist_it_init sglib_dllist_it_init_spec.
Proof.
  start_function.
  forward_call (sh, it, nullval, s).
  forward.
Qed.

Lemma body_b1: semax_body Vprog Gprog f_b1 b1_spec.
Proof.
  start_function.
  forward. forward.
  (* Loop 1: build the list with malloc + sglib_dllist_add. *)
  forward_loop
    (EX k: Z, EX s: list (val * int),
     PROP (0 <= k <= n)
     LOCAL (temp _k (Vint (Int.repr k)); temp _last (Vint (Int.repr 0));
            lvar _the_list (tptr t_dll) v_the_list; lvar _it t_it v_it;
            temp _input__1 input; temp _n (Vint (Int.repr n)); gvars gv)
     SEP (mem_mgr gv; data_at sh (tarray tint n) (map Vint contents) input;
          data_at Tsh (tptr t_dll) (hd_ptr s) v_the_list; dll nullval s;
          data_at_ Tsh t_it v_it))
  continue:
    (EX k: Z, EX s: list (val * int),
     PROP (0 <= k < n)
     LOCAL (temp _k (Vint (Int.repr k)); temp _last (Vint (Int.repr 0));
            lvar _the_list (tptr t_dll) v_the_list; lvar _it t_it v_it;
            temp _input__1 input; temp _n (Vint (Int.repr n)); gvars gv)
     SEP (mem_mgr gv; data_at sh (tarray tint n) (map Vint contents) input;
          data_at Tsh (tptr t_dll) (hd_ptr s) v_the_list; dll nullval s;
          data_at_ Tsh t_it v_it))
  break:
    (EX s: list (val * int),
     PROP ()
     LOCAL (temp _last (Vint (Int.repr 0));
            lvar _the_list (tptr t_dll) v_the_list; lvar _it t_it v_it;
            temp _input__1 input; temp _n (Vint (Int.repr n)); gvars gv)
     SEP (mem_mgr gv; data_at sh (tarray tint n) (map Vint contents) input;
          data_at Tsh (tptr t_dll) (hd_ptr s) v_the_list; dll nullval s;
          data_at_ Tsh t_it v_it)).
  - forward. Exists 0 (@nil (val * int)).
    unfold dll, hd_ptr, hd_or, dlseg. entailer!.
  - Intros k s.
    forward_if.                         (* if (!(k < n)) break; *)
    2: { forward. Exists s. entailer!. }
    forward_call (t_dll, gv).           (* l = malloc(sizeof(dllist)); *)
    Intros l.
    if_tac.
    + forward_if.                       (* if (l == NULL) break; *)
      * forward. Exists s. entailer!.
      * congruence.
    + Intros.
      forward_if.
      { congruence. }
      forward.                          (* l->i = input[k]; *)
      forward.
      forward_call (Tsh, v_the_list, l, Znth k contents, Vundef, Vundef, s).
      Exists k ((l, Znth k contents) :: s). entailer!.
  - Intros k s. forward. Exists (k + 1) s. entailer!.
  - (* Loop 2: the forward walk along ptr_to_next. *)
    Intros s.
    forward_loop
      (EX s1: list (val * int), EX s2: list (val * int), EX r: int,
       PROP (s = s1 ++ s2)
       LOCAL (temp _l (hd_ptr s2); temp _last (Vint r);
              lvar _the_list (tptr t_dll) v_the_list; lvar _it t_it v_it;
              temp _input__1 input; temp _n (Vint (Int.repr n)); gvars gv)
       SEP (mem_mgr gv; data_at sh (tarray tint n) (map Vint contents) input;
            data_at Tsh (tptr t_dll) (hd_ptr s) v_the_list;
            dlseg nullval s1 (hd_ptr s2);
            dlseg (last_or nullval s1) s2 nullval;
            data_at_ Tsh t_it v_it))
    continue:
      (EX s1: list (val * int), EX s2: list (val * int), EX r: int,
       PROP (s = s1 ++ s2; s2 <> nil)
       LOCAL (temp _l (hd_ptr s2); temp _last (Vint r);
              lvar _the_list (tptr t_dll) v_the_list; lvar _it t_it v_it;
              temp _input__1 input; temp _n (Vint (Int.repr n)); gvars gv)
       SEP (mem_mgr gv; data_at sh (tarray tint n) (map Vint contents) input;
            data_at Tsh (tptr t_dll) (hd_ptr s) v_the_list;
            dlseg nullval s1 (hd_ptr s2);
            dlseg (last_or nullval s1) s2 nullval;
            data_at_ Tsh t_it v_it))
    break:
      (EX r: int,
       PROP ()
       LOCAL (temp _last (Vint r);
              lvar _the_list (tptr t_dll) v_the_list; lvar _it t_it v_it;
              temp _input__1 input; temp _n (Vint (Int.repr n)); gvars gv)
       SEP (mem_mgr gv; data_at sh (tarray tint n) (map Vint contents) input;
            data_at Tsh (tptr t_dll) (hd_ptr s) v_the_list; dll nullval s;
            data_at_ Tsh t_it v_it)).
    + forward. Exists (@nil (val * int)) s (Int.repr 0).
      unfold dll. simpl dlseg. entailer!.
    + Intros s1 s2 r.
      destruct s2 as [| [p y] s2].
      * forward_if.
        { discriminate. }
        forward. Exists r. rewrite app_nil_r in *. subst s.
        unfold dll. entailer!. apply derives_refl.
      * rewrite dlseg_cons. Intros.
        forward_if.
        2: { assert_PROP (isptr p) by entailer!. subst p. contradiction. }
        forward. Exists s1 ((p, y) :: s2) y.
        rewrite dlseg_cons. entailer!.
    + Intros s1 s2 r.
      destruct s2 as [| [p y] s2]; [contradiction |].
      rewrite dlseg_cons. Intros.
      forward.
      Exists (s1 ++ [(p, y)]) s2 r.
      rewrite last_or_snoc, <- app_assoc.
      change (hd_ptr ((p, y) :: s2)) with p.
      sep_apply (dlseg_snoc s1 nullval p y (hd_ptr s2)).
      entailer!.
    + (* Loop 3: free every element while iterating. *)
      Intros r.
      forward.
      forward_call (Tsh, v_it, s). forward.
      forward_loop
        (EX t: list (val * int), EX q: val,
         PROP ()
         LOCAL (temp _l (hd_ptr t); temp _last (Vint r);
                lvar _the_list (tptr t_dll) v_the_list; lvar _it t_it v_it;
                temp _input__1 input; temp _n (Vint (Int.repr n)); gvars gv)
         SEP (mem_mgr gv;
              data_at sh (tarray tint n) (map Vint contents) input;
              data_at Tsh (tptr t_dll) (hd_ptr s) v_the_list;
              iter_at (hd_ptr t) (hd_ptr (tl t)) v_it;
              dll q t))
      continue:
        (EX t: list (val * int), EX p: val,
         PROP ()
         LOCAL (temp _l p; temp _last (Vint r);
                lvar _the_list (tptr t_dll) v_the_list; lvar _it t_it v_it;
                temp _input__1 input; temp _n (Vint (Int.repr n)); gvars gv)
         SEP (mem_mgr gv;
              data_at sh (tarray tint n) (map Vint contents) input;
              data_at Tsh (tptr t_dll) (hd_ptr s) v_the_list;
              iter_at p (hd_ptr t) v_it;
              dll p t))
      break:
        (PROP ()
         LOCAL (temp _last (Vint r);
                lvar _the_list (tptr t_dll) v_the_list; lvar _it t_it v_it;
                temp _input__1 input; temp _n (Vint (Int.repr n)); gvars gv)
         SEP (mem_mgr gv;
              data_at sh (tarray tint n) (map Vint contents) input;
              data_at Tsh (tptr t_dll) (hd_ptr s) v_the_list;
              data_at_ Tsh t_it v_it)).
      * Exists s nullval. unfold iter_at, it_val. entailer!.
      * Intros t q. unfold iter_at, it_val.
        destruct t as [| [p y] t].
        -- forward_if.
           { discriminate. }
           forward. unfold dll. simpl dlseg. entailer!.
        -- unfold dll. rewrite dlseg_cons. Intros.
           forward_if.
           2: { assert_PROP (isptr p) by entailer!. subst p. contradiction. }
           forward_call (t_dll, p, gv).  (* free(l); *)
           { rewrite if_false by (intro; subst; contradiction). cancel. }
           Exists t p. unfold dll, iter_at, it_val. entailer!.
      * Intros t p. unfold iter_at, it_val.
        forward_call (Tsh, v_it, p, nullval, hd_ptr t, nullval, p, t).
        { left; auto. }
        forward. Exists t p. unfold iter_at, it_val. entailer!.
      * forward. Exists r. entailer!.
Qed.

Lemma body_main: semax_body Vprog Gprog f_main main_spec.
Proof.
  start_function.
  sep_apply (create_mem_mgr gv).
  forward_call (gv, Ews, gv _input, map Int.repr [6; 7; 3; 4], 4).
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
  semax_func_cons body_sglib_dllist_add.
  semax_func_cons body_sglib_dllist_it_init_on_equal.
  semax_func_cons body_sglib_dllist_it_init.
  semax_func_cons body_sglib_dllist_it_next.
  semax_func_cons body_b1.
  semax_func_cons body_main.
Qed.

Print Assumptions prog_correct.
