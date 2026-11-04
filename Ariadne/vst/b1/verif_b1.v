(* VST proof of benchmarks B1a + B1b (b1.c): sglib's doubly linked list.
   Every function in b1.c is verified (semax_body) and the whole program
   is verified (semax_prog prog_correct).  Memory safety, including the
   absence of use after free and double free, follows from VST's
   soundness theorem w.r.t. CompCert Clight; the frees are of malloc'd
   blocks because free's spec needs the block's malloc_token.

   Contracts are restricted as in the Frama-C version
   (../../bench/b1/b1.c): the list pointer passed to add / it_init is
   the head (its predecessor is NULL), the one passed to get_first /
   get_last is any node of a whole list (or NULL), and the iterator is
   used without a subcomparator.  Values are not tracked beyond what
   the shape needs: no functional correctness. *)
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

(* B1b: splitting a list at any node, for get_first / get_last and the
   backward walk. *)
Lemma hd_or_app_gen: forall a b (t: val),
  hd_or (a ++ b) t = hd_or a (hd_or b t).
Proof. intros. destruct a as [| [] ]; reflexivity. Qed.

Lemma dlseg_app_split: forall a b prev t,
  dlseg prev (a ++ b) t
  |-- dlseg prev a (hd_or b t) * dlseg (last_or prev a) b t.
Proof.
  induction a as [| [q x] a IH]; intros; simpl.
  - cancel.
  - rewrite hd_or_app_gen. sep_apply (IH b q t). cancel.
Qed.

Lemma dlseg_app_join: forall a b prev t,
  dlseg prev a (hd_or b t) * dlseg (last_or prev a) b t
  |-- dlseg prev (a ++ b) t.
Proof.
  induction a as [| [q x] a IH]; intros; simpl.
  - cancel.
  - rewrite hd_or_app_gen. sep_apply (IH b q t). cancel.
Qed.

(* Taking the last node off a segment (the backward walks). *)
Lemma dlseg_unsnoc: forall a prev p y t,
  dlseg prev (a ++ [(p, y)]) t
  |-- dlseg prev a p
      * data_at Ews t_dll (Vint y, (t, last_or prev a)) p
      * malloc_token Ews t_dll p.
Proof.
  intros. sep_apply (dlseg_app_split a [(p, y)] prev t).
  simpl. cancel.
Qed.

(* The last node of a non-empty segment is a pointer. *)
Lemma dlseg_last_ptr: forall a prev t, a <> nil ->
  dlseg prev a t |-- !! isptr (last_or prev a).
Proof.
  induction a as [| [q x] a IH]; intros prev t H; [contradiction |].
  rewrite dlseg_cons.
  change (last_or prev ((q, x) :: a)) with (last_or q a).
  destruct a as [| r a].
  - simpl last_or. entailer!.
  - sep_apply (IH q t). { discriminate. } entailer!.
Qed.

Lemma dlseg_last_pn: forall a t,
  dlseg nullval a t |-- !! is_pointer_or_null (last_or nullval a).
Proof.
  intros. destruct a as [| x a].
  - simpl. entailer!.
  - eapply derives_trans.
    { apply (dlseg_last_ptr (x :: a) nullval t). discriminate. }
    apply prop_derives. intro Hp.
    destruct (last_or nullval (x :: a)); try contradiction; simpl; auto.
Qed.

Lemma snoc_cases: forall a: list (val * int),
  a = nil \/ exists a' p y, a = a' ++ [(p, y)].
Proof.
  intros. destruct a as [| x a]; [left; auto | right].
  destruct (exists_last (l := x :: a)) as (a' & [p y] & E);
    [discriminate |].
  exists a', p, y. exact E.
Qed.

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

(* get_first / get_last (B1b): the argument is any node of a whole list
   s1 ++ s2, namely the head of s2, or NULL when s2 is empty.  NULL in
   gives NULL out; otherwise the result is the head (first_of) or the
   last node (last_of) of that same list, and the list is unchanged. *)
Definition first_of (s1 s2: list (val * int)) : val :=
  match s2 with nil => nullval | _ => hd_ptr (s1 ++ s2) end.
Definition last_of (s1 s2: list (val * int)) : val :=
  match s2 with nil => nullval | _ => last_or nullval (s1 ++ s2) end.

Lemma first_of_nil: forall s, first_of [] s = hd_ptr s.
Proof. destruct s; reflexivity. Qed.

Lemma last_of_nil: forall s, last_of [] s = last_or nullval s.
Proof. destruct s; reflexivity. Qed.

Definition sglib_dllist_get_first_spec :=
 DECLARE _sglib_dllist_get_first
  WITH s1: list (val * int), s2: list (val * int)
  PRE [ tptr t_dll ]
    PROP () PARAMS (hd_ptr s2) SEP (dll nullval (s1 ++ s2))
  POST [ tptr t_dll ]
    PROP () RETURN (first_of s1 s2) SEP (dll nullval (s1 ++ s2)).

Definition sglib_dllist_get_last_spec :=
 DECLARE _sglib_dllist_get_last
  WITH s1: list (val * int), s2: list (val * int)
  PRE [ tptr t_dll ]
    PROP () PARAMS (hd_ptr s2) SEP (dll nullval (s1 ++ s2))
  POST [ tptr t_dll ]
    PROP () RETURN (last_of s1 s2) SEP (dll nullval (s1 ++ s2)).

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
    [sglib_dllist_add_spec; sglib_dllist_get_first_spec;
     sglib_dllist_get_last_spec; sglib_dllist_it_init_on_equal_spec;
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

Lemma body_sglib_dllist_get_first:
  semax_body Vprog Gprog f_sglib_dllist_get_first
    sglib_dllist_get_first_spec.
Proof.
  start_function.
  unfold dll.
  forward.                              (* _dll_ = list; *)
  destruct s2 as [| [p y] s2]; simpl hd_ptr.
  - forward_if (PROP () LOCAL (temp __dll_ nullval)
      SEP (dlseg nullval (s1 ++ []) nullval)).
    + discriminate.
    + forward. entailer!.
    + forward. forward.
  - sep_apply (dlseg_app_split s1 ((p, y) :: s2) nullval nullval).
    rewrite dlseg_cons. Intros.
    forward_if (PROP () LOCAL (temp __dll_ (hd_ptr (s1 ++ (p, y) :: s2)))
      SEP (dlseg nullval (s1 ++ (p, y) :: s2) nullval)).
    + (* the walk along ptr_to_previous; a ++ b is the list, the
         current node is the head of b *)
      forward_loop
        (EX a: list (val * int), EX b: list (val * int),
         PROP (s1 ++ (p, y) :: s2 = a ++ b; b <> nil)
         LOCAL (temp __dll_ (hd_ptr b))
         SEP (dlseg nullval a (hd_ptr b);
              dlseg (last_or nullval a) b nullval))
      continue:
        (EX a: list (val * int), EX b: list (val * int),
         PROP (s1 ++ (p, y) :: s2 = a ++ b; b <> nil; a <> nil)
         LOCAL (temp __dll_ (hd_ptr b))
         SEP (dlseg nullval a (hd_ptr b);
              dlseg (last_or nullval a) b nullval)).
      * Exists s1 ((p, y) :: s2). rewrite dlseg_cons. entailer!.
      * Intros a b. destruct b as [| [q x] b]; [contradiction |].
        rewrite dlseg_cons. Intros. simpl hd_ptr.
        destruct (snoc_cases a) as [-> | (a' & r & z & ->)].
        -- simpl last_or.
           forward.                     (* t = _dll_->ptr_to_previous; *)
           forward_if.
           ++ discriminate.
           ++ forward. rewrite H0. simpl app. rewrite dlseg_cons.
              entailer!.
        -- rewrite last_or_snoc.
           sep_apply (dlseg_unsnoc a' nullval r z q). Intros.
           forward.                     (* t = _dll_->ptr_to_previous; *)
           forward_if.
           ++ forward. Exists (a' ++ [(r, z)]) ((q, x) :: b). simpl hd_ptr.
              rewrite dlseg_cons, last_or_snoc.
              sep_apply (dlseg_snoc a' nullval r z q).
              entailer!. destruct a'; discriminate.
           ++ assert_PROP (isptr r) by entailer!. subst r. contradiction.
      * Intros a b. destruct b as [| [q x] b]; [contradiction |].
        destruct (snoc_cases a) as [-> | (a' & r & z & ->)];
          [contradiction |].
        rewrite dlseg_cons. Intros. rewrite last_or_snoc. simpl hd_ptr.
        sep_apply (dlseg_unsnoc a' nullval r z q). Intros.
        forward.                        (* _dll_ = _dll_->ptr_to_previous *)
        Exists a' ((r, z) :: (q, x) :: b). simpl hd_ptr.
        rewrite !dlseg_cons. entailer!.
        rewrite H0, <- app_assoc. reflexivity.
    + assert_PROP (isptr p) by entailer!. subst p. contradiction.
    + forward. forward.
Qed.

Lemma body_sglib_dllist_get_last:
  semax_body Vprog Gprog f_sglib_dllist_get_last
    sglib_dllist_get_last_spec.
Proof.
  start_function.
  unfold dll.
  forward.                              (* _dll_ = list; *)
  destruct s2 as [| [p y] s2]; simpl hd_ptr.
  - forward_if (PROP () LOCAL (temp __dll_ nullval)
      SEP (dlseg nullval (s1 ++ []) nullval)).
    + discriminate.
    + forward. entailer!.
    + forward. forward.
  - sep_apply (dlseg_app_split s1 ((p, y) :: s2) nullval nullval).
    rewrite dlseg_cons. Intros.
    forward_if
      (PROP () LOCAL (temp __dll_ (last_or nullval (s1 ++ (p, y) :: s2)))
       SEP (dlseg nullval (s1 ++ (p, y) :: s2) nullval)).
    + (* the walk along ptr_to_next *)
      forward_loop
        (EX a: list (val * int), EX b: list (val * int),
         PROP (s1 ++ (p, y) :: s2 = a ++ b; b <> nil)
         LOCAL (temp __dll_ (hd_ptr b))
         SEP (dlseg nullval a (hd_ptr b);
              dlseg (last_or nullval a) b nullval))
      continue:
        (EX a: list (val * int), EX b: list (val * int),
         PROP (s1 ++ (p, y) :: s2 = a ++ b; tl b <> nil)
         LOCAL (temp __dll_ (hd_ptr b))
         SEP (dlseg nullval a (hd_ptr b);
              dlseg (last_or nullval a) b nullval)).
      * Exists s1 ((p, y) :: s2). rewrite dlseg_cons. entailer!.
      * Intros a b. destruct b as [| [q x] b]; [contradiction |].
        rewrite dlseg_cons. Intros. simpl hd_ptr.
        forward.                        (* t = _dll_->ptr_to_next; *)
        destruct b as [| [r z] b].
        -- simpl hd_or. forward_if.
           ++ discriminate.
           ++ forward. rewrite H0, last_or_snoc.
              sep_apply (dlseg_snoc a nullval q x nullval).
              simpl dlseg. entailer!.
        -- simpl hd_or. rewrite dlseg_cons. Intros.
           forward_if.
           ++ forward. Exists a ((q, x) :: (r, z) :: b). simpl hd_ptr.
              rewrite !dlseg_cons. entailer!. discriminate.
           ++ assert_PROP (isptr r) by entailer!. subst r. contradiction.
      * Intros a b. destruct b as [| [q x] b]; [contradiction |].
        rewrite dlseg_cons. Intros. simpl hd_ptr.
        forward.                        (* _dll_ = _dll_->ptr_to_next *)
        Exists (a ++ [(q, x)]) b. rewrite last_or_snoc.
        sep_apply (dlseg_snoc a nullval q x (hd_or b nullval)).
        entailer!.
        rewrite H0, <- app_assoc. reflexivity.
    + assert_PROP (isptr p) by entailer!. subst p. contradiction.
    + forward. forward.
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
  - (* Loop 2: the forward walk along ptr_to_next, from get_first. *)
    Intros s.
    forward.                            (* t = the_list; *)
    forward_call (@nil (val * int), s). (* t' = get_first(t); *)
    { simpl app. cancel. }
    forward.                            (* l = t'; *)
    rewrite first_of_nil, app_nil_l.
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
    + Exists (@nil (val * int)) s (Int.repr 0).
      unfold dll. simpl dlseg. entailer!. destruct s; reflexivity.
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
    + (* Loop 3: the backward walk along ptr_to_previous, from
         get_last (B1b).  a ++ b is the list, l the last node of a. *)
      Intros r0.
      forward.                          (* t = the_list; *)
      forward_call (@nil (val * int), s). (* t' = get_last(t); *)
      { simpl app. cancel. }
      forward.                          (* l = t'; *)
      rewrite last_of_nil, app_nil_l.
      unfold dll.
      forward_loop
        (EX a: list (val * int), EX b: list (val * int), EX r: int,
         PROP (s = a ++ b)
         LOCAL (temp _l (last_or nullval a); temp _last (Vint r);
                lvar _the_list (tptr t_dll) v_the_list; lvar _it t_it v_it;
                temp _input__1 input; temp _n (Vint (Int.repr n)); gvars gv)
         SEP (mem_mgr gv;
              data_at sh (tarray tint n) (map Vint contents) input;
              data_at Tsh (tptr t_dll) (hd_ptr s) v_the_list;
              dlseg nullval a (hd_ptr b);
              dlseg (last_or nullval a) b nullval;
              data_at_ Tsh t_it v_it))
      continue:
        (EX a: list (val * int), EX b: list (val * int), EX r: int,
         PROP (s = a ++ b; a <> nil)
         LOCAL (temp _l (last_or nullval a); temp _last (Vint r);
                lvar _the_list (tptr t_dll) v_the_list; lvar _it t_it v_it;
                temp _input__1 input; temp _n (Vint (Int.repr n)); gvars gv)
         SEP (mem_mgr gv;
              data_at sh (tarray tint n) (map Vint contents) input;
              data_at Tsh (tptr t_dll) (hd_ptr s) v_the_list;
              dlseg nullval a (hd_ptr b);
              dlseg (last_or nullval a) b nullval;
              data_at_ Tsh t_it v_it))
      break:
        (EX r: int,
         PROP ()
         LOCAL (temp _last (Vint r);
                lvar _the_list (tptr t_dll) v_the_list; lvar _it t_it v_it;
                temp _input__1 input; temp _n (Vint (Int.repr n)); gvars gv)
         SEP (mem_mgr gv;
              data_at sh (tarray tint n) (map Vint contents) input;
              data_at Tsh (tptr t_dll) (hd_ptr s) v_the_list; dll nullval s;
              data_at_ Tsh t_it v_it)).
      { Exists s (@nil (val * int)) r0. simpl dlseg. entailer!.
        split; [rewrite app_nil_r; auto | destruct s; reflexivity]. }
      { Intros a b r'.
        destruct (snoc_cases a) as [-> | (a' & q & x & ->)].
        - simpl last_or. forward_if.
          { discriminate. }
          forward. Exists r'. simpl in H1. subst s.
          unfold dll. simpl dlseg. entailer!.
        - rewrite last_or_snoc.
          sep_apply (dlseg_unsnoc a' nullval q x (hd_ptr b)). Intros.
          forward_if.
          2: { assert_PROP (isptr q) by entailer!. subst q. contradiction. }
          forward.                      (* last = l->i; *)
          Exists (a' ++ [(q, x)]) b x. rewrite last_or_snoc.
          sep_apply (dlseg_snoc a' nullval q x (hd_ptr b)).
          entailer!. destruct a'; discriminate. }
      { Intros a b r'.
        destruct (snoc_cases a) as [-> | (a' & q & x & ->)];
          [contradiction |].
        rewrite last_or_snoc.
        sep_apply (dlseg_unsnoc a' nullval q x (hd_ptr b)). Intros.
        assert_PROP (is_pointer_or_null (last_or nullval a')).
        { sep_apply (dlseg_last_pn a' q). entailer!. }
        forward.                        (* l = l->ptr_to_previous; *)
        Exists a' ((q, x) :: b) r'. rewrite dlseg_cons. simpl hd_ptr.
        entailer!. rewrite <- app_assoc. reflexivity. }
      (* Loop 4: free every element while iterating. *)
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
  semax_func_cons body_sglib_dllist_get_first.
  semax_func_cons body_sglib_dllist_get_last.
  semax_func_cons body_sglib_dllist_it_init_on_equal.
  semax_func_cons body_sglib_dllist_it_init.
  semax_func_cons body_sglib_dllist_it_next.
  semax_func_cons body_b1.
  semax_func_cons body_main.
Qed.

Print Assumptions prog_correct.
