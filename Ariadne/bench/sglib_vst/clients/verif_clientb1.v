Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import SglibVST.clientb1 SglibVST.spec_clientb1.
Require SglibVST.lib_clientb1.
(* the list-segment lemmas of lib_clientb1 (nodes_split, nodes_focus, ...);
   the body_* lemmas below shadow its library proofs *)
Import SglibVST.lib_clientb1.

Local Open Scope logic.

(* B1 uses no comparator. *)
Definition Rc_client : globals -> val -> mpred := fun _ _ => emp.

Definition b1_spec :=
 DECLARE _b1
  WITH gv: globals, sh: share, p: val, n: Z, contents: list Z
  PRE [ tptr tint, tint ]
    PROP (readable_share sh; Zlength contents = n; 0 <= n <= Int.max_signed)
    PARAMS (p; Vint (Int.repr n)) GLOBALS (gv)
    SEP (mem_mgr gv;
         data_at sh (tarray tint n) (map Vint (map Int.repr contents)) p)
  POST [ tint ]
    EX r: int,
    PROP ()
    RETURN (Vint r)
    SEP (mem_mgr gv;
         data_at sh (tarray tint n) (map Vint (map Int.repr contents)) p).

Definition main_spec :=
 DECLARE _main
  WITH gv: globals
  PRE [ ] main_pre prog tt gv
  POST [ tint ]
    PROP () RETURN (Vint (Int.repr 0))
    SEP (has_ext tt; mem_mgr gv;
         data_at Ews (tarray tint 5)
           (map Vint (map Int.repr [6;7;3;4;7])) (gv _input)).

Definition Gprog : funspecs :=
  ltac:(with_library prog [add_spec; get_first_spec; get_last_spec;
                           it_init_on_equal_spec Rc_client; it_init_spec;
                           it_next_spec Rc_client; b1_spec; main_spec]).

#[export] Existing Instance NullExtension.Espec.

(* ------------------------------------------------------------------ *)
(* Library functions, from lib_clientb1                                *)

Lemma subVG: tycontext_subVG Vprog (SglibVST.spec_clientb1.Gprog Rc_client)
                             Vprog Gprog.
Proof.
  split;
  [apply sub_option_get;
    let A1 := fresh "A1" in let A2 := fresh "A2" in
    set (A1 := make_tycontext_g Vprog (SglibVST.spec_clientb1.Gprog Rc_client));
    set (A2 := make_tycontext_g Vprog Gprog);
    compute in A1; compute in A2; subst A1 A2;
    repeat (apply Forall_cons; [reflexivity | ]);  apply Forall_nil
  | apply subsume_spec_get;
    let A1 := fresh "A1" in let A2 := fresh "A2" in
    set (A1 := make_tycontext_s (SglibVST.spec_clientb1.Gprog Rc_client));
    set (A2 := make_tycontext_s Gprog);
    let a := make_ground_PTree A1 in change A1 with a; clear A1;
    let a := make_ground_PTree A2 in change A2 with a; clear A2;
    repeat (apply Forall_cons; [apply subsumespec_refl | ]);
    apply Forall_nil ].
Qed.

Lemma body_add: semax_body Vprog Gprog f_sglib_dllist_add add_spec.
Proof. pose proof subVG. apply_semax_body (SglibVST.lib_clientb1.body_add Rc_client). Qed.

Lemma body_get_first:
  semax_body Vprog Gprog f_sglib_dllist_get_first get_first_spec.
Proof. pose proof subVG. apply_semax_body (SglibVST.lib_clientb1.body_get_first Rc_client). Qed.

Lemma body_get_last:
  semax_body Vprog Gprog f_sglib_dllist_get_last get_last_spec.
Proof. pose proof subVG. apply_semax_body (SglibVST.lib_clientb1.body_get_last Rc_client). Qed.

Lemma body_it_init_on_equal:
  semax_body Vprog Gprog f_sglib_dllist_it_init_on_equal
    (it_init_on_equal_spec Rc_client).
Proof. pose proof subVG. apply_semax_body (SglibVST.lib_clientb1.body_it_init_on_equal Rc_client). Qed.

Lemma body_it_init:
  semax_body Vprog Gprog f_sglib_dllist_it_init it_init_spec.
Proof. pose proof subVG. apply_semax_body (SglibVST.lib_clientb1.body_it_init Rc_client). Qed.

Lemma body_it_next:
  semax_body Vprog Gprog f_sglib_dllist_it_next (it_next_spec Rc_client).
Proof. pose proof subVG. apply_semax_body (SglibVST.lib_clientb1.body_it_next Rc_client). Qed.

(* ------------------------------------------------------------------ *)

(* Helpers for b1 *)

(* the malloc tokens of a sequence of nodes *)
Fixpoint toks (l: list val) : mpred :=
  match l with
  | nil => emp
  | x :: l' => malloc_token Ews t_dl x * toks l'
  end.

Lemma toks_app: forall l1 l2, toks (l1 ++ l2) = toks l1 * toks l2.
Proof.
  induction l1; intros; simpl.
  - rewrite emp_sepcon; auto.
  - rewrite IHl1, sepcon_assoc; auto.
Qed.

Lemma toks_focus: forall s c, 0 <= c < Zlength s ->
  toks s = toks (sublist 0 c s) * malloc_token Ews t_dl (Znth c s) *
           toks (sublist (c+1) (Zlength s) s).
Proof.
  intros.
  assert (E: s = sublist 0 c s ++ ([Znth c s] ++ sublist (c+1) (Zlength s) s))
    by list_solve.
  rewrite E at 1. rewrite !toks_app. simpl. rewrite sepcon_emp, sepcon_assoc. auto.
Qed.

Lemma toks_left: forall s b, 0 <= b < Zlength s ->
  toks (sublist 0 (b+1) s) = toks (sublist 0 b s) * malloc_token Ews t_dl (Znth b s).
Proof.
  intros. rewrite (sublist_split 0 b (b+1)) by lia.
  rewrite sublist_len_1 by lia. rewrite toks_app. simpl. rewrite sepcon_emp. auto.
Qed.

Lemma toks_right: forall s f, 0 <= f < Zlength s ->
  toks (sublist f (Zlength s) s) =
  malloc_token Ews t_dl (Znth f s) * toks (sublist (f+1) (Zlength s) s).
Proof.
  intros. rewrite (sublist_split f (f+1) (Zlength s)) by lia.
  rewrite sublist_len_1 by lia. rewrite toks_app. simpl. rewrite sepcon_emp. auto.
Qed.

Lemma toks_nil: forall s i, toks (sublist i i s) = emp.
Proof. intros. rewrite sublist_nil_gen by lia. reflexivity. Qed.

Lemma ins0: forall {A} {d: Inhabitant A} (x: A) l, ins 0 x l = x :: l.
Proof. intros. unfold ins. list_solve. Qed.

Lemma whole_nil: whole [] [].
Proof.
  unfold whole, prev_links, next_links. rewrite !Zlength_nil.
  split; [auto | split; intros; exfalso; lia].
Qed.

Lemma Znth_or_null_cons0: forall (x: val) s, Znth_or_null (x :: s) 0 = x.
Proof.
  intros. pose proof (Zlength_nonneg s).
  rewrite Znth_or_null_in by (rewrite Zlength_cons; lia).
  apply Znth_0_cons.
Qed.

Lemma at_node0: forall s, at_node s 0.
Proof.
  intros. destruct s. left; auto. right. pose proof (Zlength_nonneg s).
  rewrite Zlength_cons. lia.
Qed.

Lemma idx_next: forall s r, r = nullval \/ In r s ->
  exists i, 0 <= i <= Zlength s /\ r = Znth_or_null s i.
Proof.
  intros. destruct H as [-> | Hin].
  - exists (Zlength s). split. rep_lia. rewrite Znth_or_null_out by lia. auto.
  - apply In_Znth in Hin. destruct Hin as [i [? <-]]. exists i.
    split. lia. rewrite Znth_or_null_in by lia. auto.
Qed.

Lemma idx_prev: forall s r, r = nullval \/ In r s ->
  exists i, -1 <= i < Zlength s /\ r = Znth_or_null s i.
Proof.
  intros. destruct H as [-> | Hin].
  - exists (-1). split. rep_lia. rewrite Znth_or_null_out by lia. auto.
  - apply In_Znth in Hin. destruct Hin as [i [? <-]]. exists i.
    split. lia. rewrite Znth_or_null_in by lia. auto.
Qed.

Lemma cmp_env_null: forall e sh v,
  cmp_env Rc_client nullval e sh v = emp.
Proof. intros. unfold cmp_env. rewrite if_true by auto. auto. Qed.

Lemma cmp_state_null: forall gv, cmp_state Rc_client gv nullval = emp.
Proof. intros. unfold cmp_state. rewrite if_true by auto. auto. Qed.

(* the node the iteration has just returned, owned by the client *)
Definition cur (l: val) (v: node_v) : mpred :=
  if eq_dec l nullval then emp
  else malloc_token Ews t_dl l * data_at Ews t_dl v l.

Definition dv : node_v := (Vundef, (Vundef, Vundef)).

Lemma body_b1: semax_body Vprog Gprog f_b1 b1_spec.
Proof.
  start_function.
  forward. forward. forward.
  forward_loop
   (EX k: Z, EX s: list val, EX vs: list node_v,
    PROP (0 <= k <= n; Zlength s = k; whole s vs; Forall int_val (map pay vs))
    LOCAL (temp _k (Vint (Int.repr k)); temp _last (Vint (Int.repr 0));
           lvar _the_list (tptr (Tstruct _dllist noattr)) v_the_list;
           lvar _it (Tstruct _sglib_dllist_iterator noattr) v_it;
           temp _input__1 p; temp _n (Vint (Int.repr n)); gvars gv)
    SEP (mem_mgr gv;
         data_at Tsh (tptr (Tstruct _dllist noattr)) (Znth_or_null s 0) v_the_list;
         nodes Ews s vs 0 (Zlength s); toks s;
         data_at_ Tsh (Tstruct _sglib_dllist_iterator noattr) v_it;
         data_at sh (tarray tint n) (map Vint (map Int.repr contents)) p))
  continue:
   (EX k: Z, EX s: list val, EX vs: list node_v,
    PROP (0 <= k < n; Zlength s = (k + 1)%Z; whole s vs; Forall int_val (map pay vs))
    LOCAL (temp _k (Vint (Int.repr k)); temp _last (Vint (Int.repr 0));
           lvar _the_list (tptr (Tstruct _dllist noattr)) v_the_list;
           lvar _it (Tstruct _sglib_dllist_iterator noattr) v_it;
           temp _input__1 p; temp _n (Vint (Int.repr n)); gvars gv)
    SEP (mem_mgr gv;
         data_at Tsh (tptr (Tstruct _dllist noattr)) (Znth_or_null s 0) v_the_list;
         nodes Ews s vs 0 (Zlength s); toks s;
         data_at_ Tsh (Tstruct _sglib_dllist_iterator noattr) v_it;
         data_at sh (tarray tint n) (map Vint (map Int.repr contents)) p))
  break:
   (EX s: list val, EX vs: list node_v,
    PROP (whole s vs; Forall int_val (map pay vs))
    LOCAL (temp _last (Vint (Int.repr 0));
           lvar _the_list (tptr (Tstruct _dllist noattr)) v_the_list;
           lvar _it (Tstruct _sglib_dllist_iterator noattr) v_it;
           temp _input__1 p; temp _n (Vint (Int.repr n)); gvars gv)
    SEP (mem_mgr gv;
         data_at Tsh (tptr (Tstruct _dllist noattr)) (Znth_or_null s 0) v_the_list;
         nodes Ews s vs 0 (Zlength s); toks s;
         data_at_ Tsh (Tstruct _sglib_dllist_iterator noattr) v_it;
         data_at sh (tarray tint n) (map Vint (map Int.repr contents)) p)).
  { forward. Exists 0 (@nil val) (@nil node_v).
    rewrite Znth_or_null_out by (rewrite Zlength_nil; lia).
    rewrite nodes_empty by (rewrite Zlength_nil; lia). simpl toks.
    entailer!. apply whole_nil. }
  { Intros k s vs.
    forward_if
   (PROP (k < n)
    LOCAL (temp _k (Vint (Int.repr k)); temp _last (Vint (Int.repr 0));
           lvar _the_list (tptr (Tstruct _dllist noattr)) v_the_list;
           lvar _it (Tstruct _sglib_dllist_iterator noattr) v_it;
           temp _input__1 p; temp _n (Vint (Int.repr n)); gvars gv)
    SEP (mem_mgr gv;
         data_at Tsh (tptr (Tstruct _dllist noattr)) (Znth_or_null s 0) v_the_list;
         nodes Ews s vs 0 (Zlength s); toks s;
         data_at_ Tsh (Tstruct _sglib_dllist_iterator noattr) v_it;
         data_at sh (tarray tint n) (map Vint (map Int.repr contents)) p)).
    { forward. entailer!. }
    { forward. Exists s vs. entailer!. }
    { Intros. forward_call (t_dl, gv).
      Intros q.
      forward_if
       (PROP (q <> nullval)
        LOCAL (temp _l q; temp _k (Vint (Int.repr k)); temp _last (Vint (Int.repr 0));
               lvar _the_list (tptr (Tstruct _dllist noattr)) v_the_list;
               lvar _it (Tstruct _sglib_dllist_iterator noattr) v_it;
               temp _input__1 p; temp _n (Vint (Int.repr n)); gvars gv)
        SEP (mem_mgr gv; malloc_token Ews t_dl q; data_at_ Ews t_dl q;
             data_at Tsh (tptr (Tstruct _dllist noattr)) (Znth_or_null s 0) v_the_list;
             nodes Ews s vs 0 (Zlength s); toks s;
             data_at_ Tsh (Tstruct _sglib_dllist_iterator noattr) v_it;
             data_at sh (tarray tint n) (map Vint (map Int.repr contents)) p)).
      { destruct (eq_dec q nullval); entailer!. }
      { forward. Exists s vs. rewrite if_true by auto. entailer!. }
      { forward. rewrite if_false by auto. entailer!. }
      Intros.
      forward.
      forward.
      forward_call (Tsh, v_the_list, Ews, q, Vint (Int.repr (Znth k contents)),
                    (Vundef, Vundef), s, vs, 0).
      { apply at_node0. }
      Intros vs'.
      rewrite !ins0 in *.
      Exists k (q :: s) vs'.
      rewrite Znth_or_null_cons0.
      replace (Zlength (q :: s)) with (Zlength s + 1) by (rewrite Zlength_cons; lia).
      simpl toks.
      entailer!.
      match goal with Hm: map pay vs' = _ |- _ => rewrite Hm end.
      constructor; auto. exists (Int.repr (Znth (Zlength s) contents)); auto. } }
  { Intros k s vs. forward. Exists (k+1) s vs. entailer!. }
  (* ---- loop 2: forward from get_first ---- *)
  Intros s vs.
  match goal with Hw: whole s vs |- _ => destruct Hw as [Hlen [Hprev Hnext]] end.
  match goal with Hf: Forall int_val _ |- _ => rename Hf into Hint end.
  rewrite Forall_forall in Hint.
  assert_PROP (forall i, 0 <= i < Zlength s -> isptr (Znth i s)) as Hptr.
  { sep_apply (nodes_isptr Ews s vs 0 (Zlength s)). entailer!. }
  assert (Hpay: forall i, 0 <= i < Zlength s -> exists z, pay (Znth i vs) = Vint z).
  { intros i Hi. apply Hint. apply in_map. apply Znth_In.
    rewrite Hlen. exact Hi. }
  pose proof (Zlength_nonneg s) as Hs0.
  assert (Hpn0: is_pointer_or_null (Znth_or_null s 0))
    by (apply (Znth_or_null_pn s 0 0 (Zlength s)); auto; lia).
  forward.
  rewrite (nodes_split Ews s vs 0 (Z.min (0+1) (Zlength s)) (Zlength s)) by lia.
  flatten_sepcon_in_SEP.
  forward_call (Ews, s, vs, 0).
  { repeat match goal with |- _ /\ _ => split end; auto; try apply at_node0.
    eapply prev_links_sub; [eassumption | lia | lia]. }
  Intros r.
  try forward.
  destruct (idx_next s r ltac:(assumption)) as [i0 [Hi0 ->]].
  forward_loop
   (EX i: Z, EX last: int,
    PROP (0 <= i <= Zlength s)
    LOCAL (temp _l (Znth_or_null s i); temp _last (Vint last);
           lvar _the_list (tptr (Tstruct _dllist noattr)) v_the_list;
           lvar _it (Tstruct _sglib_dllist_iterator noattr) v_it;
           temp _input__1 p; temp _n (Vint (Int.repr n)); gvars gv)
    SEP (mem_mgr gv;
         data_at Tsh (tptr (Tstruct _dllist noattr)) (Znth_or_null s 0) v_the_list;
         nodes Ews s vs 0 (Zlength s); toks s;
         data_at_ Tsh (Tstruct _sglib_dllist_iterator noattr) v_it;
         data_at sh (tarray tint n) (map Vint (map Int.repr contents)) p))
  continue:
   (EX i: Z, EX last: int,
    PROP (0 <= i < Zlength s)
    LOCAL (temp _l (Znth i s); temp _last (Vint last);
           lvar _the_list (tptr (Tstruct _dllist noattr)) v_the_list;
           lvar _it (Tstruct _sglib_dllist_iterator noattr) v_it;
           temp _input__1 p; temp _n (Vint (Int.repr n)); gvars gv)
    SEP (mem_mgr gv;
         data_at Tsh (tptr (Tstruct _dllist noattr)) (Znth_or_null s 0) v_the_list;
         nodes Ews s vs 0 (Zlength s); toks s;
         data_at_ Tsh (Tstruct _sglib_dllist_iterator noattr) v_it;
         data_at sh (tarray tint n) (map Vint (map Int.repr contents)) p))
  break:
   (EX last: int,
    PROP ()
    LOCAL (temp _last (Vint last);
           lvar _the_list (tptr (Tstruct _dllist noattr)) v_the_list;
           lvar _it (Tstruct _sglib_dllist_iterator noattr) v_it;
           temp _input__1 p; temp _n (Vint (Int.repr n)); gvars gv)
    SEP (mem_mgr gv;
         data_at Tsh (tptr (Tstruct _dllist noattr)) (Znth_or_null s 0) v_the_list;
         nodes Ews s vs 0 (Zlength s); toks s;
         data_at_ Tsh (Tstruct _sglib_dllist_iterator noattr) v_it;
         data_at sh (tarray tint n) (map Vint (map Int.repr contents)) p)).
  { Exists i0 (Int.repr 0).
    rewrite (nodes_split Ews s vs 0 (Z.min (0+1) (Zlength s)) (Zlength s)) by lia.
    entailer!. }
  { Intros i last.
    destruct (zlt i (Zlength s)).
    - rewrite Znth_or_null_in by lia.
      rewrite (nodes_focus Ews s vs 0 i (Zlength s)) by lia.
      destruct (Hpay i ltac:(lia)) as [z Hz].
      destruct (Znth i vs) as [pi [ni qi]] eqn:Ei. unfold pay in Hz; simpl in Hz; subst pi.
      assert (isptr (Znth i s)) by (apply Hptr; lia).
      Intros.
      match goal with |- semax _ ?P _ _ => forward_if P end.
      + forward. entailer!.
      + forward. Exists last. rewrite (nodes_focus Ews s vs 0 i (Zlength s)) by lia.
        rewrite Ei. entailer!.
      + forward. Exists i z. rewrite (nodes_focus Ews s vs 0 i (Zlength s)) by lia.
        rewrite Ei. entailer!.
    - rewrite Znth_or_null_out by lia.
      forward_if (PROP (False) LOCAL () SEP ()).
      + discriminate.
      + forward. Exists last. entailer!. }
  { Intros i last.
    assert (Hn: nxt (Znth i vs) = Znth_or_null s (i+1)) by (apply Hnext; lia).
    assert (Hpn: is_pointer_or_null (Znth_or_null s (i+1)))
      by (apply (Znth_or_null_pn s (i+1) 0 (Zlength s)); auto; lia).
    rewrite (nodes_focus Ews s vs 0 i (Zlength s)) by lia.
    destruct (Znth i vs) as [pi [ni qi]] eqn:Ei. unfold nxt in Hn; simpl in Hn; subst ni.
    Intros.
    forward.
    Exists (i+1) last.
    rewrite (nodes_focus Ews s vs 0 i (Zlength s)) by lia.
    rewrite Ei. entailer!. }
  (* ---- loop 3: backward from get_last ---- *)
  Intros last0.
  clear dependent i0.
  forward.
  forward_call (Ews, s, vs, 0).
  { repeat match goal with |- _ /\ _ => split end; auto; try apply at_node0. }
  Intros r.
  try forward.
  destruct (idx_prev s r ltac:(assumption)) as [i0 [Hi0 ->]].
  forward_loop
   (EX i: Z, EX last: int,
    PROP (-1 <= i < Zlength s)
    LOCAL (temp _l (Znth_or_null s i); temp _last (Vint last);
           lvar _the_list (tptr (Tstruct _dllist noattr)) v_the_list;
           lvar _it (Tstruct _sglib_dllist_iterator noattr) v_it;
           temp _input__1 p; temp _n (Vint (Int.repr n)); gvars gv)
    SEP (mem_mgr gv;
         data_at Tsh (tptr (Tstruct _dllist noattr)) (Znth_or_null s 0) v_the_list;
         nodes Ews s vs 0 (Zlength s); toks s;
         data_at_ Tsh (Tstruct _sglib_dllist_iterator noattr) v_it;
         data_at sh (tarray tint n) (map Vint (map Int.repr contents)) p))
  continue:
   (EX i: Z, EX last: int,
    PROP (0 <= i < Zlength s)
    LOCAL (temp _l (Znth i s); temp _last (Vint last);
           lvar _the_list (tptr (Tstruct _dllist noattr)) v_the_list;
           lvar _it (Tstruct _sglib_dllist_iterator noattr) v_it;
           temp _input__1 p; temp _n (Vint (Int.repr n)); gvars gv)
    SEP (mem_mgr gv;
         data_at Tsh (tptr (Tstruct _dllist noattr)) (Znth_or_null s 0) v_the_list;
         nodes Ews s vs 0 (Zlength s); toks s;
         data_at_ Tsh (Tstruct _sglib_dllist_iterator noattr) v_it;
         data_at sh (tarray tint n) (map Vint (map Int.repr contents)) p))
  break:
   (EX last: int,
    PROP ()
    LOCAL (temp _last (Vint last);
           lvar _the_list (tptr (Tstruct _dllist noattr)) v_the_list;
           lvar _it (Tstruct _sglib_dllist_iterator noattr) v_it;
           temp _input__1 p; temp _n (Vint (Int.repr n)); gvars gv)
    SEP (mem_mgr gv;
         data_at Tsh (tptr (Tstruct _dllist noattr)) (Znth_or_null s 0) v_the_list;
         nodes Ews s vs 0 (Zlength s); toks s;
         data_at_ Tsh (Tstruct _sglib_dllist_iterator noattr) v_it;
         data_at sh (tarray tint n) (map Vint (map Int.repr contents)) p)).
  { Exists i0 last0. entailer!. }
  { Intros i last.
    destruct (zlt i 0).
    - rewrite Znth_or_null_out by lia.
      forward_if (PROP (False) LOCAL () SEP ()).
      + discriminate.
      + forward. Exists last. entailer!.
    - rewrite Znth_or_null_in by lia.
      rewrite (nodes_focus Ews s vs 0 i (Zlength s)) by lia.
      destruct (Hpay i ltac:(lia)) as [z Hz].
      destruct (Znth i vs) as [pi [ni qi]] eqn:Ei. unfold pay in Hz; simpl in Hz; subst pi.
      assert (isptr (Znth i s)) by (apply Hptr; lia).
      Intros.
      match goal with |- semax _ ?P _ _ => forward_if P end.
      + forward. entailer!.
      + forward. Exists last. rewrite (nodes_focus Ews s vs 0 i (Zlength s)) by lia.
        rewrite Ei. entailer!.
      + forward. Exists i z. rewrite (nodes_focus Ews s vs 0 i (Zlength s)) by lia.
        rewrite Ei. entailer!. }
  { Intros i last.
    assert (Hp: prv (Znth i vs) = Znth_or_null s (i-1)) by (apply Hprev; lia).
    assert (Hpn: is_pointer_or_null (Znth_or_null s (i-1)))
      by (apply (Znth_or_null_pn s (i-1) 0 (Zlength s)); auto; lia).
    rewrite (nodes_focus Ews s vs 0 i (Zlength s)) by lia.
    destruct (Znth i vs) as [pi [ni qi]] eqn:Ei. unfold prv in Hp; simpl in Hp; subst qi.
    Intros.
    forward.
    Exists (i-1) last.
    rewrite (nodes_focus Ews s vs 0 i (Zlength s)) by lia.
    rewrite Ei. entailer!. }
  (* ---- loop 4: free every node by an iteration ---- *)
  Intros last1.
  clear dependent i0.
  forward.
  forward_call (Tsh, v_it, Ews, s, vs, 0).
  { repeat match goal with |- _ /\ _ => split end; auto; try apply at_node0.
    eapply prev_links_sub; [eassumption | lia | lia]. }
  Intros vret. destruct vret as [[b f] r]. simpl fst in *. simpl snd in *.
  try forward.
  match goal with Hw: init_window _ _ _ _ _ |- _ =>
    destruct Hw as [Hbf [Hfl [_ [_ Hx]]]] end.
  forward_loop
   (EX b: Z, EX f: Z, EX c: Z, EX l: val,
    PROP (-1 <= b < f; f <= Zlength s;
          (l = nullval /\ b = -1 /\ f = Zlength s) \/ (b < c < f /\ l = Znth c s))
    LOCAL (temp _l l; temp _last (Vint last1);
           lvar _the_list (tptr (Tstruct _dllist noattr)) v_the_list;
           lvar _it (Tstruct _sglib_dllist_iterator noattr) v_it;
           temp _input__1 p; temp _n (Vint (Int.repr n)); gvars gv)
    SEP (mem_mgr gv;
         data_at Tsh (tptr (Tstruct _dllist noattr)) (Znth_or_null s 0) v_the_list;
         it_rep Tsh v_it s b f nullval nullval;
         nodes Ews s vs 0 (b+1); nodes Ews s vs f (Zlength s);
         toks (sublist 0 (b+1) s); toks (sublist f (Zlength s) s);
         cur l (Znth c vs);
         cmp_env Rc_client nullval nullval Tsh dv; cmp_state Rc_client gv nullval;
         data_at sh (tarray tint n) (map Vint (map Int.repr contents)) p))
  continue:
   (EX b: Z, EX f: Z,
    PROP (-1 <= b < f; f <= Zlength s)
    LOCAL (temp _last (Vint last1);
           lvar _the_list (tptr (Tstruct _dllist noattr)) v_the_list;
           lvar _it (Tstruct _sglib_dllist_iterator noattr) v_it;
           temp _input__1 p; temp _n (Vint (Int.repr n)); gvars gv)
    SEP (mem_mgr gv;
         data_at Tsh (tptr (Tstruct _dllist noattr)) (Znth_or_null s 0) v_the_list;
         it_rep Tsh v_it s b f nullval nullval;
         nodes Ews s vs 0 (b+1); nodes Ews s vs f (Zlength s);
         toks (sublist 0 (b+1) s); toks (sublist f (Zlength s) s);
         cmp_env Rc_client nullval nullval Tsh dv; cmp_state Rc_client gv nullval;
         data_at sh (tarray tint n) (map Vint (map Int.repr contents)) p))
  break:
   (PROP ()
    LOCAL (temp _last (Vint last1);
           lvar _the_list (tptr (Tstruct _dllist noattr)) v_the_list;
           lvar _it (Tstruct _sglib_dllist_iterator noattr) v_it;
           temp _input__1 p; temp _n (Vint (Int.repr n)); gvars gv)
    SEP (mem_mgr gv;
         data_at Tsh (tptr (Tstruct _dllist noattr)) (Znth_or_null s 0) v_the_list;
         data_at_ Tsh (Tstruct _sglib_dllist_iterator noattr) v_it;
         data_at sh (tarray tint n) (map Vint (map Int.repr contents)) p)).
  { rewrite cmp_env_null, cmp_state_null.
    destruct (Hx eq_refl) as [[-> [-> [-> ->]]] | [c [Hc [-> [-> ->]]]]].
    - Exists (-1) 0 0 nullval.
      unfold cur. rewrite if_true by auto.
      replace (-1+1) with 0 by lia.
      rewrite !nodes_empty by (rewrite ?Zlength_nil; lia).
      rewrite !toks_nil. simpl toks.
      entailer!.
    - Exists (c-1) (c+1) c (Znth c s).
      assert (isptr (Znth c s)) by (apply Hptr; lia).
      unfold cur. rewrite if_false by (intro Hn; rewrite Hn in *; contradiction).
      replace (c-1+1) with c by lia.
      rewrite (nodes_focus Ews s vs 0 c (Zlength s)) by lia.
      rewrite (toks_focus s c) by lia.
      entailer!.
      right; split; [lia | reflexivity]. }
  { clear dependent b; clear dependent f; clear dependent r.
    Intros b f c l.
    match goal with Hd: (l = nullval /\ _) \/ _ |- _ =>
      destruct Hd as [[-> [-> ->]] | [Hc ->]] end.
    - unfold cur. rewrite if_true by auto.
      forward_if (PROP (False) LOCAL () SEP ()).
      + discriminate.
      + forward.
        replace (-1+1) with 0 by lia.
        rewrite !nodes_empty by lia.
        rewrite !toks_nil.
        rewrite cmp_env_null, cmp_state_null.
        unfold it_rep. Intros cur0.
        entailer!.
    - assert (isptr (Znth c s)) by (apply Hptr; lia).
      unfold cur. rewrite if_false by (intro Hn; rewrite Hn in *; contradiction).
      Intros.
      match goal with |- semax _ ?P _ _ => forward_if P end.
      + forward. entailer!.
      + match goal with Hn: Znth c s = nullval |- _ => rewrite Hn in *; contradiction end.
      + forward_call (t_dl, Znth c s, gv).
        { rewrite if_false by (intro Hn; rewrite Hn in *; contradiction). cancel. }
        Exists b f. entailer!. }
  { clear dependent b; clear dependent f; clear dependent r.
    Intros b f.
    forward_call (gv, Tsh, v_it, Ews, s, vs, b, f, nullval, nullval, Tsh, dv).
    { repeat match goal with |- _ /\ _ => split end; auto; try lia;
        try (eapply prev_links_sub; [eassumption | lia | lia]);
        try (eapply next_links_sub; [eassumption | lia | lia]);
        try (left; reflexivity). }
    Intros vret. destruct vret as [[b' f'] r]. simpl fst in *. simpl snd in *.
    try forward.
    match goal with Hs: iter_step _ _ _ _ _ _ _ |- _ => destruct Hs as [_ Hex] end.
    specialize (Hex eq_refl). unfold step_exact in Hex.
    destruct Hex as [[-> [-> [-> [-> ->]]]] | [[Hb0 [-> [-> ->]]] | [Hf0 [-> [-> ->]]]]].
    - Exists (-1) (Zlength s) 0 nullval.
      unfold cur. rewrite if_true by auto.
      entailer!.
    - Exists (b-1) f b (Znth b s).
      assert (isptr (Znth b s)) by (apply Hptr; lia).
      unfold cur. rewrite if_false by (intro Hn; rewrite Hn in *; contradiction).
      replace (b-1+1) with b by lia.
      rewrite (nodes_split Ews s vs 0 b (b+1)) by lia. rewrite nodes_one.
      rewrite (toks_left s b) by lia.
      entailer!.
      right; split; [lia | reflexivity].
    - Exists b (f+1) f (Znth f s).
      assert (isptr (Znth f s)) by (apply Hptr; lia).
      unfold cur. rewrite if_false by (intro Hn; rewrite Hn in *; contradiction).
      rewrite (nodes_split Ews s vs f (f+1) (Zlength s)) by lia. rewrite nodes_one.
      rewrite (toks_right s f) by lia.
      entailer!.
      right; split; [lia | reflexivity]. }
  forward.
  Exists last1.
  entailer!.
Qed.

Lemma body_main: semax_body Vprog Gprog f_main main_spec.
Proof.
  start_function.
  sep_apply (create_mem_mgr gv).
  forward_call (gv, Ews, gv _input, 5, [6;7;3;4;7]).
  forward.
  cancel.
Qed.

Lemma prog_correct: semax_prog prog tt Vprog Gprog.
Proof.
  prove_semax_prog.
  semax_func_cons body_malloc. apply semax_func_cons_malloc_aux.
  semax_func_cons body_free.
  semax_func_cons body_add.
  semax_func_cons body_get_first.
  semax_func_cons body_get_last.
  semax_func_cons body_it_init_on_equal.
  semax_func_cons body_it_init.
  semax_func_cons body_it_next.
  semax_func_cons body_b1.
  semax_func_cons body_main.
Qed.

Print Assumptions prog_correct.
