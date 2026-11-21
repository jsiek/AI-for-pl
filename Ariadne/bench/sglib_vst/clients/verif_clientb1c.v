Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import SglibVST.clientb1c SglibVST.spec_clientb1c.
Require SglibVST.lib_clientb1c.
Import SglibVST.lib_clientb1c.

Local Open Scope logic.

(* This program uses no comparator. *)
Definition Rc_client : globals -> val -> mpred := fun _ _ => emp.

(* ================================================================== *)
(* Client-side helpers                                                *)
(* ================================================================== *)

Fixpoint tokl (l: list val) : mpred :=
  match l with
  | nil => emp
  | p :: l' => malloc_token Ews t_dl p * tokl l'
  end.

Lemma iter_sepcon_app: forall l1 l2, tokl (l1 ++ l2) = tokl l1 * tokl l2.
Proof.
  induction l1; intros; simpl.
  - rewrite emp_sepcon. auto.
  - rewrite IHl1. rewrite sepcon_assoc. auto.
Qed.

(* malloc tokens of nodes lo .. hi-1 *)
Definition toks (s: list val) (lo hi: Z) : mpred := tokl (sublist lo hi s).

Lemma toks_split: forall s lo m hi, 0 <= lo <= m -> m <= hi <= Zlength s ->
  toks s lo hi = toks s lo m * toks s m hi.
Proof.
  intros. unfold toks. rewrite (sublist_split lo m hi) by lia.
  apply iter_sepcon_app.
Qed.

Lemma toks_one: forall s i, 0 <= i < Zlength s ->
  toks s i (i+1) = malloc_token Ews t_dl (Znth i s).
Proof.
  intros. unfold toks. rewrite sublist_len_1 by lia. simpl. apply sepcon_emp.
Qed.

Lemma toks_empty: forall s i, toks s i i = emp.
Proof.
  intros. unfold toks. replace (sublist i i s) with (@nil val). reflexivity.
  unfold sublist. rewrite skipn_all2; auto. rewrite length_firstn. lia.
Qed.

Lemma toks_ins: forall s j e, 0 <= j <= Zlength s ->
  toks (ins j e s) 0 (Zlength s + 1) =
  toks s 0 j * malloc_token Ews t_dl e * toks s j (Zlength s).
Proof.
  intros. unfold toks.
  rewrite sublist_same by (rewrite ?Zlength_ins by lia; lia).
  unfold ins. rewrite iter_sepcon_app. simpl. rewrite sepcon_assoc. reflexivity.
Qed.

Lemma Znth_or_null_ins_at: forall j e s, 0 <= j <= Zlength s ->
  Znth_or_null (ins j e s) j = e.
Proof.
  intros. rewrite Znth_or_null_ins by auto.
  destruct (zlt j j); [lia|]. destruct (zeq j j); [auto|lia].
Qed.

Lemma at_node0: forall s, at_node s 0.
Proof.
  intros. unfold at_node. destruct s.
  - left; auto.
  - right. rewrite Zlength_cons. pose proof (Zlength_nonneg s). lia.
Qed.

Lemma whole_nil: whole [] [].
Proof.
  unfold whole, prev_links, next_links. rewrite !Zlength_nil.
  split; [auto|split; intros; lia].
Qed.

Lemma Forall_ins: forall {A} {d: Inhabitant A} (P: A -> Prop) j x l,
  Forall P l -> P x -> Forall P (ins j x l).
Proof.
  intros. unfold ins. apply Forall_app. split.
  - apply Forall_sublist; auto.
  - constructor; [auto | apply Forall_sublist; auto].
Qed.

Lemma pay_int: forall vs i, Forall int_val (map pay vs) -> 0 <= i < Zlength vs ->
  int_val (pay (Znth i vs)).
Proof.
  intros. rewrite Forall_forall in H. apply H.
  rewrite <- Znth_map by lia. apply Znth_In. rewrite Zlength_map. lia.
Qed.

Lemma it_rep_data_at_: forall sh it s b f scp eqp,
  it_rep sh it s b f scp eqp |-- data_at_ sh t_it it.
Proof. intros. unfold it_rep. Intros cur. apply data_at_data_at_. Qed.

Lemma cmp_env_null: forall sheq veq,
  cmp_env Rc_client nullval nullval sheq veq = emp.
Proof. intros. unfold cmp_env. rewrite if_true by auto. auto. Qed.

Lemma cmp_state_null: forall gv, cmp_state Rc_client gv nullval = emp.
Proof. intros. unfold cmp_state. rewrite if_true by auto. auto. Qed.

(* the node the free loop currently holds *)
Definition cur (s: list val) (vs: list node_v) (l: val) (ci: Z) : mpred :=
  if Val.eq l nullval then emp
  else data_at Ews t_dl (Znth ci vs) (Znth ci s) * malloc_token Ews t_dl (Znth ci s).

(* free-loop state: NULL only at the end; otherwise the newest node of
   the window, at one of its ends *)
Definition inv3 (s: list val) (b f: Z) (l: val) (ci: Z) : Prop :=
  (l = nullval -> b = -1 /\ f = Zlength s) /\
  (l <> nullval -> (ci = b+1 \/ ci = f-1) /\ b < ci < f /\ l = Znth ci s).

Lemma inv3_null: forall s, inv3 s (-1) (Zlength s) nullval 0.
Proof. intros. split; intros; [auto | contradiction]. Qed.

Lemma inv3_node: forall s b f ci, isptr (Znth ci s) ->
  (ci = b+1 \/ ci = f-1) -> b < ci < f -> inv3 s b f (Znth ci s) ci.
Proof.
  intros. split; intros.
  - destruct (Znth ci s); try contradiction; discriminate.
  - auto.
Qed.

(* ================================================================== *)
(* Specs                                                              *)
(* ================================================================== *)

Definition b1_spec :=
 DECLARE _b1
  WITH gv: globals, sh: share, inp: val, contents: list int
  PRE [ tptr tint, tint ]
    PROP (readable_share sh; Zlength contents <= Int.max_signed)
    PARAMS (inp; Vint (Int.repr (Zlength contents))) GLOBALS (gv)
    SEP (mem_mgr gv;
         data_at sh (tarray tint (Zlength contents)) (map Vint contents) inp)
  POST [ tuint ]
    EX r: int,
    PROP () RETURN (Vint r)
    SEP (mem_mgr gv;
         data_at sh (tarray tint (Zlength contents)) (map Vint contents) inp).

Definition main_spec :=
 DECLARE _main
  WITH gv: globals
  PRE [ ] main_pre prog tt gv
  POST [ tint ]
    PROP () RETURN (Vint (Int.repr 0))
    SEP (mem_mgr gv;
         data_at Ews (tarray tint 5) (map Vint (map Int.repr [6;7;3;4;7])) (gv _input);
         has_ext tt).

Definition Gprog : funspecs :=
  ltac:(with_library prog [add_spec; get_first_spec; get_last_spec;
                           it_init_on_equal_spec Rc_client; it_init_spec;
                           it_next_spec Rc_client; b1_spec; main_spec]).

#[export] Existing Instance NullExtension.Espec.

(* ================================================================== *)
(* Library functions: from lib_clientb1c                              *)
(* ================================================================== *)

Lemma subVG: tycontext_subVG Vprog (SglibVST.spec_clientb1c.Gprog Rc_client) Vprog Gprog.
Proof.
  split.
  - apply sub_option_get.
    set (A1 := make_tycontext_g Vprog (SglibVST.spec_clientb1c.Gprog Rc_client)).
    set (A2 := make_tycontext_g Vprog Gprog).
    compute in A1; compute in A2; subst A1 A2.
    repeat (apply Forall_cons; [reflexivity | ]); apply Forall_nil.
  - apply subsume_spec_get.
    set (A1 := make_tycontext_s (SglibVST.spec_clientb1c.Gprog Rc_client)).
    set (A2 := make_tycontext_s Gprog).
    let a := make_ground_PTree A1 in change A1 with a; clear A1.
    let a := make_ground_PTree A2 in change A2 with a; clear A2.
    repeat (apply Forall_cons; [apply subsumespec_refl | ]); apply Forall_nil.
Qed.

Ltac from_lib L :=
  eapply semax_body_subsumption; [apply L | apply tycontext_sub_i99; apply subVG].

Lemma body_add: semax_body Vprog Gprog f_sglib_dllist_add add_spec.
Proof. from_lib (SglibVST.lib_clientb1c.body_add Rc_client). Qed.
Lemma body_get_first: semax_body Vprog Gprog f_sglib_dllist_get_first get_first_spec.
Proof. from_lib (SglibVST.lib_clientb1c.body_get_first Rc_client). Qed.
Lemma body_get_last: semax_body Vprog Gprog f_sglib_dllist_get_last get_last_spec.
Proof. from_lib (SglibVST.lib_clientb1c.body_get_last Rc_client). Qed.
Lemma body_it_init_on_equal: semax_body Vprog Gprog f_sglib_dllist_it_init_on_equal
  (it_init_on_equal_spec Rc_client).
Proof. from_lib (SglibVST.lib_clientb1c.body_it_init_on_equal Rc_client). Qed.
Lemma body_it_init: semax_body Vprog Gprog f_sglib_dllist_it_init it_init_spec.
Proof. from_lib (SglibVST.lib_clientb1c.body_it_init Rc_client). Qed.
Lemma body_it_next: semax_body Vprog Gprog f_sglib_dllist_it_next (it_next_spec Rc_client).
Proof. from_lib (SglibVST.lib_clientb1c.body_it_next Rc_client). Qed.

(* ================================================================== *)
(* b1                                                                 *)
(* ================================================================== *)

Lemma body_b1: semax_body Vprog Gprog f_b1 b1_spec.
Proof.
  start_function.
  repeat forward.
  (* ---------------- loop 1: build ---------------- *)
  forward_loop
   (EX s: list val, EX vs: list node_v,
    PROP (Zlength s <= Zlength contents; whole s vs; Forall int_val (map pay vs))
    LOCAL (temp _k (Vint (Int.repr (Zlength s))); temp _m (Vint (Int.repr (Zlength s)));
           temp _mid nullval; temp _sum (Vint (Int.repr 0)); temp _c (Vint (Int.repr 0));
           temp _input__1 inp; temp _n (Vint (Int.repr (Zlength contents))); gvars gv;
           lvar _the_list (tptr (Tstruct _dllist noattr)) v_the_list;
           lvar _it (Tstruct _sglib_dllist_iterator noattr) v_it)
    SEP (data_at Tsh (tptr t_dl) (Znth_or_null s 0) v_the_list;
         data_at_ Tsh t_it v_it;
         nodes Ews s vs 0 (Zlength s); toks s 0 (Zlength s); mem_mgr gv;
         data_at sh (tarray tint (Zlength contents)) (map Vint contents) inp))
  continue:
   (EX k: Z, EX s: list val, EX vs: list node_v,
    PROP (Zlength s = (k + 1)%Z;0 <= k < Zlength contents; whole s vs;
          Forall int_val (map pay vs))
    LOCAL (temp _k (Vint (Int.repr k)); temp _m (Vint (Int.repr (k+1)));
           temp _mid nullval; temp _sum (Vint (Int.repr 0)); temp _c (Vint (Int.repr 0));
           temp _input__1 inp; temp _n (Vint (Int.repr (Zlength contents))); gvars gv;
           lvar _the_list (tptr (Tstruct _dllist noattr)) v_the_list;
           lvar _it (Tstruct _sglib_dllist_iterator noattr) v_it)
    SEP (data_at Tsh (tptr t_dl) (Znth_or_null s 0) v_the_list;
         data_at_ Tsh t_it v_it;
         nodes Ews s vs 0 (Zlength s); toks s 0 (Zlength s); mem_mgr gv;
         data_at sh (tarray tint (Zlength contents)) (map Vint contents) inp))
  break:
   (EX s: list val, EX vs: list node_v,
    PROP (Zlength s <= Zlength contents; whole s vs; Forall int_val (map pay vs))
    LOCAL (temp _m (Vint (Int.repr (Zlength s)));
           temp _mid nullval; temp _sum (Vint (Int.repr 0)); temp _c (Vint (Int.repr 0));
           gvars gv;
           lvar _the_list (tptr (Tstruct _dllist noattr)) v_the_list;
           lvar _it (Tstruct _sglib_dllist_iterator noattr) v_it)
    SEP (data_at Tsh (tptr t_dl) (Znth_or_null s 0) v_the_list;
         data_at_ Tsh t_it v_it;
         nodes Ews s vs 0 (Zlength s); toks s 0 (Zlength s); mem_mgr gv;
         data_at sh (tarray tint (Zlength contents)) (map Vint contents) inp)).
  { forward.
    Exists (@nil val) (@nil node_v).
    change (Zlength (@nil val)) with 0.
    rewrite Znth_or_null_out by (change (Zlength (@nil val)) with 0; lia).
    rewrite nodes_empty by lia. rewrite toks_empty.
    pose proof whole_nil.
    entailer!. }
  { Intros s vs.
    forward_if.
    - forward_call (t_dl, gv).
      Intros l.
      assert_PROP (is_pointer_or_null l) by (if_tac; entailer!).
      forward_if.
      + if_tac; entailer!.
      + rewrite if_true by auto. forward. Exists s vs. entailer!.
      + rewrite if_false by auto. Intros.
        change (data_at_ Ews t_dl l) with (data_at Ews t_dl (Vundef, (Vundef, Vundef)) l).
        forward.
        { pose proof (Zlength_nonneg s). entailer!. }
        forward.
        pose proof (at_node0 s).
        forward_call (Tsh, v_the_list, Ews, l, Vint (Znth (Zlength s) contents),
                      (Vundef, Vundef), s, vs, 0).
        Intros vs'.
        forward.
        Exists (Zlength s) (ins 0 l s) vs'.
        pose proof (Zlength_nonneg s).
        rewrite Zlength_ins by lia.
        rewrite toks_ins by lia. rewrite toks_empty.
        rewrite Znth_or_null_ins_at by lia.
        assert (Forall int_val (map pay vs')).
        { match goal with H: map pay vs' = _ |- _ => rewrite H end.
          apply Forall_ins; auto.
          eexists; reflexivity. }
        entailer!.
    - forward. Exists s vs. entailer!. }
  { Intros k s vs. forward. Exists s vs.
    replace (k+1) with (Zlength s) by lia.
    entailer!. }
  (* ---------------- loop 2: sum, find mid ---------------- *)
  Intros s vs.
  match goal with H: whole s vs |- _ => assert (Hw := H); destruct H as [Hlen [Hprev Hnext]] end.
  assert_PROP (forall i, 0 <= i < Zlength s -> isptr (Znth i s)) as Hptr.
  { sep_apply (nodes_isptr Ews s vs 0 (Zlength s)). entailer!. }
  forward.
  { entailer!. apply (Znth_or_null_pn _ _ _ _ Hptr); lia. }
  pose proof (at_node0 s).
  assert (prev_links s vs 0 (Z.min (0+1) (Zlength s)))
    by (eapply prev_links_sub; [exact Hprev | lia | lia]).
  forward_call (Tsh, v_it, Ews, s, vs, 0).
  Intros vret. destruct vret as [[b0 f0] r0]. simpl fst in *. simpl snd in *.
  forward.
  match goal with H: init_window _ _ _ _ _ |- _ =>
    destruct H as [Hb0 [Hf0 [Hr0 [Hrn0 _]]]] end.
  forward_loop
   (EX b: Z, EX f: Z, EX l: val, EX sum: int, EX c: int, EX mid: val,
    PROP (-1 <= b < f; f <= Zlength s; l = nullval -> b = -1 /\ f = Zlength s;
          l = nullval \/ (exists ci, b < ci < f /\ l = Znth ci s);
          mid = nullval \/ (exists i, 0 <= i < Zlength s /\ mid = Znth i s))
    LOCAL (temp _l l; temp _sum (Vint sum); temp _c (Vint c);
           temp _m (Vint (Int.repr (Zlength s))); temp _mid mid; gvars gv;
           lvar _the_list (tptr (Tstruct _dllist noattr)) v_the_list;
           lvar _it (Tstruct _sglib_dllist_iterator noattr) v_it)
    SEP (data_at Tsh (tptr t_dl) (Znth_or_null s 0) v_the_list;
         it_rep Tsh v_it s b f nullval nullval;
         nodes Ews s vs 0 (Zlength s); toks s 0 (Zlength s); mem_mgr gv;
         data_at sh (tarray tint (Zlength contents)) (map Vint contents) inp))
  continue:
   (EX b: Z, EX f: Z, EX sum: int, EX c: int, EX mid: val,
    PROP (-1 <= b < f; f <= Zlength s;
          mid = nullval \/ (exists i, 0 <= i < Zlength s /\ mid = Znth i s))
    LOCAL (temp _sum (Vint sum); temp _c (Vint c);
           temp _m (Vint (Int.repr (Zlength s))); temp _mid mid; gvars gv;
           lvar _the_list (tptr (Tstruct _dllist noattr)) v_the_list;
           lvar _it (Tstruct _sglib_dllist_iterator noattr) v_it)
    SEP (data_at Tsh (tptr t_dl) (Znth_or_null s 0) v_the_list;
         it_rep Tsh v_it s b f nullval nullval;
         nodes Ews s vs 0 (Zlength s); toks s 0 (Zlength s); mem_mgr gv;
         data_at sh (tarray tint (Zlength contents)) (map Vint contents) inp))
  break:
   (EX sum: int, EX mid: val,
    PROP (mid = nullval \/ (exists i, 0 <= i < Zlength s /\ mid = Znth i s))
    LOCAL (temp _sum (Vint sum); temp _mid mid; gvars gv;
           lvar _the_list (tptr (Tstruct _dllist noattr)) v_the_list;
           lvar _it (Tstruct _sglib_dllist_iterator noattr) v_it)
    SEP (data_at Tsh (tptr t_dl) (Znth_or_null s 0) v_the_list;
         data_at_ Tsh t_it v_it;
         nodes Ews s vs 0 (Zlength s); toks s 0 (Zlength s); mem_mgr gv;
         data_at sh (tarray tint (Zlength contents)) (map Vint contents) inp)).
  { Exists b0 f0 r0 (Int.repr 0) (Int.repr 0) nullval. entailer!. }
  { Intros b f l sum c mid.
    assert (is_pointer_or_null l).
    { match goal with H: l = nullval \/ _ |- _ => destruct H as [-> | [ci [Hci ->]]] end.
      - simpl; auto.
      - apply isptr_is_pointer_or_null. apply Hptr. lia. }
    forward_if.
    - match goal with H: l = nullval \/ _ |- _ => destruct H as [-> | [ci [Hci ->]]] end.
      + entailer!.
      + rewrite (nodes_focus Ews s vs 0 ci (Zlength s)) by lia. entailer!.
    - match goal with H: l = nullval \/ _ |- _ => destruct H as [-> | [ci [Hci ->]]] end.
      { contradiction. }
      destruct (pay_int vs ci) as [iv Hiv]; auto; try lia.
      rewrite (nodes_focus Ews s vs 0 ci (Zlength s)) by lia. Intros.
      destruct (Znth ci vs) as [pv [nv qv]] eqn:Eci. simpl in Hiv. subst pv.
      forward.
      forward.
      match goal with |- context [temp _sum (Vint ?v)] => remember v as sum' eqn:Hsum' end.
      forward_if
       (EX mid': val,
        PROP (mid' = nullval \/ (exists i, 0 <= i < Zlength s /\ mid' = Znth i s))
        LOCAL (temp _mid mid'; temp _sum (Vint sum'); temp _c (Vint c);
               temp _m (Vint (Int.repr (Zlength s))); gvars gv;
               lvar _the_list (tptr (Tstruct _dllist noattr)) v_the_list;
               lvar _it (Tstruct _sglib_dllist_iterator noattr) v_it)
        SEP (data_at Tsh (tptr t_dl) (Znth_or_null s 0) v_the_list;
             it_rep Tsh v_it s b f nullval nullval;
             nodes Ews s vs 0 ci; data_at Ews t_dl (Vint iv, (nv, qv)) (Znth ci s);
             nodes Ews s vs (ci + 1) (Zlength s);
             toks s 0 (Zlength s); mem_mgr gv;
             data_at sh (tarray tint (Zlength contents)) (map Vint contents) inp))%assert.
      + forward. Exists (Znth ci s). entailer!. right. exists ci. split; [lia|auto].
      + forward. Exists mid. entailer!.
      + Intros mid'.
        forward.
        Exists b f sum' (Int.add c (Int.repr 1)) mid'.
        entailer!.
    - forward. Exists sum mid.
      sep_apply it_rep_data_at_. entailer!. }
  { Intros b f sum c mid.
    rewrite (nodes_split Ews s vs 0 (b+1) (Zlength s)) by lia.
    rewrite (nodes_split Ews s vs (b+1) f (Zlength s)) by lia.
    assert (prev_links s vs 0 (b+1)) by (eapply prev_links_sub; [exact Hprev | lia | lia]).
    assert (next_links s vs f (Zlength s)) by (eapply next_links_sub; [exact Hnext | lia | lia]).
    assert (cmp_payloads nullval vs 0 (b+1)) by (left; auto).
    assert (cmp_payloads nullval vs f (Zlength s)) by (left; auto).
    forward_call (gv, Tsh, v_it, Ews, s, vs, b, f, nullval, nullval, Ews,
                  (Vundef, (Vundef, Vundef))).
    { rewrite cmp_env_null, cmp_state_null. cancel. }
    Intros vret. destruct vret as [[b' f'] r]. simpl fst in *. simpl snd in *.
    rewrite cmp_env_null, cmp_state_null.
    forward.
    match goal with H: iter_step _ _ _ _ _ _ _ |- _ =>
      destruct H as [[Hb' [Hf' [Hr Hrn]]] _] end.
    Exists b' f' r sum c mid.
    rewrite (nodes_split Ews s vs 0 (b+1) (Zlength s)) by lia.
    rewrite (nodes_split Ews s vs (b+1) f (Zlength s)) by lia.
    assert (r = nullval \/ (exists ci, b' < ci < f' /\ r = Znth ci s)).
    { destruct Hr as [?|[ci [? [? ?]]]]; [left; auto | right; exists ci; split; auto]. }
    entailer!. }
  (* ---------------- add before mid ---------------- *)
  Intros sum mid.
  assert (is_pointer_or_null mid).
  { match goal with H: mid = nullval \/ _ |- _ => destruct H as [-> | [im [Him ->]]] end.
    - simpl; auto.
    - apply isptr_is_pointer_or_null. apply Hptr. lia. }
  forward_if
   (EX s2: list val, EX vs2: list node_v, EX j: Z,
    PROP (whole s2 vs2; at_node s2 j)
    LOCAL (temp _sum (Vint sum); gvars gv;
           lvar _the_list (tptr (Tstruct _dllist noattr)) v_the_list;
           lvar _it (Tstruct _sglib_dllist_iterator noattr) v_it)
    SEP (data_at Tsh (tptr t_dl) (Znth_or_null s2 j) v_the_list;
         data_at_ Tsh t_it v_it;
         nodes Ews s2 vs2 0 (Zlength s2); toks s2 0 (Zlength s2); mem_mgr gv;
         data_at sh (tarray tint (Zlength contents)) (map Vint contents) inp))%assert.
  { match goal with H: mid = nullval \/ _ |- _ => destruct H as [-> | [im [Him ->]]] end.
    + entailer!.
    + rewrite (nodes_focus Ews s vs 0 im (Zlength s)) by lia. entailer!. }
  { match goal with H: mid = nullval \/ _ |- _ => destruct H as [-> | [im [Him ->]]] end.
    { contradiction. }
    forward_call (t_dl, gv).
    Intros e.
    assert_PROP (is_pointer_or_null e) by (if_tac; entailer!).
    forward_if.
    - if_tac; entailer!.
    - rewrite if_false by auto. Intros.
      change (data_at_ Ews t_dl e) with (data_at Ews t_dl (Vundef, (Vundef, Vundef)) e).
      forward.
      forward.
      rewrite <- (Znth_or_null_in s im) by lia.
      assert (at_node s im) by (right; lia).
      forward_call (Tsh, v_the_list, Ews, e, Vint (Int.repr 0), (Vundef, Vundef), s, vs, im).
      Intros vs2.
      Exists (ins im e s) vs2 im.
      rewrite Zlength_ins by lia. rewrite toks_ins by lia.
      rewrite Znth_or_null_ins_at by lia.
      rewrite (toks_split s 0 im (Zlength s)) by lia.
      assert (at_node (ins im e s) im) by (right; rewrite Zlength_ins by lia; lia).
      entailer!.
    - rewrite if_true by auto. forward. Exists s vs 0.
      pose proof (at_node0 s). entailer!. }
  { forward. Exists s vs 0. pose proof (at_node0 s). entailer!. }
  (* ---------------- loop 3: free ---------------- *)
  clear dependent s. clear dependent vs. clear dependent b0. clear dependent f0.
  clear dependent r0.
  Intros s vs j.
  match goal with H: whole s vs |- _ => assert (Hw := H); destruct H as [Hlen [Hprev Hnext]] end.
  assert_PROP (forall i, 0 <= i < Zlength s -> isptr (Znth i s)) as Hptr.
  { sep_apply (nodes_isptr Ews s vs 0 (Zlength s)). entailer!. }
  assert (Hj: 0 <= j <= Zlength s).
  { match goal with H: at_node s j |- _ => destruct H as [[-> ->]|?] end;
    [rewrite Zlength_nil; lia | lia]. }
  forward.
  { entailer!. apply (Znth_or_null_pn _ _ _ _ Hptr); lia. }
  assert (prev_links s vs 0 (Z.min (j+1) (Zlength s)))
    by (eapply prev_links_sub; [exact Hprev | lia | lia]).
  assert (next_links s vs j (Zlength s))
    by (eapply next_links_sub; [exact Hnext | lia | lia]).
  forward_call (Tsh, v_it, Ews, s, vs, j).
  Intros vret. destruct vret as [[b0 f0] r0]. simpl fst in *. simpl snd in *.
  forward.
  match goal with H: init_window _ _ _ _ _ |- _ =>
    destruct H as [Hb0 [Hf0 [Hr0 [Hrn0 Hex0]]]] end.
  specialize (Hex0 eq_refl).
  forward_loop
   (EX b: Z, EX f: Z, EX l: val, EX ci: Z,
    PROP (-1 <= b < f; f <= Zlength s; inv3 s b f l ci)
    LOCAL (temp _l l; temp _sum (Vint sum); gvars gv;
           lvar _the_list (tptr (Tstruct _dllist noattr)) v_the_list;
           lvar _it (Tstruct _sglib_dllist_iterator noattr) v_it)
    SEP (data_at Tsh (tptr t_dl) (Znth_or_null s j) v_the_list;
         it_rep Tsh v_it s b f nullval nullval;
         nodes Ews s vs 0 (b+1); toks s 0 (b+1);
         nodes Ews s vs f (Zlength s); toks s f (Zlength s);
         cur s vs l ci; mem_mgr gv;
         data_at sh (tarray tint (Zlength contents)) (map Vint contents) inp))
  continue:
   (EX b: Z, EX f: Z,
    PROP (-1 <= b < f; f <= Zlength s)
    LOCAL (temp _sum (Vint sum); gvars gv;
           lvar _the_list (tptr (Tstruct _dllist noattr)) v_the_list;
           lvar _it (Tstruct _sglib_dllist_iterator noattr) v_it)
    SEP (data_at Tsh (tptr t_dl) (Znth_or_null s j) v_the_list;
         it_rep Tsh v_it s b f nullval nullval;
         nodes Ews s vs 0 (b+1); toks s 0 (b+1);
         nodes Ews s vs f (Zlength s); toks s f (Zlength s);
         mem_mgr gv;
         data_at sh (tarray tint (Zlength contents)) (map Vint contents) inp))
  break:
   (PROP ()
    LOCAL (temp _sum (Vint sum); gvars gv;
           lvar _the_list (tptr (Tstruct _dllist noattr)) v_the_list;
           lvar _it (Tstruct _sglib_dllist_iterator noattr) v_it)
    SEP (data_at_ Tsh (tptr t_dl) v_the_list;
         data_at_ Tsh t_it v_it; mem_mgr gv;
         data_at sh (tarray tint (Zlength contents)) (map Vint contents) inp)).
  { destruct Hex0 as [[-> [-> [-> ->]]] | [c [Hc [-> [-> ->]]]]].
    - Exists (-1) 0 nullval 0.
      unfold cur. rewrite if_true by auto.
      pose proof (inv3_null []) as Hi.
      change (Zlength (@nil val)) with 0 in *.
      replace (-1+1) with 0 by lia.
      entailer!.
    - assert (isptr (Znth c s)) by (apply Hptr; lia).
      Exists (c-1) (c+1) (Znth c s) c.
      unfold cur. rewrite if_false by (intro Hn; rewrite Hn in *; contradiction).
      pose proof (inv3_node s (c-1) (c+1) c ltac:(auto) ltac:(lia) ltac:(lia)).
      replace (c-1+1) with c by lia.
      rewrite (nodes_focus Ews s vs 0 c (Zlength s)) by lia.
      rewrite (toks_split s 0 c (Zlength s)) by lia.
      rewrite (toks_split s c (c+1) (Zlength s)) by lia.
      rewrite toks_one by lia.
      entailer!. }
  { Intros b f l ci.
    match goal with H: inv3 _ _ _ _ _ |- _ => destruct H as [Hnull Hnn] end.
    assert (is_pointer_or_null l).
    { destruct (Val.eq l nullval) as [-> | Hn]; [simpl; auto|].
      destruct (Hnn Hn) as [_ [? ->]].
      apply isptr_is_pointer_or_null. apply Hptr. lia. }
    forward_if.
    - destruct (Val.eq l nullval) as [-> | Hn]; [entailer! |].
      destruct (Hnn Hn) as [_ [? ->]].
      unfold cur. rewrite if_false by auto. entailer!.
    - match goal with Hn: l <> nullval |- _ =>
        destruct (Hnn Hn) as [Hci [Hbc ->]] end.
      unfold cur. rewrite if_false by auto. Intros.
      forward_call (t_dl, Znth ci s, gv).
      { rewrite if_false by auto. cancel. }
      Exists b f. entailer!.
    - match goal with Hn: l = nullval |- _ =>
        destruct (Hnull Hn) as [-> ->] end.
      subst l.
      forward.
      unfold cur. rewrite if_true by auto.
      replace (-1+1) with 0 by lia.
      rewrite nodes_empty by lia. rewrite nodes_empty by lia.
      rewrite !toks_empty.
      sep_apply it_rep_data_at_.
      sep_apply (data_at_data_at_ Tsh (tptr t_dl) (Znth_or_null s j) v_the_list).
      entailer!. }
  { Intros b f.
    assert (prev_links s vs 0 (b+1)) by (eapply prev_links_sub; [exact Hprev | lia | lia]).
    assert (next_links s vs f (Zlength s)) by (eapply next_links_sub; [exact Hnext | lia | lia]).
    assert (cmp_payloads nullval vs 0 (b+1)) by (left; auto).
    assert (cmp_payloads nullval vs f (Zlength s)) by (left; auto).
    forward_call (gv, Tsh, v_it, Ews, s, vs, b, f, nullval, nullval, Ews,
                  (Vundef, (Vundef, Vundef))).
    { rewrite cmp_env_null, cmp_state_null. cancel. }
    Intros vret. destruct vret as [[b' f'] r]. simpl fst in *. simpl snd in *.
    rewrite cmp_env_null, cmp_state_null.
    forward.
    match goal with H: iter_step _ _ _ _ _ _ _ |- _ =>
      destruct H as [_ Hex]; specialize (Hex eq_refl) end.
    destruct Hex as [[-> [-> [-> [-> ->]]]] | [[Hb [-> [-> ->]]] | [Hf [-> [-> ->]]]]].
    - Exists (-1) (Zlength s) nullval 0.
      unfold cur. rewrite if_true by auto.
      pose proof (inv3_null s).
      entailer!.
    - assert (isptr (Znth b s)) by (apply Hptr; lia).
      Exists (b-1) f (Znth b s) b.
      unfold cur. rewrite if_false by (intro Hn; rewrite Hn in *; contradiction).
      pose proof (inv3_node s (b-1) f b ltac:(auto) ltac:(lia) ltac:(lia)).
      replace (b-1+1) with b by lia.
      rewrite (nodes_split Ews s vs 0 b (b+1)) by lia.
      rewrite nodes_one.
      rewrite (toks_split s 0 b (b+1)) by lia.
      rewrite toks_one by lia.
      entailer!.
    - assert (isptr (Znth f s)) by (apply Hptr; lia).
      Exists b (f+1) (Znth f s) f.
      unfold cur. rewrite if_false by (intro Hn; rewrite Hn in *; contradiction).
      pose proof (inv3_node s b (f+1) f ltac:(auto) ltac:(lia) ltac:(lia)).
      rewrite (nodes_split Ews s vs f (f+1) (Zlength s)) by lia.
      rewrite nodes_one.
      rewrite (toks_split s f (f+1) (Zlength s)) by lia.
      rewrite toks_one by lia.
      entailer!. }
  forward.
  Exists sum. entailer!.
Qed.

(* ================================================================== *)
(* main                                                               *)
(* ================================================================== *)

Lemma body_main: semax_body Vprog Gprog f_main main_spec.
Proof.
  start_function.
  sep_apply (create_mem_mgr gv).
  forward_call (gv, Ews, gv _input, map Int.repr [6;7;3;4;7]).
  { rewrite !Zlength_cons, Zlength_nil. rep_lia. }
  change (Zlength (map Int.repr [6;7;3;4;7])) with 5.
  forward.
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
