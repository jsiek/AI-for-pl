Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import SglibVST.clientst SglibVST.spec_clientst.
Require SglibVST.lib_clientst.
Require Import VST.msl.iter_sepcon.

Local Open Scope logic.

(* myListCmp keeps no state *)
Definition Rc_client : globals -> val -> mpred := fun _ _ => emp.

(* ================================================================== *)
(* Helpers                                                            *)
(* ================================================================== *)

Definition tok (s: list val) (lo hi: Z) : mpred :=
  iter_sepcon (malloc_token Ews t_dl) (sublist lo hi s).

Lemma tok_split: forall s lo m hi, 0 <= lo <= m -> m <= hi <= Zlength s ->
  tok s lo hi = tok s lo m * tok s m hi.
Proof.
  intros. unfold tok. rewrite (sublist_split lo m hi) by lia.
  apply iter_sepcon_app.
Qed.

Lemma tok_one: forall s i, 0 <= i < Zlength s ->
  tok s i (i+1) = malloc_token Ews t_dl (Znth i s).
Proof.
  intros. unfold tok. rewrite sublist_len_1 by lia. simpl. apply sepcon_emp.
Qed.

Lemma tok_empty: forall s i, tok s i i = emp.
Proof. intros. unfold tok. rewrite sublist_nil. reflexivity. Qed.

Lemma tok_all: forall s, tok s 0 (Zlength s) = iter_sepcon (malloc_token Ews t_dl) s.
Proof. intros. unfold tok. rewrite sublist_same by lia. auto. Qed.

Lemma ins0: forall {A} {d: Inhabitant A} (x: A) l, ins 0 x l = x :: l.
Proof.
  intros. unfold ins. rewrite sublist_nil. rewrite sublist_same by lia. reflexivity.
Qed.

Lemma Znth_or_null_0: forall x s, Znth_or_null (x :: s) 0 = x.
Proof.
  intros. rewrite SglibVST.lib_clientst.Znth_or_null_in by list_solve.
  apply Znth_0_cons.
Qed.

Lemma Znth_or_null_nil: forall i, Znth_or_null [] i = nullval.
Proof.
  intros. apply SglibVST.lib_clientst.Znth_or_null_out. rewrite Zlength_nil. lia.
Qed.

Lemma at_node0: forall s, at_node s 0.
Proof. intros. destruct s. left; auto. right. list_solve. Qed.

Lemma all_ints: forall scp vs lo hi, Forall int_val (map pay vs) ->
  0 <= lo -> hi <= Zlength vs -> cmp_payloads scp vs lo hi.
Proof.
  intros. right. intros i Hi.
  assert (H2: int_val (Znth i (map pay vs))) by (apply Forall_Znth; auto; list_solve).
  rewrite Znth_map in H2 by lia. auto.
Qed.

Lemma func_ptr'_emp: forall fs v, func_ptr' fs v |-- emp.
Proof. intros. unfold func_ptr'. apply andp_left2. auto. Qed.

(* ================================================================== *)
(* Specs                                                              *)
(* ================================================================== *)

Definition myListCmp_spec :=
  DECLARE _myListCmp (cmp_spec Rc_client nullval).

Definition build_spec :=
 DECLARE _build
  WITH gv: globals, lp: val, shl: share, inp: val, shi: share,
       il: list int, n: Z
  PRE [ tptr (tptr t_dl), tptr tint, tint ]
    PROP (writable_share shl; readable_share shi;
          Zlength il = n; n <= Int.max_signed)
    PARAMS (lp; inp; Vint (Int.repr n)) GLOBALS (gv)
    SEP (mem_mgr gv; data_at shi (tarray tint n) (map Vint il) inp;
         data_at shl (tptr t_dl) nullval lp)
  POST [ tint ]
    EX s: list val, EX vs: list node_v,
    PROP (whole s vs; Forall int_val (map pay vs))
    RETURN (Vint (Int.repr (Zlength s)))
    SEP (mem_mgr gv; data_at shi (tarray tint n) (map Vint il) inp;
         data_at shl (tptr t_dl) (Znth_or_null s 0) lp;
         nodes Ews s vs 0 (Zlength s);
         iter_sepcon (malloc_token Ews t_dl) s).

Definition free_all_spec :=
 DECLARE _free_all
  WITH gv: globals, s: list val, vs: list node_v
  PRE [ tptr t_dl ]
    PROP (whole s vs)
    PARAMS (Znth_or_null s 0) GLOBALS (gv)
    SEP (mem_mgr gv; nodes Ews s vs 0 (Zlength s);
         iter_sepcon (malloc_token Ews t_dl) s)
  POST [ tvoid ]
    PROP () RETURN () SEP (mem_mgr gv).

Definition st_iter_equal_spec :=
 DECLARE _st_iter_equal
  WITH gv: globals, it: val, s: list val, vs: list node_v, shl: share,
       te: val, shte: share, vte: node_v
  PRE [ tptr t_it, tptr t_dl, tptr t_dl ]
    PROP (readable_share shl; readable_share shte; whole s vs;
          Forall int_val (map pay vs); int_val (pay vte))
    PARAMS (it; Znth_or_null s 0; te) GLOBALS (gv)
    SEP (data_at_ Tsh t_it it; nodes shl s vs 0 (Zlength s);
         data_at shte t_dl vte te)
  POST [ tint ]
    EX r: Z,
    PROP (r = 0 \/ r = 1)
    RETURN (Vint (Int.repr r))
    SEP (data_at_ Tsh t_it it; nodes shl s vs 0 (Zlength s);
         data_at shte t_dl vte te).

Definition input_vals : list int := map Int.repr [6;7;3;4;7].

Definition main_spec :=
 DECLARE _main
  WITH gv: globals
  PRE [ ] main_pre prog tt gv
  POST [ tint ]
    PROP () RETURN (Vint (Int.repr 0))
    SEP (mem_mgr gv;
         data_at Ews (tarray tint 5) (map Vint input_vals) (gv _input);
         has_ext tt).

Definition Gprog : funspecs :=
  SglibVST.spec_clientst.Gprog Rc_client ++
  [build_spec; free_all_spec; myListCmp_spec; st_iter_equal_spec; main_spec].

#[export] Existing Instance NullExtension.Espec.

(* ================================================================== *)
(* Library bodies under this Gprog                                    *)
(* ================================================================== *)

Lemma Gprog_norepet:
  list_norepet (map fst Vprog ++ map fst Gprog).
Proof. apply compute_list_norepet_e; reflexivity. Qed.

Ltac lib_body L :=
  eapply semax_body_subsumption; [apply L |];
  unfold Gprog;
  apply tycontext_sub_Gprog_app1;
  [ apply compute_list_norepet_e; reflexivity | apply Gprog_norepet ].

Lemma body_add': semax_body Vprog Gprog f_sglib_dllist_add add_spec.
Proof. lib_body (SglibVST.lib_clientst.body_add Rc_client). Qed.
Lemma body_get_first': semax_body Vprog Gprog f_sglib_dllist_get_first get_first_spec.
Proof. lib_body (SglibVST.lib_clientst.body_get_first Rc_client). Qed.
Lemma body_get_last': semax_body Vprog Gprog f_sglib_dllist_get_last get_last_spec.
Proof. lib_body (SglibVST.lib_clientst.body_get_last Rc_client). Qed.
Lemma body_it_init_on_equal': semax_body Vprog Gprog
  f_sglib_dllist_it_init_on_equal (it_init_on_equal_spec Rc_client).
Proof. lib_body (SglibVST.lib_clientst.body_it_init_on_equal Rc_client). Qed.
Lemma body_it_init': semax_body Vprog Gprog f_sglib_dllist_it_init it_init_spec.
Proof. lib_body (SglibVST.lib_clientst.body_it_init Rc_client). Qed.
Lemma body_it_next': semax_body Vprog Gprog f_sglib_dllist_it_next (it_next_spec Rc_client).
Proof. lib_body (SglibVST.lib_clientst.body_it_next Rc_client). Qed.

(* ================================================================== *)
(* Client bodies                                                      *)
(* ================================================================== *)

Lemma body_myListCmp: semax_body Vprog Gprog f_myListCmp myListCmp_spec.
Proof.
  start_function.
  destruct H as [ia Ha]. destruct H0 as [ib Hb].
  destruct va as [pa [na qa]]. destruct vb as [pb [nb qb]].
  unfold pay in Ha, Hb. simpl in Ha, Hb. subst pa pb.
  forward. forward. forward. forward.
  forward.
  - entailer!.
    destruct (Int.lt ib ia), (Int.lt ia ib); simpl; rep_lia.
  - Exists (Int.repr (Z.b2z (Int.lt ib ia) - Z.b2z (Int.lt ia ib))).
    entailer!.
Qed.

(* more helpers *)
Lemma whole_nil: whole [] [].
Proof.
  unfold whole, prev_links, next_links. rewrite !Zlength_nil.
  split; [auto | split; intros; lia].
Qed.

Lemma nodes_first: forall sh s vs i hi, i < hi ->
  nodes sh s vs i hi = data_at sh t_dl (Znth i vs) (Znth i s) * nodes sh s vs (i+1) hi.
Proof.
  intros. rewrite (SglibVST.lib_clientst.nodes_focus sh s vs i i hi) by lia.
  rewrite SglibVST.lib_clientst.nodes_empty by lia. rewrite emp_sepcon. auto.
Qed.

Lemma nodes_last: forall sh s vs lo i, lo <= i ->
  nodes sh s vs lo (i+1) = nodes sh s vs lo i * data_at sh t_dl (Znth i vs) (Znth i s).
Proof.
  intros. rewrite (SglibVST.lib_clientst.nodes_focus sh s vs lo i (i+1)) by lia.
  rewrite (SglibVST.lib_clientst.nodes_empty sh s vs (i+1) (i+1)) by lia.
  rewrite sepcon_emp. auto.
Qed.

Lemma tok_first: forall s i hi, 0 <= i < hi -> hi <= Zlength s ->
  tok s i hi = malloc_token Ews t_dl (Znth i s) * tok s (i+1) hi.
Proof.
  intros. rewrite (tok_split s i (i+1) hi) by lia. rewrite tok_one by lia. auto.
Qed.

Lemma tok_last: forall s lo i, 0 <= lo <= i -> i < Zlength s ->
  tok s lo (i+1) = tok s lo i * malloc_token Ews t_dl (Znth i s).
Proof.
  intros. rewrite (tok_split s lo i (i+1)) by lia. rewrite tok_one by lia. auto.
Qed.

Lemma mk_env: forall gv p eqp sh v, isptr p -> readable_share sh -> int_val (pay v) ->
  func_ptr' (cmp_spec Rc_client nullval) p * data_at sh t_dl v eqp |--
  cmp_env Rc_client p eqp sh v * cmp_state Rc_client gv p.
Proof.
  intros.
  change (cmp_spec Rc_client nullval) with (cmp_spec Rc_client p).
  unfold cmp_env, cmp_state.
  rewrite !if_false by (destruct p; try contradiction; discriminate).
  unfold Rc_client. rewrite sepcon_emp.
  apply andp_right; [apply prop_right; auto | auto].
Qed.

Lemma un_env: forall gv p eqp sh v, isptr p ->
  cmp_env Rc_client p eqp sh v * cmp_state Rc_client gv p |-- data_at sh t_dl v eqp.
Proof.
  intros. unfold cmp_env, cmp_state.
  rewrite !if_false by (destruct p; try contradiction; discriminate).
  unfold Rc_client. rewrite sepcon_emp.
  apply andp_left2. sep_apply func_ptr'_emp. rewrite emp_sepcon. auto.
Qed.

Lemma body_build: semax_body Vprog Gprog f_build build_spec.
Proof.
  start_function.
  forward.
  forward_loop
   (EX k: Z, EX s: list val, EX vs: list node_v,
    PROP (0 <= k <= n; Zlength s <= k; whole s vs; Forall int_val (map pay vs))
    LOCAL (temp _m (Vint (Int.repr (Zlength s))); temp _k (Vint (Int.repr k));
           temp _list lp; temp _input__1 inp; temp _n (Vint (Int.repr n)); gvars gv)
    SEP (mem_mgr gv; data_at shi (tarray tint n) (map Vint il) inp;
         data_at shl (tptr t_dl) (Znth_or_null s 0) lp;
         nodes Ews s vs 0 (Zlength s);
         iter_sepcon (malloc_token Ews t_dl) s))
  continue:
   (EX k: Z, EX s: list val, EX vs: list node_v,
    PROP (0 <= k < n; Zlength s <= k + 1; whole s vs; Forall int_val (map pay vs))
    LOCAL (temp _m (Vint (Int.repr (Zlength s))); temp _k (Vint (Int.repr k));
           temp _list lp; temp _input__1 inp; temp _n (Vint (Int.repr n)); gvars gv)
    SEP (mem_mgr gv; data_at shi (tarray tint n) (map Vint il) inp;
         data_at shl (tptr t_dl) (Znth_or_null s 0) lp;
         nodes Ews s vs 0 (Zlength s);
         iter_sepcon (malloc_token Ews t_dl) s))
  break:
   (EX s: list val, EX vs: list node_v,
    PROP (whole s vs; Forall int_val (map pay vs))
    LOCAL (temp _m (Vint (Int.repr (Zlength s))); gvars gv)
    SEP (mem_mgr gv; data_at shi (tarray tint n) (map Vint il) inp;
         data_at shl (tptr t_dl) (Znth_or_null s 0) lp;
         nodes Ews s vs 0 (Zlength s);
         iter_sepcon (malloc_token Ews t_dl) s)).
  - forward. Exists 0 (@nil val) (@nil node_v).
    rewrite Znth_or_null_nil. rewrite Zlength_nil.
    rewrite SglibVST.lib_clientst.nodes_empty by lia. simpl iter_sepcon.
    entailer!. apply whole_nil.
  - Intros k s vs.
    forward_if.
    + forward_call (t_dl, gv).
      Intros l.
      forward_if.
      * if_tac; entailer!.
      * forward. Exists s vs. rewrite if_true by auto. entailer!.
      * rewrite if_false by auto. Intros.
        forward.
        forward.
        forward_call (shl, lp, Ews, l, Vint (Znth k il), (Vundef, Vundef), s, vs, 0).
        { apply at_node0. }
        Intros vs'.
        forward.
        rewrite !ins0 in *.
        Exists k (l :: s) vs'.
        rewrite Znth_or_null_0. simpl iter_sepcon.
        rewrite Zlength_cons.
        entailer!.
        match goal with Hm: map pay vs' = _ |- _ => rewrite Hm end.
        constructor; auto. exists (Znth k il); reflexivity.
        rewrite <- Z.add_1_r. cancel.
    + forward. Exists s vs. entailer!.
  - Intros k s vs. forward. Exists (k+1) s vs. entailer!.
  - Intros s vs. forward. Exists s vs. entailer!.
Qed.

Ltac sidec :=
  repeat first [ apply at_node0 | split ]; auto; try lia;
  try (eapply SglibVST.lib_clientst.prev_links_sub; eauto; lia);
  try (eapply SglibVST.lib_clientst.next_links_sub; eauto; lia);
  try (left; reflexivity).

Ltac nullcontra :=
  match goal with
  | Hn: ?x = nullval, Hq: isptr ?x |- _ => rewrite Hn in Hq; contradiction
  end.

Definition fa_ok(s: list val) (b f lo hi: Z) (r: val) : Prop :=
  (r = nullval /\ b = -1 /\ f = Zlength s /\ lo = 0 /\ hi = Zlength s) \/
  (lo = b+2 /\ hi = f /\ b+1 < f /\ r = Znth (b+1) s) \/
  (lo = b+1 /\ hi = f-1 /\ b < f-1 /\ r = Znth (f-1) s).

Lemma body_free_all: semax_body Vprog Gprog f_free_all free_all_spec.
Proof.
  start_function.
  assert (Hw := H). destruct H as [Hlen [Hprev Hnext]].
  assert_PROP (forall i, 0 <= i < Zlength s -> isptr (Znth i s)) as Hp.
  { sep_apply SglibVST.lib_clientst.nodes_isptr. entailer!. }
  forward_call (Tsh, v_it, Ews, s, vs, 0).
  { sidec. }
  Intros vret. destruct vret as [[b f] r]. simpl fst in *. simpl snd in *.
  rewrite <- tok_all.
  forward_loop
    (EX b: Z, EX f: Z, EX lo: Z, EX hi: Z, EX r: val,
     PROP (-1 <= b < f; f <= Zlength s; fa_ok s b f lo hi r)
     LOCAL (temp _l r; lvar _it t_it v_it; gvars gv)
     SEP (mem_mgr gv; it_rep Tsh v_it s b f nullval nullval;
          nodes Ews s vs 0 lo; tok s 0 lo;
          nodes Ews s vs hi (Zlength s); tok s hi (Zlength s)))
  continue:
    (EX b: Z, EX f: Z,
     PROP (-1 <= b < f; f <= Zlength s)
     LOCAL (lvar _it t_it v_it; gvars gv)
     SEP (mem_mgr gv; it_rep Tsh v_it s b f nullval nullval;
          nodes Ews s vs 0 (b+1); tok s 0 (b+1);
          nodes Ews s vs f (Zlength s); tok s f (Zlength s)))
  break:
    (EX b: Z, EX f: Z,
     PROP ()
     LOCAL (lvar _it t_it v_it; gvars gv)
     SEP (mem_mgr gv; it_rep Tsh v_it s b f nullval nullval)).
  - destruct H as [Hb [Hf [_ [_ Hex]]]].
    destruct (Hex eq_refl) as [[Hr [Hs [Hb0 Hf0]]] | [c [Hc [Hr [Hb0 Hf0]]]]].
    + subst. rewrite Zlength_nil in *.
      Exists (-1) 0 0 0 nullval.
      entailer!. unfold fa_ok. left. rewrite Zlength_nil. auto.
    + subst.
      Exists (c-1) (c+1) (c+1) (c+1) (Znth c s).
      rewrite (SglibVST.lib_clientst.nodes_split Ews s vs 0 (c+1) (Zlength s)) by lia.
      rewrite (tok_split s 0 (c+1) (Zlength s)) by lia.
      entailer!. unfold fa_ok. right; left.
      split; [lia|]. split; [lia|]. split; [lia|]. f_equal; lia.
  - Intros b0 f0 lo hi r0.
    match goal with Hfa: fa_ok _ _ _ _ _ _ |- _ =>
    destruct Hfa as [[Hr [Hb0 [Hf0 [Hlo Hhi]]]] | [[Hlo [Hhi [Hbf Hr]]]
                   | [Hlo [Hhi [Hbf Hr]]]]] end; subst lo hi r0.
    + forward_if.
      { discriminate. }
      rewrite !SglibVST.lib_clientst.nodes_empty by lia. rewrite !tok_empty.
      forward. Exists b0 f0. entailer!.
    + assert (Hpc: isptr (Znth (b0+1) s)) by (apply Hp; lia).
      replace (b0+2) with (b0+1+1) by lia.
      rewrite (nodes_last Ews s vs 0 (b0+1)) by lia.
      rewrite (tok_last s 0 (b0+1)) by lia.
      forward_if.
      * forward_call (t_dl, Znth (b0+1) s, gv).
        { rewrite if_false by (intro X; rewrite X in Hpc; contradiction). cancel. }
        Exists b0 f0. entailer!.
      * exfalso. nullcontra.
    + assert (Hpc: isptr (Znth (f0-1) s)) by (apply Hp; lia).
      rewrite (nodes_first Ews s vs (f0-1) (Zlength s)) by lia.
      rewrite (tok_first s (f0-1) (Zlength s)) by lia.
      replace (f0-1+1) with f0 by lia.
      forward_if.
      * forward_call (t_dl, Znth (f0-1) s, gv).
        { rewrite if_false by (intro X; rewrite X in Hpc; contradiction). cancel. }
        Exists b0 f0. entailer!.
      * exfalso. nullcontra.
  - Intros b0 f0.
    forward_call (gv, Tsh, v_it, Ews, s, vs, b0, f0, nullval, nullval, Ews,
                  (Vundef, (Vundef, Vundef))).
    { unfold cmp_env, cmp_state. rewrite !if_true by auto. cancel. }
    { sidec. }
    Intros vret. destruct vret as [[b' f'] r']. simpl fst in *. simpl snd in *.
    unfold cmp_env, cmp_state. rewrite !if_true by auto.
    match goal with Hit: iter_step _ _ _ _ _ _ _ |- _ =>
      destruct Hit as [[Hb' [Hf' _]] Hex] end.
    forward.
    Exists b' f' (b0+1) f0 r'.
    entailer!.
    destruct (Hex eq_refl) as [[? [? [? [? ?]]]] | [[? [? [? ?]]] | [? [? [? ?]]]]].
    + subst. unfold fa_ok. left. repeat split; auto; lia.
    + subst. unfold fa_ok. right; left. repeat split; try lia. f_equal; lia.
    + subst. unfold fa_ok. right; right. repeat split; try lia. f_equal; lia.
  - Intros b0 f0. unfold it_rep. Intros cur.
    unfold POSTCONDITION, abbreviate. simpl_ret_assert.
    entailer!.
Qed.

Lemma body_st_iter_equal: semax_body Vprog Gprog f_st_iter_equal st_iter_equal_spec.
Proof.
  start_function.
  rename H into Hw, H0 into Hints, H1 into Hte.
  assert (Hw' := Hw). destruct Hw' as [Hlen [Hprev Hnext]].
  assert_PROP (forall i, 0 <= i < Zlength s -> isptr (Znth i s)) as Hp.
  { sep_apply SglibVST.lib_clientst.nodes_isptr. entailer!. }
  forward. forward.
  make_func_ptr _myListCmp.
  assert_PROP (isptr (gv _myListCmp)) as Hfp.
  { entailer!. }
  sep_apply (mk_env gv (gv _myListCmp) te shte vte); auto.
  forward_call (gv, Tsh, it, shl, s, vs, 0, gv _myListCmp, te, shte, vte).
  { cancel. }
  { sidec. apply all_ints; auto; list_solve. }
  Intros vret. destruct vret as [[b f] r]. simpl fst in *. simpl snd in *.
  match goal with Hi: init_window _ _ _ _ _ |- _ =>
    destruct Hi as [Hb [Hf [Hr [Hrn _]]]] end.
  assert (Hr2: r = nullval \/ (exists c, 0 <= c < Zlength s /\ r = Znth c s)).
  { destruct Hr as [?|[c [? ?]]]; [left; auto | right; exists c; split; [lia|auto]]. }
  forward_loop
   (EX b: Z, EX f: Z, EX r: val, EX fd: Z,
    PROP (-1 <= b < f; f <= Zlength s;
          r = nullval \/ (exists c, 0 <= c < Zlength s /\ r = Znth c s);
          fd = 0 \/ fd = 1)
    LOCAL (temp _ll r; temp _found (Vint (Int.repr fd)); temp _it it; gvars gv)
    SEP (it_rep Tsh it s b f (gv _myListCmp) te; nodes shl s vs 0 (Zlength s);
         cmp_env Rc_client (gv _myListCmp) te shte vte;
         cmp_state Rc_client gv (gv _myListCmp)))
  continue:
   (EX b: Z, EX f: Z,
    PROP (-1 <= b < f; f <= Zlength s)
    LOCAL (temp _found (Vint (Int.repr 1)); temp _it it; gvars gv)
    SEP (it_rep Tsh it s b f (gv _myListCmp) te; nodes shl s vs 0 (Zlength s);
         cmp_env Rc_client (gv _myListCmp) te shte vte;
         cmp_state Rc_client gv (gv _myListCmp)))
  break:
   (EX b: Z, EX f: Z, EX fd: Z,
    PROP (fd = 0 \/ fd = 1)
    LOCAL (temp _found (Vint (Int.repr fd)); temp _it it; gvars gv)
    SEP (it_rep Tsh it s b f (gv _myListCmp) te; nodes shl s vs 0 (Zlength s);
         cmp_env Rc_client (gv _myListCmp) te shte vte;
         cmp_state Rc_client gv (gv _myListCmp))).
  - Exists b f r 0. entailer!.
  - Intros b0 f0 r0 fd.
    match goal with Hx: r0 = nullval \/ _ |- _ => destruct Hx as [Hn | [c [Hc Hrc]]] end.
    + subst r0. forward_if.
      { discriminate. }
      forward. Exists b0 f0 fd. entailer!.
    + subst r0.
      assert (Hpc: isptr (Znth c s)) by (apply Hp; lia).
      rewrite (SglibVST.lib_clientst.nodes_focus shl s vs 0 c (Zlength s)) by lia.
      Intros.
      forward_if.
      * forward. Exists b0 f0.
        rewrite (SglibVST.lib_clientst.nodes_focus shl s vs 0 c (Zlength s)) by lia.
        entailer!.
      * exfalso. nullcontra.
  - Intros b0 f0.
    rewrite (SglibVST.lib_clientst.nodes_split shl s vs 0 (b0+1) (Zlength s)) by lia.
    rewrite (SglibVST.lib_clientst.nodes_split shl s vs (b0+1) f0 (Zlength s)) by lia.
    Intros.
    forward_call (gv, Tsh, it, shl, s, vs, b0, f0, gv _myListCmp, te, shte, vte).
    { sidec. all: apply all_ints; auto; lia. }
    Intros vret. destruct vret as [[b' f'] r']. simpl fst in *. simpl snd in *.
    match goal with Hit: iter_step _ _ _ _ _ _ _ |- _ =>
      destruct Hit as [[Hb' [Hf' [Hr' _]]] _] end.
    forward.
    Exists b' f' r' 1.
    rewrite (SglibVST.lib_clientst.nodes_split shl s vs 0 (b0+1) (Zlength s)) by lia.
    rewrite (SglibVST.lib_clientst.nodes_split shl s vs (b0+1) f0 (Zlength s)) by lia.
    entailer!.
    destruct Hr' as [?|[c [? [? ?]]]]; [left; auto | right; exists c; split; [lia|auto]].
  - Intros b0 f0 fd.
    sep_apply (un_env gv (gv _myListCmp) te shte vte); auto.
    unfold it_rep. Intros cur.
    forward.
    Exists fd. entailer!.
Qed.

Lemma body_main: semax_body Vprog Gprog f_main main_spec.
Proof.
  start_function.
  sep_apply (create_mem_mgr gv).
  forward.
  forward_call (gv, v_list, Tsh, gv _input, Ews, input_vals, 5).
  Intros vret. destruct vret as [s vs]. simpl fst in *. simpl snd in *.
  assert (Hiv: Zlength input_vals = 5) by reflexivity.
  assert_PROP (is_pointer_or_null (Znth_or_null s 0)) as Hpn.
  { sep_apply SglibVST.lib_clientst.nodes_isptr. entailer!.
    apply (SglibVST.lib_clientst.Znth_or_null_pn s 0 0 (Zlength s)); auto.
    destruct (zlt 0 (Zlength s)); [right; right | right; left]; lia. }
  forward. forward. forward. forward. forward.
  change (Vlong (Int64.repr (Int.signed (Int.repr 0)))) with nullval.
  change (Znth 0 input_vals) with (Int.repr 6).
  forward_call (gv, v_it, s, vs, Ews, v_te, Tsh,
                (Vint (Int.repr 6), (nullval, nullval))).
  { repeat split; auto. exists (Int.repr 6); reflexivity. }
  Intros r.
  forward.
  forward_call (gv, s, vs).
  forward.
  sep_apply (data_at_data_at_ Tsh t_dl (Vint (Int.repr 6), (nullval, nullval)) v_te).
  sep_apply (data_at_data_at_ Tsh (tptr t_dl) (Znth_or_null s 0) v_list).
  cancel.
Qed.

Lemma prog_correct: semax_prog prog tt Vprog Gprog.
Proof.
  prove_semax_prog.
  semax_func_cons body_malloc. apply semax_func_cons_malloc_aux.
  semax_func_cons body_free.
  semax_func_cons body_add'.
  semax_func_cons body_get_first'.
  semax_func_cons body_get_last'.
  semax_func_cons body_it_init_on_equal'.
  semax_func_cons body_it_init'.
  semax_func_cons body_it_next'.
  semax_func_cons body_build.
  semax_func_cons body_free_all.
  semax_func_cons body_myListCmp.
  semax_func_cons body_st_iter_equal.
  semax_func_cons body_main.
Qed.

(* the check's Gprog lemma, for each library function *)
Goal forall i, In i [_sglib_dllist_add; _sglib_dllist_get_first;
                     _sglib_dllist_get_last; _sglib_dllist_it_init_on_equal;
                     _sglib_dllist_it_init; _sglib_dllist_it_next] ->
  initial_world.find_id i Gprog =
  initial_world.find_id i (SglibVST.spec_clientst.Gprog Rc_client).
Proof.
  intros i Hi. simpl in Hi.
  repeat (destruct Hi as [<- | Hi]; [reflexivity |]). contradiction.
Qed.

Print Assumptions prog_correct.


