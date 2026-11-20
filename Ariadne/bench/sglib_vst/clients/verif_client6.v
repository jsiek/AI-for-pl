Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import SglibVST.client6 SglibVST.spec_client6.
Require SglibVST.lib_client6.

Module L := SglibVST.lib_client6.

Local Open Scope logic.

#[export] Existing Instance NullExtension.Espec.

(* This program uses no comparator. *)
Definition Rc_client : globals -> val -> mpred := fun _ _ => emp.

(* ================================================================== *)
(* Helpers                                                            *)
(* ================================================================== *)

(* malloc tokens of nodes lo .. hi-1 *)
Fixpoint tokl (l: list val) : mpred :=
  match l with
  | nil => emp
  | p :: l' => malloc_token Ews t_dl p * tokl l'
  end.

Lemma tokl_app: forall l1 l2, tokl (l1 ++ l2) = tokl l1 * tokl l2.
Proof.
  induction l1; intros; simpl.
  - rewrite emp_sepcon. auto.
  - rewrite IHl1, sepcon_assoc. auto.
Qed.

Definition toks (s: list val) (lo hi: Z) : mpred := tokl (sublist lo hi s).

Lemma toks_split: forall s lo m hi, 0 <= lo <= m -> m <= hi <= Zlength s ->
  toks s lo hi = toks s lo m * toks s m hi.
Proof.
  intros. unfold toks. rewrite (sublist_split lo m hi) by lia.
  apply tokl_app.
Qed.

Lemma toks_one: forall s i, 0 <= i < Zlength s ->
  toks s i (i+1) = malloc_token Ews t_dl (Znth i s).
Proof.
  intros. unfold toks. rewrite sublist_one by lia. simpl. apply sepcon_emp.
Qed.

Lemma toks_empty: forall s lo, toks s lo lo = emp.
Proof. intros. unfold toks. rewrite sublist_nil. reflexivity. Qed.

Lemma toks_cons: forall e s,
  toks (e :: s) 0 (Zlength s + 1) = malloc_token Ews t_dl e * toks s 0 (Zlength s).
Proof.
  intros. unfold toks. rewrite !sublist_same by (try rewrite Zlength_cons; lia).
  reflexivity.
Qed.

Lemma ins0: forall {A} {d: Inhabitant A} (x: A) l, ins 0 x l = x :: l.
Proof. intros. unfold ins. rewrite sublist_nil, sublist_same by lia. reflexivity. Qed.

Lemma Znth_or_null_cons0: forall e s, Znth_or_null (e :: s) 0 = e.
Proof.
  intros. rewrite L.Znth_or_null_in by (rewrite Zlength_cons; list_solve).
  apply Znth_0_cons.
Qed.

Lemma int_payloads_cons: forall vs vs' ev,
  map pay vs' = ev :: map pay vs -> int_val ev ->
  int_payloads vs 0 (Zlength vs) -> int_payloads vs' 0 (Zlength vs').
Proof.
  intros vs vs' ev H Hev Hp i Hi.
  assert (Zlength vs' = Zlength vs + 1).
  { rewrite <- (Zlength_map _ _ pay vs'), H, Zlength_cons, Zlength_map. lia. }
  replace (pay (Znth i vs')) with (Znth i (map pay vs')) by (rewrite Znth_map; auto; lia).
  rewrite H. destruct (zeq i 0).
  - subst. rewrite Znth_0_cons. auto.
  - rewrite Znth_pos_cons by lia. rewrite Znth_map by lia. apply Hp. lia.
Qed.

Lemma cmp_env_null: forall eqp sh v, cmp_env Rc_client nullval eqp sh v = emp.
Proof. intros. unfold cmp_env. destruct (Val.eq nullval nullval); congruence. Qed.

Lemma cmp_state_null: forall gv, cmp_state Rc_client gv nullval = emp.
Proof. intros. unfold cmp_state. destruct (Val.eq nullval nullval); congruence. Qed.

Lemma whole_at_node0: forall s vs, whole s vs ->
  at_node s 0 /\ Zlength vs = Zlength s /\
  prev_links s vs 0 (Z.min (0+1) (Zlength s)) /\ next_links s vs 0 (Zlength s).
Proof.
  intros s vs [Hl [Hp Hn]]. split; [|split; [auto|split; auto]].
  - destruct s; [left; auto|right; rewrite Zlength_cons; list_solve].
  - eapply L.prev_links_sub; eauto; lia.
Qed.

(* ================================================================== *)
(* Specs of the client's own functions                                *)
(* ================================================================== *)

Definition build_spec :=
 DECLARE _build
  WITH gv: globals, shl: share, lp: val, sh: share, inp: val,
       contents: list int
  PRE [ tptr (tptr t_dl), tptr tint, tint ]
    PROP (writable_share shl; readable_share sh;
          Zlength contents <= Int.max_signed)
    PARAMS (lp; inp; Vint (Int.repr (Zlength contents))) GLOBALS (gv)
    SEP (mem_mgr gv; data_at shl (tptr t_dl) nullval lp;
         data_at sh (tarray tint (Zlength contents)) (map Vint contents) inp)
  POST [ tint ]
    EX s: list val, EX vs: list node_v,
    PROP (whole s vs; int_payloads vs 0 (Zlength s);
          Zlength s <= Zlength contents)
    RETURN (Vint (Int.repr (Zlength s)))
    SEP (mem_mgr gv; data_at shl (tptr t_dl) (Znth_or_null s 0) lp;
         nodes Ews s vs 0 (Zlength s); toks s 0 (Zlength s);
         data_at sh (tarray tint (Zlength contents)) (map Vint contents) inp).

Definition client_spec :=
 DECLARE _client
  WITH gv: globals, sh: share, inp: val, contents: list int, k: Z
  PRE [ tptr tint, tint, tint ]
    PROP (readable_share sh; Zlength contents <= Int.max_signed;
          0 <= k <= Int.max_signed)
    PARAMS (inp; Vint (Int.repr (Zlength contents)); Vint (Int.repr k))
    GLOBALS (gv)
    SEP (mem_mgr gv;
         data_at sh (tarray tint (Zlength contents)) (map Vint contents) inp)
  POST [ tuint ]
    EX r: int,
    PROP ()
    RETURN (Vint r)
    SEP (mem_mgr gv;
         data_at sh (tarray tint (Zlength contents)) (map Vint contents) inp).

Definition input_contents : list int :=
  map Int.repr [6; 7; 3; 4; 7].

Definition main_spec :=
 DECLARE _main
  WITH gv: globals
  PRE [ ] main_pre prog tt gv
  POST [ tint ]
    PROP ()
    RETURN (Vint (Int.repr 0))
    SEP (has_ext tt; mem_mgr gv;
         data_at Ews (tarray tint 5) (map Vint input_contents) (gv _input)).

Definition Gprog : funspecs :=
  ltac:(with_library prog [add_spec; get_first_spec; get_last_spec;
                           it_init_on_equal_spec Rc_client; it_init_spec;
                           it_next_spec Rc_client;
                           build_spec; client_spec; main_spec]).

(* ================================================================== *)
(* Library functions, from lib_client6                                 *)
(* ================================================================== *)

Lemma subVG: tycontext_subVG Vprog (SglibVST.spec_client6.Gprog Rc_client) Vprog Gprog.
Proof.
  split.
  - apply sub_option_get.
    let A1 := fresh "A1" in let A2 := fresh "A2" in
    set (A1 := make_tycontext_g Vprog (SglibVST.spec_client6.Gprog Rc_client));
    set (A2 := make_tycontext_g Vprog Gprog);
    compute in A1; compute in A2; subst A1 A2;
    repeat (apply Forall_cons; [reflexivity | ]);  apply Forall_nil.
  - apply subsume_spec_get.
    let A1 := fresh "A1" in let A2 := fresh "A2" in
    set (A1 := make_tycontext_s (SglibVST.spec_client6.Gprog Rc_client));
    set (A2 := make_tycontext_s Gprog);
    let a := make_ground_PTree A1 in change A1 with a; clear A1;
    let a := make_ground_PTree A2 in change A2 with a; clear A2;
    repeat (apply Forall_cons; [apply subsumespec_refl | ]);
    apply Forall_nil.
Qed.

Ltac from_lib L :=
  eapply semax_body_subsumption; [apply L | apply tycontext_sub_i99; exact subVG].

Lemma body_add: semax_body Vprog Gprog f_sglib_dllist_add add_spec.
Proof. from_lib (L.body_add Rc_client). Qed.
Lemma body_get_first: semax_body Vprog Gprog f_sglib_dllist_get_first get_first_spec.
Proof. from_lib (L.body_get_first Rc_client). Qed.
Lemma body_get_last: semax_body Vprog Gprog f_sglib_dllist_get_last get_last_spec.
Proof. from_lib (L.body_get_last Rc_client). Qed.
Lemma body_it_init_on_equal: semax_body Vprog Gprog f_sglib_dllist_it_init_on_equal
  (it_init_on_equal_spec Rc_client).
Proof. from_lib (L.body_it_init_on_equal Rc_client). Qed.
Lemma body_it_init: semax_body Vprog Gprog f_sglib_dllist_it_init it_init_spec.
Proof. from_lib (L.body_it_init Rc_client). Qed.
Lemma body_it_next: semax_body Vprog Gprog f_sglib_dllist_it_next (it_next_spec Rc_client).
Proof. from_lib (L.body_it_next Rc_client). Qed.

(* ================================================================== *)
(* build                                                              *)
(* ================================================================== *)

Lemma body_build: semax_body Vprog Gprog f_build build_spec.
Proof.
  start_function.
  forward.
  forward_loop
    (EX k: Z, EX s: list val, EX vs: list node_v,
     PROP (0 <= k <= Zlength contents; Zlength s = k; whole s vs;
           int_payloads vs 0 k)
     LOCAL (temp _m (Vint (Int.repr k)); temp _k (Vint (Int.repr k));
            temp _list lp; temp _input__1 inp;
            temp _n (Vint (Int.repr (Zlength contents))); gvars gv)
     SEP (mem_mgr gv; data_at shl (tptr t_dl) (Znth_or_null s 0) lp;
          nodes Ews s vs 0 k; toks s 0 k;
          data_at sh (tarray tint (Zlength contents)) (map Vint contents) inp))
  continue:
    (EX k: Z, EX s: list val, EX vs: list node_v,
     PROP (0 <= k < Zlength contents; Zlength s = (k+1)%Z; whole s vs;
           int_payloads vs 0 (k+1)%Z)
     LOCAL (temp _m (Vint (Int.repr (k+1)%Z)); temp _k (Vint (Int.repr k));
            temp _list lp; temp _input__1 inp;
            temp _n (Vint (Int.repr (Zlength contents))); gvars gv)
     SEP (mem_mgr gv; data_at shl (tptr t_dl) (Znth_or_null s 0) lp;
          nodes Ews s vs 0 (k+1)%Z; toks s 0 (k+1)%Z;
          data_at sh (tarray tint (Zlength contents)) (map Vint contents) inp))
  break:
    (EX s: list val, EX vs: list node_v,
     PROP (whole s vs; int_payloads vs 0 (Zlength s);
           Zlength s <= Zlength contents)
     LOCAL (temp _m (Vint (Int.repr (Zlength s))))
     SEP (mem_mgr gv; data_at shl (tptr t_dl) (Znth_or_null s 0) lp;
          nodes Ews s vs 0 (Zlength s); toks s 0 (Zlength s);
          data_at sh (tarray tint (Zlength contents)) (map Vint contents) inp)).
  - (* entry *)
    forward.
    Exists 0 (@nil val) (@nil node_v).
    rewrite L.nodes_empty by lia. rewrite toks_empty.
    rewrite L.Znth_or_null_out by (rewrite Zlength_nil; lia).
    entailer!.
    split; [|intros i Hi; lia].
    split; [auto|split; intros i Hi; rewrite Zlength_nil in Hi; lia].
  - (* body *)
    Intros k s vs.
    forward_if.
    + forward_call (Tstruct _dllist noattr, gv).
      Intros p.
      if_tac.
      * subst p. forward_if.
        { forward. Exists s vs. entailer!. }
        { exfalso; auto. }
      * Intros. forward_if.
        { contradiction. }
        forward.
        forward.
        subst k.
        forward_call (shl, lp, Ews, p, Vint (Znth (Zlength s) contents), (Vundef, Vundef), s, vs, 0).
        { destruct s; [left; auto|right; rewrite Zlength_cons; list_solve]. }
        Intros vs'.
        rewrite ins0 in *.
        forward.
        Exists (Zlength s) (p :: s) vs'.
        rewrite Znth_or_null_cons0.
        rewrite toks_cons.
        entailer!.
        destruct H2 as [Hl _].
        assert (Hl2: Zlength vs' = Zlength s + 1).
        { destruct H1 as [Hl' _]. rewrite Hl', Zlength_cons. lia. }
        split; [rewrite Zlength_cons; lia |].
        rewrite <- Hl2.
        eapply int_payloads_cons; [eassumption | eexists; eauto |].
        rewrite Hl. auto.
    + forward. Exists s vs. entailer!.
  - (* increment *)
    Intros k s vs.
    forward.
    Exists (k+1) s vs. entailer!.
  - (* after the loop *)
    Intros s vs.
    forward.
    Exists s vs. entailer!.
Qed.

(* ================================================================== *)
(* client                                                             *)
(* ================================================================== *)

Lemma nodes_3: forall sh s vs b f n, 0 <= b+1 <= f -> f <= n ->
  nodes sh s vs 0 n =
  nodes sh s vs 0 (b+1) * nodes sh s vs (b+1) f * nodes sh s vs f n.
Proof.
  intros. rewrite (L.nodes_split sh s vs 0 (b+1) n) by lia.
  rewrite (L.nodes_split sh s vs (b+1) f n) by lia.
  rewrite sepcon_assoc; auto.
Qed.

Lemma nodes_pn: forall sh s vs i,
  nodes sh s vs 0 (Zlength s) |-- !! is_pointer_or_null (Znth_or_null s i).
Proof.
  intros. eapply derives_trans; [apply L.nodes_isptr|]. apply prop_derives.
  intros. eapply L.Znth_or_null_pn; eauto. lia.
Qed.

Lemma toks_empty': forall s lo hi, hi <= lo -> toks s lo hi = emp.
Proof. intros. unfold toks. rewrite sublist_nil_gen by lia. reflexivity. Qed.

Lemma nodes_mid1: forall sh s vs c,
  nodes sh s vs (c-1+1) (c+1) = data_at sh t_dl (Znth c vs) (Znth c s).
Proof. intros. replace (c-1+1) with c by lia. apply L.nodes_one. Qed.

Lemma toks_mid1: forall s c, 0 <= c < Zlength s ->
  toks s (c-1+1) (c+1) = malloc_token Ews t_dl (Znth c s).
Proof. intros. replace (c-1+1) with c by lia. apply toks_one; auto. Qed.

(* the node the free loop holds: none, or node c (and its token) *)
Definition cur_node (vs: list node_v) (l: val) (c: Z) : mpred :=
  if eq_dec l nullval then emp
  else data_at Ews t_dl (Znth c vs) l * malloc_token Ews t_dl l.

Lemma body_client: semax_body Vprog Gprog f_client client_spec.
Proof.
  start_function.
  forward.
  forward.
  forward.
  forward_call (gv, Tsh, v_list, sh, inp, contents).
  Intros vret. destruct vret as [s vs]. simpl fst in *. simpl snd in *.
  pose proof H1 as Hw. destruct Hw as [Hlen [Hp Hn]].
  assert_PROP (is_pointer_or_null (Znth_or_null s 0)).
  { go_lower. sep_apply (nodes_pn Ews s vs 0). entailer!. }
  forward.
  forward_call (Tsh, v_it, Ews, s, vs, 0).
  { destruct (whole_at_node0 s vs H1) as [? [? [? ?]]]. repeat split; auto. }
  Intros vret. destruct vret as [[b f] r]. simpl fst in *. simpl snd in *.
  assert_PROP (forall i, 0 <= i < Zlength s -> isptr (Znth i s)) as Hptr.
  { go_lower. sep_apply (L.nodes_isptr Ews s vs 0 (Zlength s)). entailer!. }
  forward.
  forward_loop
    (EX b: Z, EX f: Z, EX l: val, EX c: Z, EX sum: int,
     PROP (-1 <= b < f; f <= Zlength s;
           l = nullval -> b = -1 /\ f = Zlength s;
           l = nullval \/ (exists c', b < c' < f /\ l = Znth c' s);
           0 <= c <= k)
     LOCAL (temp _l l; temp _c (Vint (Int.repr c)); temp _sum (Vint sum);
            temp _k (Vint (Int.repr k));
            lvar _it (Tstruct _sglib_dllist_iterator noattr) v_it;
            lvar _list (tptr (Tstruct _dllist noattr)) v_list; gvars gv)
     SEP (mem_mgr gv; data_at Tsh (tptr t_dl) (Znth_or_null s 0) v_list;
          it_rep Tsh v_it s b f nullval nullval;
          nodes Ews s vs 0 (Zlength s); toks s 0 (Zlength s);
          data_at sh (tarray tint (Zlength contents)) (map Vint contents) inp))
  break:
    (EX sum: int,
     PROP ()
     LOCAL (temp _sum (Vint sum);
            lvar _it (Tstruct _sglib_dllist_iterator noattr) v_it;
            lvar _list (tptr (Tstruct _dllist noattr)) v_list; gvars gv)
     SEP (mem_mgr gv; data_at Tsh (tptr t_dl) (Znth_or_null s 0) v_list;
          data_at_ Tsh (Tstruct _sglib_dllist_iterator noattr) v_it;
          nodes Ews s vs 0 (Zlength s); toks s 0 (Zlength s);
          data_at sh (tarray tint (Zlength contents)) (map Vint contents) inp)).
  - (* entry *)
    destruct H5 as [? [? [? [? _]]]].
    Exists b f r 0 (Int.repr 0). entailer!.
  - (* body *)
    Intros b' f' l c sum.
    match goal with H: l = nullval \/ _ |- _ =>
      destruct H as [Hl0 | [c' [Hc' Hl0]]] end.
    + subst l.
      forward_if (temp _t'2 (Vint (Int.repr 0))).
      { discriminate. }
      { forward. entailer!. }
      forward_if.
      { contradiction. }
      forward. Exists sum. unfold it_rep. Intros cur. entailer!.
    + subst l.
      assert (Hc2 : 0 <= c' < Zlength s) by lia.
      pose proof (Hptr c' Hc2) as Hpc.
      rewrite (L.nodes_focus Ews s vs 0 c' (Zlength s)) by lia.
      Intros.
      forward_if (temp _t'2 (Vint (Int.repr (if zlt c k then 1 else 0)))).
      { forward. entailer!. destruct (zlt c k); reflexivity. }
      { match goal with H: Znth c' s = nullval |- _ => rewrite H in Hpc; contradiction end. }
      destruct (zlt c k) as [Hck|Hck].
      * forward_if.
        2:{ exfalso. apply Int.one_not_zero. assumption. }
        destruct (H2 c' ltac:(lia)) as [iv Hiv]. unfold pay in Hiv.
        destruct (Znth c' vs) as [pv [nv qv]] eqn:Ez. simpl in Hiv. subst pv.
        forward. forward. forward.
        assert (Hfold: nodes Ews s vs 0 c' * data_at Ews t_dl (Vint iv, (nv, qv)) (Znth c' s)
                       * nodes Ews s vs (c'+1) (Zlength s) |-- nodes Ews s vs 0 (Zlength s)).
        { rewrite <- Ez. rewrite (L.nodes_focus Ews s vs 0 c' (Zlength s)) by lia. auto. }
        sep_apply Hfold.
        rewrite (nodes_3 Ews s vs b' f' (Zlength s)) by lia.
        Intros.
        forward_call (gv, Tsh, v_it, Ews, s, vs, b', f', nullval, nullval, Ews,
                      (Vundef, (Vundef, Vundef)) : node_v).
        { rewrite cmp_env_null, cmp_state_null. cancel. }
        { split3; [eapply L.prev_links_sub; eauto; lia
                  | eapply L.next_links_sub; eauto; lia
                  | split; left; auto]. }
        Intros vret. destruct vret as [[b2 f2] r2]. simpl fst in *. simpl snd in *.
        rewrite cmp_env_null, cmp_state_null.
        forward.
        Exists b2 f2 r2 (c+1)%Z (Int.add sum iv).
        rewrite (nodes_3 Ews s vs b' f' (Zlength s)) by lia.
        match goal with H: iter_step _ _ _ _ _ _ _ |- _ =>
          destruct H as [[Hb2 [Hf2 [Hr Hrn]]] _] end.
        entailer!.
        destruct Hr as [Hr|[cc [? [? ?]]]]; [left; auto | right; exists cc; split; [lia|auto]].
      * forward_if.
        { contradiction. }
        forward. Exists sum. unfold it_rep. Intros cur.
        rewrite (L.nodes_focus Ews s vs 0 c' (Zlength s)) by lia.
        entailer!.
  - (* after *)
    Intros sum.
    match goal with H: init_window _ _ b f r |- _ => clear H end. clear b f r.
    forward.
    forward_call (Tsh, v_it, Ews, s, vs, 0).
    { destruct (whole_at_node0 s vs H1) as [? [? [? ?]]]. repeat split; auto. }
    Intros vret. destruct vret as [[b2 f2] r2]. simpl fst in *. simpl snd in *.
    forward.
    forward_loop
      (EX b: Z, EX f: Z, EX l: val, EX c: Z,
       PROP (-1 <= b < f; f <= Zlength s;
             (l = nullval /\ b = -1 /\ f = Zlength s) \/
             ((c = (b+1)%Z \/ c = (f-1)%Z) /\ b < c < f /\ l = Znth c s /\ isptr l))
       LOCAL (temp _l l; temp _sum (Vint sum);
              lvar _it (Tstruct _sglib_dllist_iterator noattr) v_it;
              lvar _list (tptr (Tstruct _dllist noattr)) v_list; gvars gv)
       SEP (mem_mgr gv; data_at Tsh (tptr t_dl) (Znth_or_null s 0) v_list;
            it_rep Tsh v_it s b f nullval nullval;
            nodes Ews s vs 0 (b+1)%Z; nodes Ews s vs f (Zlength s);
            toks s 0 (b+1)%Z; toks s f (Zlength s);
            cur_node vs l c;
            data_at sh (tarray tint (Zlength contents)) (map Vint contents) inp))
    continue:
      (EX b: Z, EX f: Z,
       PROP (-1 <= b < f; f <= Zlength s)
       LOCAL (temp _sum (Vint sum);
              lvar _it (Tstruct _sglib_dllist_iterator noattr) v_it;
              lvar _list (tptr (Tstruct _dllist noattr)) v_list; gvars gv)
       SEP (mem_mgr gv; data_at Tsh (tptr t_dl) (Znth_or_null s 0) v_list;
            it_rep Tsh v_it s b f nullval nullval;
            nodes Ews s vs 0 (b+1)%Z; nodes Ews s vs f (Zlength s);
            toks s 0 (b+1)%Z; toks s f (Zlength s);
            data_at sh (tarray tint (Zlength contents)) (map Vint contents) inp))
    break:
      (PROP ()
       LOCAL (temp _sum (Vint sum);
              lvar _it (Tstruct _sglib_dllist_iterator noattr) v_it;
              lvar _list (tptr (Tstruct _dllist noattr)) v_list; gvars gv)
       SEP (mem_mgr gv; data_at Tsh (tptr t_dl) (Znth_or_null s 0) v_list;
            data_at_ Tsh (Tstruct _sglib_dllist_iterator noattr) v_it;
            data_at sh (tarray tint (Zlength contents)) (map Vint contents) inp)).
    + (* entry *)
      match goal with H: init_window _ _ b2 f2 r2 |- _ =>
        destruct H as [Hbf2 [Hf2 [_ [_ Hex]]]] end.
      specialize (Hex eq_refl).
      rewrite (nodes_3 Ews s vs b2 f2 (Zlength s)) by lia.
      rewrite (toks_split s 0 (b2+1) (Zlength s)) by lia.
      rewrite (toks_split s (b2+1) f2 (Zlength s)) by lia.
      destruct Hex as [[Hr [Hs [Hb Hf]]] | [c [Hc [Hr [Hb Hf]]]]].
      * subst r2.
        rewrite (L.nodes_empty Ews s vs (b2+1) f2) by lia.
        rewrite (toks_empty' s (b2+1) f2) by lia.
        Exists b2 f2 nullval 0. unfold cur_node; rewrite if_true by auto.
        entailer!.
      * subst r2 b2 f2.
        rewrite nodes_mid1, toks_mid1 by lia.
        Exists (c-1)%Z (c+1)%Z (Znth c s) c.
        unfold cur_node; rewrite if_false by (pose proof (Hptr c Hc); intro Hx; rewrite Hx in *; contradiction).
        entailer!.
        right. split; [left; lia|]. split; [lia|]. split; auto.
    + (* body *)
      Intros b f l c.
      match goal with H: (l = nullval /\ _) \/ _ |- _ =>
        destruct H as [[Hl [Hb Hf]] | [Hc [Hbc [Hl Hpl]]]] end.
      * subst l b f. unfold cur_node; rewrite if_true by auto.
        rewrite (L.nodes_empty Ews s vs 0 (-1+1)) by lia.
        rewrite (L.nodes_empty Ews s vs (Zlength s) (Zlength s)) by lia.
        rewrite (toks_empty' s 0 (-1+1)) by lia.
        rewrite (toks_empty' s (Zlength s) (Zlength s)) by lia.
        forward_if.
        { exfalso; congruence. }
        forward. unfold it_rep. Intros cur. entailer!.
      * subst l.
        unfold cur_node; rewrite if_false by (intro Hx; rewrite Hx in Hpl; contradiction).
        Intros.
        forward_if.
        2:{ match goal with H: Znth c s = nullval |- _ => rewrite H in Hpl; contradiction end. }
        forward_call (t_dl, Znth c s, gv).
        { rewrite if_false by (intro Hx; rewrite Hx in Hpl; contradiction). cancel. }
        Exists b f. entailer!.
    + (* incr *)
      Intros b f.
      forward_call (gv, Tsh, v_it, Ews, s, vs, b, f, nullval, nullval, Ews,
                    (Vundef, (Vundef, Vundef)) : node_v).
      { rewrite cmp_env_null, cmp_state_null. cancel. }
      { split3; [eapply L.prev_links_sub; eauto; lia
                | eapply L.next_links_sub; eauto; lia
                | split; left; auto]. }
      Intros vret. destruct vret as [[b3 f3] r3]. simpl fst in *. simpl snd in *.
      rewrite cmp_env_null, cmp_state_null.
      forward.
      match goal with H: iter_step _ _ _ _ _ _ _ |- _ =>
        destruct H as [_ Hex] end.
      specialize (Hex eq_refl).
      destruct Hex as [[Hr [Hb [Hf [Hb3 Hf3]]]] | [[Hb0 [Hr [Hb3 Hf3]]] | [Hf0 [Hr [Hb3 Hf3]]]]].
      * subst r3 b3 f3 b f.
        Exists (-1) (Zlength s) nullval 0. unfold cur_node; rewrite if_true by auto.
        entailer!.
      * subst r3 b3 f3.
        rewrite (L.nodes_split Ews s vs 0 b (b+1)) by lia.
        rewrite (toks_split s 0 b (b+1)) by lia.
        rewrite L.nodes_one, toks_one by lia.
        Exists (b-1)%Z f (Znth b s) b.
        unfold cur_node; rewrite if_false by (pose proof (Hptr b ltac:(lia)); intro Hx; rewrite Hx in *; contradiction).
        replace (b-1+1)%Z with b by lia.
        entailer!.
        right. split; [left; lia|]. split; [lia|]. split; auto.
      * subst r3 b3 f3.
        rewrite (L.nodes_split Ews s vs f (f+1) (Zlength s)) by lia.
        rewrite (toks_split s f (f+1) (Zlength s)) by lia.
        rewrite L.nodes_one, toks_one by lia.
        Exists b (f+1)%Z (Znth f s) f.
        unfold cur_node; rewrite if_false by (pose proof (Hptr f ltac:(lia)); intro Hx; rewrite Hx in *; contradiction).
        entailer!.
        right. split; [right; lia|]. split; [lia|]. split; auto.
    + (* after *)
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
  forward_call (gv, Ews, gv _input, input_contents, 2).
  { cbv; intros; discriminate. }
  forward.
  change (Zlength input_contents) with 5. cancel.
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
  semax_func_cons body_build.
  semax_func_cons body_client.
  semax_func_cons body_main.
Qed.
