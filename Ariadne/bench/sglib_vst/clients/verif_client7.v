Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import SglibVST.client7 SglibVST.spec_client7.
Require SglibVST.lib_client7.

Module L := SglibVST.lib_client7.

#[export] Existing Instance NullExtension.Espec.

Local Open Scope logic.

(* ================================================================== *)
(* The comparator resource: same_payload has no state.                *)
(* ================================================================== *)

Definition Rc_client (gv: globals) (f: val) : mpred := emp.

Fixpoint toks (l: list val) : mpred :=
  match l with nil => emp | x :: r => malloc_token Ews t_dl x * toks r end.

(* the malloc tokens of nodes lo .. hi-1 *)
Definition tokens (s: list val) (lo hi: Z) : mpred :=
  toks (sublist lo hi s).

(* ================================================================== *)
(* Helper lemmas                                                      *)
(* ================================================================== *)

Lemma toks_app: forall l1 l2, toks (l1 ++ l2) = toks l1 * toks l2.
Proof.
  induction l1; intros; simpl. rewrite emp_sepcon; auto.
  rewrite IHl1. rewrite sepcon_assoc. auto.
Qed.

Lemma tokens_split: forall s lo m hi, 0 <= lo <= m -> m <= hi <= Zlength s ->
  tokens s lo hi = tokens s lo m * tokens s m hi.
Proof.
  intros. unfold tokens. rewrite (sublist_split lo m hi) by lia.
  apply toks_app.
Qed.

Lemma tokens_one: forall s i, 0 <= i < Zlength s ->
  tokens s i (i+1) = malloc_token Ews t_dl (Znth i s).
Proof.
  intros. unfold tokens. rewrite sublist_len_1 by lia. simpl. apply sepcon_emp.
Qed.

Lemma tokens_empty: forall s i, tokens s i i = emp.
Proof. intros. unfold tokens. rewrite sublist_nil. reflexivity. Qed.

Lemma ins0: forall {A} {d: Inhabitant A} (e: A) s, ins 0 e s = e :: s.
Proof.
  intros. unfold ins. rewrite sublist_nil. rewrite sublist_same by auto. reflexivity.
Qed.

Lemma tokens_cons: forall s e,
  tokens (ins 0 e s) 0 (Zlength s + 1) = malloc_token Ews t_dl e * tokens s 0 (Zlength s).
Proof.
  intros. rewrite ins0. unfold tokens.
  rewrite sublist_same by list_solve. rewrite sublist_same by auto.
  reflexivity.
Qed.

Lemma nodesN_share_join: forall sh1 sh2 sh s vs n lo,
  sepalg.join sh1 sh2 sh ->
  nodesN sh1 s vs lo n * nodesN sh2 s vs lo n = nodesN sh s vs lo n.
Proof.
  induction n; intros; simpl.
  - apply sepcon_emp.
  - rewrite <- (IHn (lo+1) H).
    rewrite <- (data_at_share_join sh1 sh2 sh) by auto.
    apply pred_ext; cancel.
Qed.

Lemma nodes_share_join: forall sh1 sh2 sh s vs lo hi,
  sepalg.join sh1 sh2 sh ->
  nodes sh1 s vs lo hi * nodes sh2 s vs lo hi = nodes sh s vs lo hi.
Proof. intros. unfold nodes. apply nodesN_share_join; auto. Qed.

Definition sh1 := fst (slice.cleave Ews).
Definition sh2 := snd (slice.cleave Ews).
Lemma join_sh12: sepalg.join sh1 sh2 Ews.
Proof. apply slice.cleave_join. Qed.
Lemma readable_sh1: readable_share sh1.
Proof. apply slice.cleave_readable1. auto. Qed.
Lemma readable_sh2: readable_share sh2.
Proof. apply slice.cleave_readable2. auto. Qed.
#[export] Hint Resolve readable_sh1 readable_sh2 : core.

Lemma cmp_state_emp: forall gv scp, cmp_state Rc_client gv scp = emp.
Proof. intros. unfold cmp_state, Rc_client. destruct (Val.eq scp nullval); auto. Qed.

Lemma cmp_env_null: forall eqp sh veq, cmp_env Rc_client nullval eqp sh veq = emp.
Proof. intros. unfold cmp_env. rewrite if_true by auto. auto. Qed.

Lemma int_payloads_ins: forall vs vs' ev,
  map pay vs' = ins 0 ev (map pay vs) -> int_val ev ->
  int_payloads vs 0 (Zlength vs) -> int_payloads vs' 0 (Zlength vs').
Proof.
  intros vs vs' ev H Hev Hi.
  assert (Hl: Zlength vs' = Zlength vs + 1).
  { rewrite <- (Zlength_map _ _ pay vs'). rewrite H.
    rewrite L.Zlength_ins; rewrite ?Zlength_map; list_solve. }
  intros i Hr.
  replace (pay (Znth i vs')) with (Znth i (map pay vs')) by (rewrite Znth_map; auto; lia).
  rewrite H. rewrite L.Znth_ins by (rewrite ?Zlength_map; lia).
  destruct (zlt i 0); [lia|]. destruct (zeq i 0); auto.
  rewrite Znth_map by lia. apply Hi; lia.
Qed.

Lemma at_node_0: forall s, at_node s 0.
Proof.
  intros. destruct s. left; auto. right. rewrite Zlength_cons. list_solve.
Qed.

(* ================================================================== *)
(* Funspecs of the client's own functions                             *)
(* ================================================================== *)

Definition build_spec :=
 DECLARE _build
  WITH gv: globals, lp: val, inp: val, shi: share, ns: list int, n: Z
  PRE [ tptr (tptr t_dl), tptr tint, tint ]
    PROP (readable_share shi; n = Zlength ns; n <= Int.max_signed)
    PARAMS (lp; inp; Vint (Int.repr n)) GLOBALS (gv)
    SEP (mem_mgr gv; data_at shi (tarray tint n) (map Vint ns) inp;
         data_at Tsh (tptr t_dl) nullval lp)
  POST [ tint ]
    EX s: list val, EX vs: list node_v,
    PROP (whole s vs; int_payloads vs 0 (Zlength s))
    RETURN (Vint (Int.repr (Zlength s)))
    SEP (mem_mgr gv; data_at shi (tarray tint n) (map Vint ns) inp;
         data_at Tsh (tptr t_dl) (Znth_or_null s 0) lp;
         nodes Ews s vs 0 (Zlength s); tokens s 0 (Zlength s)).

Definition free_all_spec :=
 DECLARE _free_all
  WITH gv: globals, s: list val, vs: list node_v
  PRE [ tptr t_dl ]
    PROP (whole s vs)
    PARAMS (Znth_or_null s 0) GLOBALS (gv)
    SEP (mem_mgr gv; nodes Ews s vs 0 (Zlength s); tokens s 0 (Zlength s))
  POST [ tvoid ]
    PROP () RETURN () SEP (mem_mgr gv).

Definition same_payload_spec :=
  (_same_payload, cmp_spec Rc_client nullval).

Definition client_spec :=
 DECLARE _client
  WITH gv: globals, inp: val, shi: share, ns: list int, n: Z
  PRE [ tptr tint, tint ]
    PROP (readable_share shi; n = Zlength ns; n <= Int.max_signed)
    PARAMS (inp; Vint (Int.repr n)) GLOBALS (gv)
    SEP (mem_mgr gv; data_at shi (tarray tint n) (map Vint ns) inp)
  POST [ tuint ]
    EX r: int,
    PROP () RETURN (Vint r)
    SEP (mem_mgr gv; data_at shi (tarray tint n) (map Vint ns) inp).

Definition input_vals : list int := map Int.repr [6; 7; 3; 4; 7].

Definition main_spec :=
 DECLARE _main
  WITH gv: globals
  PRE [ ] main_pre prog tt gv
  POST [ tint ]
    PROP () RETURN (Vint (Int.repr 0))
    SEP (mem_mgr gv; data_at Ews (tarray tint 5) (map Vint input_vals) (gv _input);
         has_ext tt).

Definition client_specs : funspecs :=
  [build_spec; free_all_spec; same_payload_spec; client_spec; main_spec].

Definition Gprog : funspecs :=
  SglibVST.spec_client7.Gprog Rc_client ++ client_specs.

Lemma Gprog_lib_ids: forall i,
  In i [_sglib_dllist_add; _sglib_dllist_get_first; _sglib_dllist_get_last;
        _sglib_dllist_it_init_on_equal; _sglib_dllist_it_init; _sglib_dllist_it_next] ->
  VST.veric.initial_world.find_id i Gprog =
  VST.veric.initial_world.find_id i (SglibVST.spec_client7.Gprog Rc_client).
Proof. intros i H. simpl in H. repeat destruct H as [<-|H]; try reflexivity. contradiction. Qed.

(* ================================================================== *)
(* Library functions, from lib_client7                                *)
(* ================================================================== *)

Lemma sub_lib: forall f,
  tycontext_sub (func_tycontext f Vprog (SglibVST.spec_client7.Gprog Rc_client) [])
                (func_tycontext f Vprog Gprog []).
Proof.
  intros. apply tycontext_sub_Gprog_app1.
  - apply compute_list_norepet_e; reflexivity.
  - apply compute_list_norepet_e; reflexivity.
Qed.

Lemma body_add: semax_body Vprog Gprog f_sglib_dllist_add add_spec.
Proof. eapply semax_body_subsumption. apply (L.body_add Rc_client). apply sub_lib. Qed.
Lemma body_get_first: semax_body Vprog Gprog f_sglib_dllist_get_first get_first_spec.
Proof. eapply semax_body_subsumption. apply (L.body_get_first Rc_client). apply sub_lib. Qed.
Lemma body_get_last: semax_body Vprog Gprog f_sglib_dllist_get_last get_last_spec.
Proof. eapply semax_body_subsumption. apply (L.body_get_last Rc_client). apply sub_lib. Qed.
Lemma body_it_init_on_equal: semax_body Vprog Gprog f_sglib_dllist_it_init_on_equal
                               (it_init_on_equal_spec Rc_client).
Proof. eapply semax_body_subsumption. apply (L.body_it_init_on_equal Rc_client). apply sub_lib. Qed.
Lemma body_it_init: semax_body Vprog Gprog f_sglib_dllist_it_init it_init_spec.
Proof. eapply semax_body_subsumption. apply (L.body_it_init Rc_client). apply sub_lib. Qed.
Lemma body_it_next: semax_body Vprog Gprog f_sglib_dllist_it_next (it_next_spec Rc_client).
Proof. eapply semax_body_subsumption. apply (L.body_it_next Rc_client). apply sub_lib. Qed.

(* ================================================================== *)
(* Client functions                                                   *)
(* ================================================================== *)

Lemma body_same_payload: semax_body Vprog Gprog f_same_payload same_payload_spec.
Proof.
  start_function.
  destruct va as [pa [na qa]], vb as [pb [nb qb]].
  repeat match goal with H: int_val (pay (?p, _)) |- _ =>
    let i := fresh "i" in let E := fresh "E" in
    destruct H as [i E]; cbv [pay fst] in E; subst p end.
  rename i into ib, i0 into ia.
  forward. forward.
  forward_if (EX r: int, PROP () LOCAL (temp _t'1 (Vint r))
     SEP (data_at sha t_dl (Vint ia, (na, qa)) a; data_at shb t_dl (Vint ib, (nb, qb)) b;
          Rc_client gv nullval))%assert.
  - forward. Exists (Int.repr 0). entailer!.
  - forward. Exists (Int.repr 1). entailer!.
  - Intros r. forward. Exists r. entailer!.
Qed.

Lemma Znth_or_null_ins0: forall (p: val) s, Znth_or_null (ins 0 p s) 0 = p.
Proof.
  intros. rewrite ins0. rewrite L.Znth_or_null_in by list_solve. apply Znth_0_cons.
Qed.

Lemma whole_nil: whole [] [].
Proof.
  unfold whole, prev_links, next_links. rewrite !Zlength_nil.
  split; [auto | split; intros; lia].
Qed.

Lemma body_build: semax_body Vprog Gprog f_build build_spec.
Proof.
  start_function.
  forward.
  forward_loop
   (EX k:Z, EX s: list val, EX vs: list node_v,
    PROP (0 <= k <= n; Zlength s = k; whole s vs; int_payloads vs 0 (Zlength s))
    LOCAL (temp _m (Vint (Int.repr k)); temp _k (Vint (Int.repr k)); temp _list lp;
           temp _input__1 inp; temp _n (Vint (Int.repr n)); gvars gv)
    SEP (mem_mgr gv; data_at shi (tarray tint n) (map Vint ns) inp;
         data_at Tsh (tptr t_dl) (Znth_or_null s 0) lp;
         nodes Ews s vs 0 (Zlength s); tokens s 0 (Zlength s)))%assert
   continue:
   (EX k:Z, EX s: list val, EX vs: list node_v,
    PROP (0 <= k < n; Zlength s = (k+1)%Z; whole s vs; int_payloads vs 0 (Zlength s))
    LOCAL (temp _m (Vint (Int.repr (k+1))); temp _k (Vint (Int.repr k)); temp _list lp;
           temp _input__1 inp; temp _n (Vint (Int.repr n)); gvars gv)
    SEP (mem_mgr gv; data_at shi (tarray tint n) (map Vint ns) inp;
         data_at Tsh (tptr t_dl) (Znth_or_null s 0) lp;
         nodes Ews s vs 0 (Zlength s); tokens s 0 (Zlength s)))%assert
   break:
   (EX s: list val, EX vs: list node_v,
    PROP (whole s vs; int_payloads vs 0 (Zlength s))
    LOCAL (temp _m (Vint (Int.repr (Zlength s))))
    SEP (mem_mgr gv; data_at shi (tarray tint n) (map Vint ns) inp;
         data_at Tsh (tptr t_dl) (Znth_or_null s 0) lp;
         nodes Ews s vs 0 (Zlength s); tokens s 0 (Zlength s)))%assert.
  - forward. Exists 0 (@nil val) (@nil node_v).
    rewrite L.Znth_or_null_out by (rewrite Zlength_nil; lia).
    rewrite Zlength_nil. rewrite L.nodes_empty by lia. rewrite tokens_empty.
    entailer!. split; [apply whole_nil | intros i Hi; lia].
  - Intros k s vs.
    forward_if.
    + forward_call (t_dl, gv).
      Intros p.
      forward_if
       (PROP (p <> nullval)
        LOCAL (temp _l p; temp _m (Vint (Int.repr k)); temp _k (Vint (Int.repr k));
               temp _list lp; temp _input__1 inp; temp _n (Vint (Int.repr n)); gvars gv)
        SEP (mem_mgr gv; data_at shi (tarray tint n) (map Vint ns) inp;
             data_at Tsh (tptr t_dl) (Znth_or_null s 0) lp;
             nodes Ews s vs 0 (Zlength s); tokens s 0 (Zlength s);
             malloc_token Ews t_dl p; data_at_ Ews t_dl p))%assert.
      * destruct (eq_dec p nullval); entailer!.
      * rewrite if_true by auto.
        forward. Exists s vs. entailer!.
      * rewrite if_false by auto. forward. entailer!.
      * Intros.
        forward.
        forward.
        forward_call (Tsh, lp, Ews, p, Vint (Znth k ns), (Vundef, Vundef), s, vs, 0).
        { apply at_node_0. }
        Intros vs'.
        forward.
        Exists k (ins 0 p s) vs'.
        rewrite L.Zlength_ins by list_solve.
        rewrite tokens_cons. rewrite Znth_or_null_ins0.
        entailer!.
        match goal with Hw: whole (ins 0 p s) vs' |- _ =>
          destruct Hw as [Hl' _]; rewrite L.Zlength_ins in Hl' by list_solve end.
        rewrite <- Hl'.
        eapply int_payloads_ins; eauto.
        { eexists; reflexivity. }
        { match goal with Hw: whole s vs |- _ => destruct Hw as [Hl _] end.
          rewrite Hl. auto. }
    + forward. Exists s vs. entailer!.
  - Intros k s vs. forward. Exists (k+1) s vs. entailer!.
  - Intros s vs. forward. Exists s vs. entailer!.
Qed.

Lemma isptr_not_null: forall v, isptr v -> v <> nullval.
Proof. intros. destruct v; try contradiction. intro; discriminate. Qed.

Lemma isptr_pn: forall v, isptr v -> is_pointer_or_null v.
Proof. intros. destruct v; try contradiction. simpl; auto. Qed.

Lemma body_free_all: semax_body Vprog Gprog f_free_all free_all_spec.
Proof.
  start_function.
  rename H into Hw. assert (Hw' := Hw). destruct Hw' as [Hlen [Hp Hn]].
  assert_PROP (forall i, 0 <= i < Zlength s -> isptr (Znth i s)) as Hptr.
  { sep_apply (L.nodes_isptr Ews s vs 0 (Zlength s)). entailer!. }
  forward_call (Tsh, v_it, Ews, s, vs, 0).
  { repeat split; auto; try apply at_node_0.
    eapply L.prev_links_sub; eauto; lia. }
  Intros vret. destruct vret as [[b f] r]. simpl fst in *. simpl snd in *.
  match goal with H: init_window _ _ _ _ _ |- _ => rename H into Hiw end.
  destruct Hiw as [Hb [Hf [Hr [Hrn Hex]]]]. specialize (Hex eq_refl).
  forward_loop
   (EX b:Z, EX f:Z, EX r:val,
    PROP (-1 <= b < f; f <= Zlength s; is_pointer_or_null r;
          r = nullval -> b = -1 /\ f = Zlength s)
    LOCAL (temp _l r; lvar _it t_it v_it; gvars gv)
    SEP (mem_mgr gv; it_rep Tsh v_it s b f nullval nullval;
         nodes Ews s vs 0 (b+1); nodes Ews s vs f (Zlength s);
         tokens s 0 (b+1); tokens s f (Zlength s);
         if eq_dec r nullval then emp
         else (malloc_token Ews t_dl r * data_at_ Ews t_dl r)))%assert
   continue:
   (EX b:Z, EX f:Z,
    PROP (-1 <= b < f; f <= Zlength s)
    LOCAL (lvar _it t_it v_it; gvars gv)
    SEP (mem_mgr gv; it_rep Tsh v_it s b f nullval nullval;
         nodes Ews s vs 0 (b+1); nodes Ews s vs f (Zlength s);
         tokens s 0 (b+1); tokens s f (Zlength s)))%assert
   break:
   (EX b:Z, EX f:Z,
    PROP ()
    LOCAL (lvar _it t_it v_it; gvars gv)
    SEP (mem_mgr gv; it_rep Tsh v_it s b f nullval nullval))%assert.
  - destruct Hex as [[-> [-> [-> ->]]] | [c [Hc [-> [-> ->]]]]].
    + Exists (-1) 0 nullval. rewrite if_true by auto.
      rewrite Zlength_nil in *.
      rewrite !L.nodes_empty by lia. rewrite !tokens_empty.
      entailer!.
    + Exists (c-1) (c+1) (Znth c s).
      replace (c-1+1) with c by lia.
      assert (isptr (Znth c s)) by (apply Hptr; lia).
      rewrite if_false by (apply isptr_not_null; auto).
      rewrite (L.nodes_focus Ews s vs 0 c (Zlength s)) by lia.
      rewrite (tokens_split s 0 c (Zlength s)) by lia.
      rewrite (tokens_split s c (c+1) (Zlength s)) by lia.
      rewrite tokens_one by lia.
      entailer!.
      all: try (split; [apply isptr_pn; auto | intro Hc0; rewrite Hc0 in *; contradiction]).
      all: try (match goal with Hz: Znth _ _ = nullval |- _ => rewrite Hz in *; contradiction end).
  - Intros b0 f0 r0.
    forward_if.
    + destruct (eq_dec r0 nullval); [subst; entailer! | entailer!].
    + rewrite if_false by auto.
      forward_call (t_dl, r0, gv).
      { rewrite if_false by auto. cancel. }
      Exists b0 f0. entailer!.
    + forward.
      match goal with H: r0 = nullval -> _ |- _ => destruct (H ltac:(auto)) as [-> ->] end.
      Exists (-1) (Zlength s).
      rewrite if_true by auto. replace (-1+1) with 0 by lia.
      rewrite !L.nodes_empty by lia. rewrite !tokens_empty.
      entailer!.
  - Intros b0 f0.
    forward_call (gv, Tsh, v_it, Ews, s, vs, b0, f0, nullval, nullval, Ews,
                  (Vundef, (Vundef, Vundef))).
    { rewrite cmp_env_null, cmp_state_emp. cancel. }
    { repeat split; auto; try lia.
      eapply L.prev_links_sub; eauto; lia.
      eapply L.next_links_sub; eauto; lia.
      left; auto. left; auto. }
    Intros vret. destruct vret as [[b' f'] r']. simpl fst in *. simpl snd in *.
    rewrite cmp_env_null, cmp_state_emp.
    forward.
    match goal with H: iter_step _ _ _ _ _ _ _ |- _ => destruct H as [Hany Hex2] end.
    specialize (Hex2 eq_refl).
    destruct Hex2 as [[-> [-> [-> [-> ->]]]] | [[Hb0 [-> [-> ->]]] | [Hf0 [-> [-> ->]]]]].
    + Exists (-1) (Zlength s) nullval. rewrite if_true by auto. entailer!.
    + Exists (b0-1) f0 (Znth b0 s).
      replace (b0-1+1) with b0 by lia.
      assert (isptr (Znth b0 s)) by (apply Hptr; lia).
      rewrite if_false by (apply isptr_not_null; auto).
      rewrite (L.nodes_split Ews s vs 0 b0 (b0+1)) by lia. rewrite L.nodes_one.
      rewrite (tokens_split s 0 b0 (b0+1)) by lia. rewrite tokens_one by lia.
      entailer!.
      all: try (split; [apply isptr_pn; auto | intro Hc0; rewrite Hc0 in *; contradiction]).
      all: try (match goal with Hz: Znth _ _ = nullval |- _ => rewrite Hz in *; contradiction end).
    + Exists b0 (f0+1) (Znth f0 s).
      assert (isptr (Znth f0 s)) by (apply Hptr; lia).
      rewrite if_false by (apply isptr_not_null; auto).
      rewrite (L.nodes_split Ews s vs f0 (f0+1) (Zlength s)) by lia. rewrite L.nodes_one.
      rewrite (tokens_split s f0 (f0+1) (Zlength s)) by lia. rewrite tokens_one by lia.
      entailer!.
      all: try (split; [apply isptr_pn; auto | intro Hc0; rewrite Hc0 in *; contradiction]).
      all: try (match goal with Hz: Znth _ _ = nullval |- _ => rewrite Hz in *; contradiction end).
  - Intros b0 f0.
    unfold it_rep. Intros cur.
    unfold abbreviate in POSTCONDITION. subst POSTCONDITION.
    unfold frame_ret_assert, function_body_ret_assert, RA_normal.
    simpl normal_ret_assert. cbv iota beta.
    unfold stackframe_of. simpl fn_vars. simpl map. simpl fold_right.
    go_lowerx. entailer!.
    rewrite var_block_data_at_ by (auto; reflexivity).
    unfold_lift.
    rewrite (lvar_eval_lvar _it (Tstruct _sglib_dllist_iterator noattr) v_it rho H1).
    cancel.
Qed.

Lemma init_facts: forall scp s b f r, init_window scp s b f r ->
  -1 <= b < f /\ f <= Zlength s /\
  (r = nullval \/ exists c, 0 <= c < Zlength s /\ r = Znth c s).
Proof.
  intros scp s b f r [Hb [Hf [Hr _]]]. split; [lia | split; [lia |]].
  destruct Hr as [? | [c [? ?]]]; [left; auto | right; exists c; split; [lia | auto]].
Qed.

Lemma step_facts: forall scp s b f b' f' r, -1 <= b < f ->
  iter_step scp s b f b' f' r ->
  -1 <= b' < f' /\ f' <= Zlength s /\
  (r = nullval \/ exists c, 0 <= c < Zlength s /\ r = Znth c s).
Proof.
  intros scp s b f b' f' r Hb [[Hb' [Hf' [Hr _]]] _]. split; [lia | split; [lia |]].
  destruct Hr as [? | [c [? [? ?]]]]; [left; auto | right; exists c; split; [lia | auto]].
Qed.

Lemma split_nodes: forall s vs c, 0 <= c < Zlength s ->
  nodes Ews s vs 0 (Zlength s) |--
  nodes sh1 s vs 0 (Zlength s) * nodes sh2 s vs 0 c *
  data_at sh2 t_dl (Znth c vs) (Znth c s) * nodes sh2 s vs (c+1) (Zlength s).
Proof.
  intros. rewrite <- (nodes_share_join sh1 sh2 Ews s vs 0 (Zlength s) join_sh12).
  rewrite (L.nodes_focus sh2 s vs 0 c (Zlength s)) by lia. cancel.
Qed.

Lemma merge_nodes: forall s vs c, 0 <= c < Zlength s ->
  nodes sh1 s vs 0 (Zlength s) * nodes sh2 s vs 0 c *
  data_at sh2 t_dl (Znth c vs) (Znth c s) * nodes sh2 s vs (c+1) (Zlength s) |--
  nodes Ews s vs 0 (Zlength s).
Proof.
  intros. rewrite <- (nodes_share_join sh1 sh2 Ews s vs 0 (Zlength s) join_sh12).
  rewrite (L.nodes_focus sh2 s vs 0 c (Zlength s)) by lia. cancel.
Qed.

Lemma it_rep_data_at_: forall sh it s b f scp eqp,
  it_rep sh it s b f scp eqp |-- data_at_ sh t_it it.
Proof. intros. unfold it_rep. Intros cur. apply data_at_data_at_. Qed.

Lemma make_cmp_env: forall scp eqp sh veq,
  isptr scp -> readable_share sh -> int_val (pay veq) ->
  func_ptr' (cmp_spec Rc_client scp) scp * data_at sh t_dl veq eqp |--
  cmp_env Rc_client scp eqp sh veq.
Proof.
  intros. unfold cmp_env. rewrite if_false by (apply isptr_not_null; auto).
  entailer!.
Qed.

Lemma drop_cmp_env: forall scp eqp sh veq,
  isptr scp -> cmp_env Rc_client scp eqp sh veq |-- data_at sh t_dl veq eqp.
Proof.
  intros. unfold cmp_env. rewrite if_false by (apply isptr_not_null; auto).
  normalize. sep_apply (func_ptr'_emp (cmp_spec Rc_client scp) scp). cancel.
Qed.

Lemma body_client: semax_body Vprog Gprog f_client client_spec.
Proof.
  start_function.
  forward. forward.
  forward_call (gv, v_list, inp, shi, ns, n).
  Intros vret. destruct vret as [s vs]. simpl fst in *. simpl snd in *.
  rename H1 into Hw, H2 into Hint.
  assert (Hw' := Hw). destruct Hw' as [Hlen [Hp Hn]].
  assert_PROP (forall i, 0 <= i < Zlength s -> isptr (Znth i s)) as Hptr.
  { sep_apply (L.nodes_isptr Ews s vs 0 (Zlength s)). entailer!. }
  forward.
  { entailer!. apply (L.Znth_or_null_pn _ _ _ _ Hptr); lia. }
  forward_call (Tsh, v_outer, Ews, s, vs, 0).
  { repeat split; auto; try apply at_node_0.
    eapply L.prev_links_sub; eauto; lia. }
  Intros vret. destruct vret as [[b f] r]. simpl fst in *. simpl snd in *.
  match goal with H: init_window _ _ _ _ _ |- _ => apply init_facts in H; destruct H as [Hb [Hf Hr]] end.
  forward.
  forward_loop
   (EX b:Z, EX f:Z, EX r:val, EX cnt:int,
    PROP (-1 <= b < f; f <= Zlength s;
          r = nullval \/ exists c, 0 <= c < Zlength s /\ r = Znth c s)
    LOCAL (temp _l r; temp _count (Vint cnt); lvar _inner t_it v_inner;
           lvar _outer t_it v_outer; lvar _list (tptr t_dl) v_list; gvars gv)
    SEP (mem_mgr gv; data_at shi (tarray tint n) (map Vint ns) inp;
         data_at Tsh (tptr t_dl) (Znth_or_null s 0) v_list;
         nodes Ews s vs 0 (Zlength s); tokens s 0 (Zlength s);
         data_at_ Tsh t_it v_inner;
         it_rep Tsh v_outer s b f nullval nullval))%assert
   continue:
   (EX b:Z, EX f:Z, EX cnt:int,
    PROP (-1 <= b < f; f <= Zlength s)
    LOCAL (temp _count (Vint cnt); lvar _inner t_it v_inner;
           lvar _outer t_it v_outer; lvar _list (tptr t_dl) v_list; gvars gv)
    SEP (mem_mgr gv; data_at shi (tarray tint n) (map Vint ns) inp;
         data_at Tsh (tptr t_dl) (Znth_or_null s 0) v_list;
         nodes Ews s vs 0 (Zlength s); tokens s 0 (Zlength s);
         data_at_ Tsh t_it v_inner;
         it_rep Tsh v_outer s b f nullval nullval))%assert
   break:
   (EX b:Z, EX f:Z, EX cnt:int,
    PROP ()
    LOCAL (temp _count (Vint cnt); lvar _inner t_it v_inner;
           lvar _outer t_it v_outer; lvar _list (tptr t_dl) v_list; gvars gv)
    SEP (mem_mgr gv; data_at shi (tarray tint n) (map Vint ns) inp;
         data_at Tsh (tptr t_dl) (Znth_or_null s 0) v_list;
         nodes Ews s vs 0 (Zlength s); tokens s 0 (Zlength s);
         data_at_ Tsh t_it v_inner;
         it_rep Tsh v_outer s b f nullval nullval))%assert.
  - (* entry *)
    Exists b f r (Int.repr 0). entailer!.
  - (* outer body *)
    Intros b0 f0 r0 cnt.
    match goal with H: r0 = nullval \/ _ |- _ => rename H into Hr0 end.
    forward_if.
    + destruct Hr0 as [-> | [c' [Hc' ->]]]; [entailer! |].
      rewrite (L.nodes_focus Ews s vs 0 c' (Zlength s)) by lia. entailer!.
    + destruct Hr0 as [-> | [c [Hc ->]]]; [exfalso; auto |].
      forward.
      { entailer!. apply (L.Znth_or_null_pn _ _ _ _ Hptr); lia. }
      make_func_ptr _same_payload.
      assert_PROP (isptr (gv _same_payload)) as Hsp.
      { sep_apply (func_ptr'_isptr (cmp_spec Rc_client nullval) (gv _same_payload)).
        entailer!. }
      change (func_ptr' (cmp_spec Rc_client nullval) (gv _same_payload)) with
             (func_ptr' (cmp_spec Rc_client (gv _same_payload)) (gv _same_payload)).
      sep_apply (split_nodes s vs c Hc).
      assert (Hic: int_val (pay (Znth c vs))) by (apply Hint; lia).
      sep_apply (make_cmp_env (gv _same_payload) (Znth c s) sh2 (Znth c vs) Hsp readable_sh2 Hic).
      forward_call (gv, Tsh, v_inner, sh1, s, vs, 0, gv _same_payload, Znth c s, sh2, Znth c vs).
      { rewrite cmp_state_emp. cancel. }
      { split; [apply at_node_0 | split; [eapply L.prev_links_sub; eauto; lia | right; auto]]. }
      Intros vret. destruct vret as [[b2 f2] r2]. simpl fst in *. simpl snd in *.
      match goal with H: init_window _ _ _ _ _ |- _ => apply init_facts in H; destruct H as [Hb2 [Hf2 Hr2]] end.
      rewrite cmp_state_emp.
      forward.
      forward_loop
       (EX b2:Z, EX f2:Z, EX r2:val, EX cnt2:int,
        PROP (-1 <= b2 < f2; f2 <= Zlength s;
              r2 = nullval \/ exists c2, 0 <= c2 < Zlength s /\ r2 = Znth c2 s)
        LOCAL (temp _m r2; temp _l (Znth c s); temp _count (Vint cnt2);
               lvar _inner t_it v_inner;
               lvar _outer t_it v_outer; lvar _list (tptr t_dl) v_list; gvars gv)
        SEP (it_rep Tsh v_inner s b2 f2 (gv _same_payload) (Znth c s);
             nodes sh1 s vs 0 (Zlength s);
             cmp_env Rc_client (gv _same_payload) (Znth c s) sh2 (Znth c vs);
             nodes sh2 s vs 0 c; nodes sh2 s vs (c + 1) (Zlength s); mem_mgr gv;
             data_at shi (tarray tint n) (map Vint ns) inp;
             data_at Tsh (tptr t_dl) (Znth_or_null s 0) v_list;
             tokens s 0 (Zlength s); it_rep Tsh v_outer s b0 f0 nullval nullval))%assert
       continue:
       (EX b2:Z, EX f2:Z, EX cnt2:int,
        PROP (-1 <= b2 < f2; f2 <= Zlength s)
        LOCAL (temp _l (Znth c s); temp _count (Vint cnt2);
               lvar _inner t_it v_inner;
               lvar _outer t_it v_outer; lvar _list (tptr t_dl) v_list; gvars gv)
        SEP (it_rep Tsh v_inner s b2 f2 (gv _same_payload) (Znth c s);
             nodes sh1 s vs 0 (Zlength s);
             cmp_env Rc_client (gv _same_payload) (Znth c s) sh2 (Znth c vs);
             nodes sh2 s vs 0 c; nodes sh2 s vs (c + 1) (Zlength s); mem_mgr gv;
             data_at shi (tarray tint n) (map Vint ns) inp;
             data_at Tsh (tptr t_dl) (Znth_or_null s 0) v_list;
             tokens s 0 (Zlength s); it_rep Tsh v_outer s b0 f0 nullval nullval))%assert
       break:
       (EX b2:Z, EX f2:Z, EX cnt2:int,
        PROP ()
        LOCAL (temp _l (Znth c s); temp _count (Vint cnt2);
               lvar _inner t_it v_inner;
               lvar _outer t_it v_outer; lvar _list (tptr t_dl) v_list; gvars gv)
        SEP (it_rep Tsh v_inner s b2 f2 (gv _same_payload) (Znth c s);
             nodes sh1 s vs 0 (Zlength s);
             cmp_env Rc_client (gv _same_payload) (Znth c s) sh2 (Znth c vs);
             nodes sh2 s vs 0 c; nodes sh2 s vs (c + 1) (Zlength s); mem_mgr gv;
             data_at shi (tarray tint n) (map Vint ns) inp;
             data_at Tsh (tptr t_dl) (Znth_or_null s 0) v_list;
             tokens s 0 (Zlength s); it_rep Tsh v_outer s b0 f0 nullval nullval))%assert.
      * Exists b2 f2 r2 cnt. entailer!.
      * Intros b3 f3 r3 cnt2.
        match goal with H: r3 = nullval \/ _ |- _ => rename H into Hr3 end.
        forward_if.
        { destruct Hr3 as [-> | [c' [Hc' ->]]]; [entailer! |].
          rewrite (L.nodes_focus sh1 s vs 0 c' (Zlength s)) by lia. entailer!. }
        { forward. Exists b3 f3 (Int.add cnt2 (Int.repr 1)). entailer!. }
        { forward. Exists b3 f3 cnt2. entailer!. }
      * Intros b3 f3 cnt2.
        rewrite (L.nodes_split sh1 s vs 0 (b3+1) (Zlength s)) by lia.
        rewrite (L.nodes_split sh1 s vs (b3+1) f3 (Zlength s)) by lia.
        forward_call (gv, Tsh, v_inner, sh1, s, vs, b3, f3, gv _same_payload, Znth c s,
                      sh2, Znth c vs).
        { rewrite cmp_state_emp. cancel. }
        { repeat split; auto; try lia.
          - eapply L.prev_links_sub; eauto; lia.
          - eapply L.next_links_sub; eauto; lia.
          - right. intros i Hi. apply Hint; lia.
          - right. intros i Hi. apply Hint; lia. }
        Intros vret. destruct vret as [[b4 f4] r4]. simpl fst in *. simpl snd in *.
        match goal with H: iter_step _ _ _ _ _ _ _ |- _ =>
          apply step_facts in H; [destruct H as [Hb4 [Hf4 Hr4]] | lia] end.
        rewrite cmp_state_emp.
        forward.
        Exists b4 f4 r4 cnt2.
        rewrite (L.nodes_split sh1 s vs 0 (b3+1) (Zlength s)) by lia.
        rewrite (L.nodes_split sh1 s vs (b3+1) f3 (Zlength s)) by lia.
        entailer!.
      * Intros b3 f3 cnt2.
        sep_apply (drop_cmp_env (gv _same_payload) (Znth c s) sh2 (Znth c vs) Hsp).
        sep_apply (merge_nodes s vs c Hc).
        sep_apply (it_rep_data_at_ Tsh v_inner s b3 f3 (gv _same_payload) (Znth c s)).
        Exists b0 f0 cnt2. entailer!.
    + forward.
      Exists b0 f0 cnt. entailer!.
  - (* outer step *)
    Intros b0 f0 cnt.
    rewrite (L.nodes_split Ews s vs 0 (b0+1) (Zlength s)) by lia.
    rewrite (L.nodes_split Ews s vs (b0+1) f0 (Zlength s)) by lia.
    forward_call (gv, Tsh, v_outer, Ews, s, vs, b0, f0, nullval, nullval, Ews,
                  (Vundef, (Vundef, Vundef))).
    { rewrite cmp_env_null, cmp_state_emp. cancel. }
    { repeat split; auto; try lia.
      - eapply L.prev_links_sub; eauto; lia.
      - eapply L.next_links_sub; eauto; lia.
      - left; auto.
      - left; auto. }
    Intros vret. destruct vret as [[b4 f4] r4]. simpl fst in *. simpl snd in *.
    match goal with H: iter_step _ _ _ _ _ _ _ |- _ =>
      apply step_facts in H; [destruct H as [Hb4 [Hf4 Hr4]] | lia] end.
    rewrite cmp_env_null, cmp_state_emp.
    forward.
    Exists b4 f4 r4 cnt.
    rewrite (L.nodes_split Ews s vs 0 (b0+1) (Zlength s)) by lia.
    rewrite (L.nodes_split Ews s vs (b0+1) f0 (Zlength s)) by lia.
    entailer!.
  - (* after the loops *)
    Intros b0 f0 cnt.
    forward.
    { entailer!. apply (L.Znth_or_null_pn _ _ _ _ Hptr); lia. }
    forward_call (gv, s, vs).
    sep_apply (it_rep_data_at_ Tsh v_outer s b0 f0 nullval nullval).
    forward.
    Exists cnt. entailer!.
Qed.

Lemma body_main: semax_body Vprog Gprog f_main main_spec.
Proof.
  start_function.
  sep_apply (create_mem_mgr gv).
  forward_call (gv, gv _input, Ews, input_vals, 5).
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
  semax_func_cons body_build.
  semax_func_cons body_free_all.
  semax_func_cons body_same_payload.
  semax_func_cons body_client.
  semax_func_cons body_main.
Qed.
