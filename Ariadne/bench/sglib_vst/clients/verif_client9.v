Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import SglibVST.client9 SglibVST.spec_client9.
Require SglibVST.lib_client9.

Module L := SglibVST.lib_client9.

Local Open Scope logic.

(* ================================================================== *)
(* Comparator state: the global counter, any value                    *)
(* ================================================================== *)

Definition Rc_client (gv: globals) (_: val) : mpred :=
  EX k: int, data_at Ews tuint (Vint k) (gv _counter).

Fixpoint toks (l: list val) : mpred :=
  match l with nil => emp | x :: l' => malloc_token Ews t_dl x * toks l' end.

Lemma toks_app: forall l1 l2, toks (l1 ++ l2) = toks l1 * toks l2.
Proof.
  induction l1; intros; simpl. rewrite emp_sepcon; auto.
  rewrite IHl1. rewrite sepcon_assoc. auto.
Qed.

(* malloc tokens of nodes lo .. hi-1 *)
Definition tokens (s: list val) (lo hi: Z) : mpred := toks (sublist lo hi s).

(* the node returned last by free_all's iteration, not yet freed *)
Definition cur_node (s: list val) (vs: list node_v) (c: Z) : mpred :=
  if zle 0 c
  then data_at Ews t_dl (Znth c vs) (Znth c s) * malloc_token Ews t_dl (Znth c s)
  else emp.

(* ================================================================== *)
(* Helper lemmas                                                      *)
(* ================================================================== *)

Lemma tokens_split: forall s lo m hi,
  0 <= lo <= m -> m <= hi <= Zlength s ->
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

Lemma tokens_empty: forall s i j, j <= i -> tokens s i j = emp.
Proof.
  intros. unfold tokens. rewrite sublist_nil_gen by lia. reflexivity.
Qed.

Lemma tokens_cons: forall x s,
  tokens (x::s) 0 (Zlength (x::s)) = malloc_token Ews t_dl x * tokens s 0 (Zlength s).
Proof.
  intros. unfold tokens. rewrite !sublist_same by lia. reflexivity.
Qed.

Lemma cur_node_neg: forall s vs c, c < 0 -> cur_node s vs c = emp.
Proof. intros. unfold cur_node. destruct (zle 0 c); [lia|auto]. Qed.

Lemma cur_node_pos: forall s vs c, 0 <= c -> cur_node s vs c =
  data_at Ews t_dl (Znth c vs) (Znth c s) * malloc_token Ews t_dl (Znth c s).
Proof. intros. unfold cur_node. destruct (zle 0 c); [auto|lia]. Qed.

Lemma ins0: forall {A} {d: Inhabitant A} (x: A) (l: list A), ins 0 x l = x :: l.
Proof.
  intros. unfold ins. rewrite sublist_nil. rewrite sublist_same by lia. reflexivity.
Qed.

Lemma int_payloads_ins0: forall (vs vs': list node_v) ev,
  int_payloads vs 0 (Zlength vs) -> int_val ev ->
  map pay vs' = ins 0 ev (map pay vs) ->
  int_payloads vs' 0 (Zlength vs').
Proof.
  intros vs vs' ev H Hev H1. rewrite ins0 in H1.
  assert (Hl: Zlength vs' = Zlength vs + 1).
  { apply (f_equal (@Zlength val)) in H1. rewrite Zlength_cons, !Zlength_map in H1. auto. }
  intros i Hi.
  assert (E: pay (Znth i vs') = Znth i (map pay vs')) by (rewrite Znth_map by lia; auto).
  rewrite E, H1.
  destruct (zeq i 0).
  - subst. rewrite Znth_0_cons. auto.
  - rewrite Znth_pos_cons by lia. rewrite Znth_map by lia. apply H. lia.
Qed.

Lemma nodes_last: forall sh s vs lo i, lo <= i ->
  nodes sh s vs lo (i+1) = nodes sh s vs lo i * data_at sh t_dl (Znth i vs) (Znth i s).
Proof.
  intros. rewrite (L.nodes_split sh s vs lo i (i+1)) by lia. rewrite L.nodes_one. auto.
Qed.

Lemma nodes_first: forall sh s vs i hi, i < hi ->
  nodes sh s vs i hi = data_at sh t_dl (Znth i vs) (Znth i s) * nodes sh s vs (i+1) hi.
Proof.
  intros. rewrite (L.nodes_split sh s vs i (i+1) hi) by lia. rewrite L.nodes_one. auto.
Qed.

(* ================================================================== *)
(* Specs of the client's functions                                    *)
(* ================================================================== *)

Definition build_spec :=
 DECLARE _build
  WITH gv: globals, lp: val, ip: val, sh: share, contents: list Z, n: Z
  PRE [ tptr (tptr t_dl), tptr tint, tint ]
    PROP (readable_share sh; 0 <= n <= Zlength contents;
          Zlength contents <= Int.max_signed)
    PARAMS (lp; ip; Vint (Int.repr n)) GLOBALS (gv)
    SEP (mem_mgr gv; data_at Tsh (tptr t_dl) nullval lp;
         data_at sh (tarray tint (Zlength contents))
           (map Vint (map Int.repr contents)) ip)
  POST [ tint ]
    EX s: list val, EX vs: list node_v,
    PROP (whole s vs; int_payloads vs 0 (Zlength s); Zlength s <= n)
    RETURN (Vint (Int.repr (Zlength s)))
    SEP (mem_mgr gv; data_at Tsh (tptr t_dl) (Znth_or_null s 0) lp;
         nodes Ews s vs 0 (Zlength s); tokens s 0 (Zlength s);
         data_at sh (tarray tint (Zlength contents))
           (map Vint (map Int.repr contents)) ip).

Definition free_all_spec :=
 DECLARE _free_all
  WITH gv: globals, s: list val, vs: list node_v
  PRE [ tptr t_dl ]
    PROP (whole s vs)
    PARAMS (Znth_or_null s 0) GLOBALS (gv)
    SEP (mem_mgr gv; nodes Ews s vs 0 (Zlength s); tokens s 0 (Zlength s))
  POST [ tvoid ]
    PROP () RETURN () SEP (mem_mgr gv).

Definition counting_cmp_spec :=
  DECLARE _counting_cmp (cmp_spec Rc_client nullval).

Definition client_spec :=
 DECLARE _client
  WITH gv: globals, ip: val, sh: share, contents: list Z, n: Z
  PRE [ tptr tint, tint ]
    PROP (readable_share sh; 0 <= n <= Zlength contents;
          1 <= Zlength contents <= Int.max_signed)
    PARAMS (ip; Vint (Int.repr n)) GLOBALS (gv)
    SEP (mem_mgr gv;
         data_at sh (tarray tint (Zlength contents))
           (map Vint (map Int.repr contents)) ip;
         Rc_client gv nullval)
  POST [ tuint ]
    EX r: int,
    PROP () RETURN (Vint r)
    SEP (mem_mgr gv;
         data_at sh (tarray tint (Zlength contents))
           (map Vint (map Int.repr contents)) ip;
         Rc_client gv nullval).

Definition main_spec :=
 DECLARE _main
  WITH gv: globals
  PRE [ ] main_pre prog tt gv
  POST [ tint ]
    EX k: int,
    PROP () RETURN (Vint (Int.repr 0))
    SEP (mem_mgr gv; has_ext tt;
         data_at Ews (tarray tint 5)
           (map Vint (map Int.repr [6;7;3;4;7])) (gv _input);
         data_at Ews tuint (Vint k) (gv _counter)).

Definition own_specs : funspecs :=
  [build_spec; free_all_spec; counting_cmp_spec; client_spec; main_spec].

Definition Gprog : funspecs := SglibVST.spec_client9.Gprog Rc_client ++ own_specs.

#[export] Existing Instance NullExtension.Espec.

(* ================================================================== *)
(* Library functions, from lib_client9                                *)
(* ================================================================== *)

Lemma Gprog_sub: forall f,
  tycontext_sub (func_tycontext f Vprog (SglibVST.spec_client9.Gprog Rc_client) [])
                (func_tycontext f Vprog Gprog []).
Proof.
  intros. unfold Gprog.
  apply tycontext_sub_Gprog_app1.
  - apply compute_list_norepet_e; reflexivity.
  - apply compute_list_norepet_e; reflexivity.
Qed.

Lemma body_add: semax_body Vprog Gprog f_sglib_dllist_add add_spec.
Proof. eapply semax_body_subsumption. apply (L.body_add Rc_client). apply Gprog_sub. Qed.

Lemma body_get_first: semax_body Vprog Gprog f_sglib_dllist_get_first get_first_spec.
Proof. eapply semax_body_subsumption. apply (L.body_get_first Rc_client). apply Gprog_sub. Qed.

Lemma body_get_last: semax_body Vprog Gprog f_sglib_dllist_get_last get_last_spec.
Proof. eapply semax_body_subsumption. apply (L.body_get_last Rc_client). apply Gprog_sub. Qed.

Lemma body_it_init_on_equal: semax_body Vprog Gprog f_sglib_dllist_it_init_on_equal
  (it_init_on_equal_spec Rc_client).
Proof. eapply semax_body_subsumption. apply (L.body_it_init_on_equal Rc_client). apply Gprog_sub. Qed.

Lemma body_it_init: semax_body Vprog Gprog f_sglib_dllist_it_init it_init_spec.
Proof. eapply semax_body_subsumption. apply (L.body_it_init Rc_client). apply Gprog_sub. Qed.

Lemma body_it_next: semax_body Vprog Gprog f_sglib_dllist_it_next (it_next_spec Rc_client).
Proof. eapply semax_body_subsumption. apply (L.body_it_next Rc_client). apply Gprog_sub. Qed.

(* ================================================================== *)
(* Client functions                                                   *)
(* ================================================================== *)

Lemma body_counting_cmp: semax_body Vprog Gprog f_counting_cmp counting_cmp_spec.
Proof.
  start_function.
  destruct H as [ia Ha]. destruct H0 as [ib Hb].
  destruct va as [pa [na qa]], vb as [pb [nb qb]].
  unfold pay in Ha, Hb; simpl in Ha, Hb; subst pa pb.
  unfold Rc_client. Intros k.
  forward. forward. forward. forward.
  forward_if (EX r: int, PROP () LOCAL (temp _t'1 (Vint r); gvars gv)
     SEP (data_at Ews tuint (Vint (Int.add k (Int.repr 1))) (gv _counter);
          data_at sha t_dl (Vint ia, (na, qa)) a; data_at shb t_dl (Vint ib, (nb, qb)) b))%assert.
  - forward. Exists (Int.repr 0). entailer!.
  - forward. Exists (Int.repr 1). entailer!.
  - Intros r. forward. Exists r. unfold Rc_client. Exists (Int.add k (Int.repr 1)). entailer!.
Qed.

Lemma body_build: semax_body Vprog Gprog f_build build_spec.
Proof.
  start_function.
  forward.
  forward_loop
    (EX k: Z, EX s: list val, EX vs: list node_v,
     PROP (0 <= k <= n; whole s vs; int_payloads vs 0 (Zlength s); Zlength s <= k)
     LOCAL (temp _m (Vint (Int.repr (Zlength s))); temp _k (Vint (Int.repr k));
            temp _list lp; temp _input__1 ip; temp _n (Vint (Int.repr n)); gvars gv)
     SEP (mem_mgr gv; data_at Tsh (tptr t_dl) (Znth_or_null s 0) lp;
          nodes Ews s vs 0 (Zlength s); tokens s 0 (Zlength s);
          data_at sh (tarray tint (Zlength contents))
            (map Vint (map Int.repr contents)) ip))
  continue:
    (EX k: Z, EX s: list val, EX vs: list node_v,
     PROP (0 <= k < n; whole s vs; int_payloads vs 0 (Zlength s); Zlength s <= k+1)
     LOCAL (temp _m (Vint (Int.repr (Zlength s))); temp _k (Vint (Int.repr k));
            temp _list lp; temp _input__1 ip; temp _n (Vint (Int.repr n)); gvars gv)
     SEP (mem_mgr gv; data_at Tsh (tptr t_dl) (Znth_or_null s 0) lp;
          nodes Ews s vs 0 (Zlength s); tokens s 0 (Zlength s);
          data_at sh (tarray tint (Zlength contents))
            (map Vint (map Int.repr contents)) ip))
  break:
    (EX s: list val, EX vs: list node_v,
     PROP (whole s vs; int_payloads vs 0 (Zlength s); Zlength s <= n)
     LOCAL (temp _m (Vint (Int.repr (Zlength s))); gvars gv)
     SEP (mem_mgr gv; data_at Tsh (tptr t_dl) (Znth_or_null s 0) lp;
          nodes Ews s vs 0 (Zlength s); tokens s 0 (Zlength s);
          data_at sh (tarray tint (Zlength contents))
            (map Vint (map Int.repr contents)) ip)).
  - forward. Exists 0 (@nil val) (@nil node_v).
    rewrite (L.Znth_or_null_out [] 0) by (rewrite Zlength_nil; lia).
    change (Zlength (@nil val)) with 0.
    rewrite (L.nodes_empty Ews [] [] 0 0) by lia. rewrite tokens_empty by lia.
    entailer!.
    split; [|intros i Hi; lia].
    split; [reflexivity|]. split; intros i Hi; rewrite Zlength_nil in Hi; lia.
  - Intros k s vs.
    forward_if.
    2:{ forward. Exists s vs. entailer!. }
    forward_call (t_dl, gv).
    Intros p.
    forward_if (PROP (p <> nullval)
      LOCAL (temp _l p; temp _m (Vint (Int.repr (Zlength s)));
             temp _k (Vint (Int.repr k)); temp _list lp; temp _input__1 ip;
             temp _n (Vint (Int.repr n)); gvars gv)
      SEP (mem_mgr gv; malloc_token Ews t_dl p; data_at_ Ews t_dl p;
           data_at Tsh (tptr t_dl) (Znth_or_null s 0) lp;
           nodes Ews s vs 0 (Zlength s); tokens s 0 (Zlength s);
           data_at sh (tarray tint (Zlength contents))
             (map Vint (map Int.repr contents)) ip))%assert.
    + if_tac; entailer!.
    + forward. Exists s vs. rewrite if_true by auto. entailer!.
    + rewrite if_false by auto. forward. entailer!.
    + Intros.
      forward.
      forward.
      assert (Hlen: Zlength vs = Zlength s) by (destruct H2; auto).
      assert (Hat: at_node s 0).
      { destruct s; [left; auto | right; rewrite Zlength_cons; list_solve]. }
      forward_call (Tsh, lp, Ews, p, Vint (Int.repr (Znth k contents)),
                    snd (default_val t_dl), s, vs, 0).
      Intros vs'.
      match goal with Hm: map pay vs' = _ |- _ =>
        assert (Hip: int_payloads vs' 0 (Zlength vs'))
          by (eapply int_payloads_ins0; [rewrite Hlen; exact H3 | eexists; reflexivity | exact Hm])
      end.
      rewrite !ins0 in *.
      match goal with Hw: whole (p :: s) vs' |- _ =>
        assert (Hw' := Hw); destruct Hw as [Hl' _] end.
      rewrite Zlength_cons in Hl'.
      rewrite Hl' in Hip.
      forward.
      Exists k (p::s) vs'.
      rewrite tokens_cons.
      rewrite (L.Znth_or_null_in (p::s) 0) by (rewrite Zlength_cons; list_solve).
      rewrite Znth_0_cons.
      rewrite Zlength_cons.
      entailer!.
      unfold Z.succ; apply derives_refl.
  - Intros k s vs.
    forward.
    Exists (k+1) s vs.
    entailer!.
  - Intros s vs.
    forward.
    Exists s vs.
    entailer!.
Qed.

Lemma body_free_all: semax_body Vprog Gprog f_free_all free_all_spec.
Proof.
  start_function.
  assert (Hw := H). destruct H as [Hlen [Hprev Hnext]].
  assert_PROP (forall i, 0 <= i < Zlength s -> isptr (Znth i s)) as Hp.
  { sep_apply (L.nodes_isptr Ews s vs 0 (Zlength s)). entailer!. }
  assert (Hat: at_node s 0).
  { destruct s; [left; auto | right; rewrite Zlength_cons; list_solve]. }
  assert (Hpl: prev_links s vs 0 (Z.min (0+1) (Zlength s)))
    by (eapply L.prev_links_sub; eauto; lia).
  forward_call (Tsh, v_it, Ews, s, vs, 0).
  Intros vret. destruct vret as [[b0 f0] r0]. simpl fst in *. simpl snd in *.
  match goal with Hi: init_window nullval s b0 f0 r0 |- _ =>
    destruct Hi as [Hbf [Hfl [_ [_ Hex]]]] end.
  specialize (Hex eq_refl).
  forward_loop
   (EX b: Z, EX f: Z, EX c: Z,
    PROP (-1 <= b < f; f <= Zlength s;
          (c = -1 /\ b = -1 /\ f = Zlength s) \/ (0 <= c < Zlength s))
    LOCAL (temp _l (Znth_or_null s c); lvar _it t_it v_it; gvars gv)
    SEP (it_rep Tsh v_it s b f nullval nullval;
         nodes Ews s vs 0 (b+1); nodes Ews s vs f (Zlength s);
         tokens s 0 (b+1); tokens s f (Zlength s);
         cur_node s vs c; mem_mgr gv))%assert
  continue:
   (EX b: Z, EX f: Z,
    PROP (-1 <= b < f; f <= Zlength s)
    LOCAL (lvar _it t_it v_it; gvars gv)
    SEP (it_rep Tsh v_it s b f nullval nullval;
         nodes Ews s vs 0 (b+1); nodes Ews s vs f (Zlength s);
         tokens s 0 (b+1); tokens s f (Zlength s); mem_mgr gv))%assert
  break:
   (PROP () LOCAL (lvar _it t_it v_it; gvars gv)
    SEP (data_at_ Tsh t_it v_it; mem_mgr gv))%assert.
  - destruct Hex as [[-> [-> [-> ->]]] | [c [Hc [-> [-> ->]]]]].
    + Exists (-1) 0 (-1).
      rewrite (L.Znth_or_null_out [] (-1)) by lia.
      rewrite cur_node_neg by lia.
      change (Zlength (@nil val)) with 0.
      replace (-1+1) with 0 by lia.
      rewrite !(L.nodes_empty Ews [] vs 0 0) by lia.
      rewrite !tokens_empty by lia.
      entailer!.
    + Exists (c-1) (c+1) c.
      replace (c-1+1) with c by lia.
      rewrite (L.nodes_focus Ews s vs 0 c (Zlength s)) by lia.
      rewrite (tokens_split s 0 c (Zlength s)) by lia.
      rewrite (tokens_split s c (c+1) (Zlength s)) by lia.
      rewrite (tokens_one s c) by lia.
      rewrite (L.Znth_or_null_in s c) by lia.
      rewrite cur_node_pos by lia.
      entailer!.
  - Intros b f c.
    destruct H1 as [[-> [-> ->]] | Hc].
    + rewrite (L.Znth_or_null_out s (-1)) by lia.
      rewrite cur_node_neg by lia.
      forward_if.
      { discriminate. }
      forward.
      replace (-1+1) with 0 by lia.
      rewrite (L.nodes_empty Ews s vs 0 0) by lia.
      rewrite (L.nodes_empty Ews s vs (Zlength s) (Zlength s)) by lia.
      rewrite !tokens_empty by lia.
      unfold it_rep. Intros cur.
      entailer!.
    + assert (Hpc := Hp c Hc).
      rewrite (L.Znth_or_null_in s c) by lia.
      rewrite cur_node_pos by lia. Intros.
      forward_if.
      2:{ match goal with Hn: Znth c s = nullval |- _ => rewrite Hn in Hpc; contradiction end. }
      forward_call (t_dl, Znth c s, gv).
      { rewrite if_false by assumption. cancel. }
      Exists b f. entailer!.
  - Intros b f.
    assert (prev_links s vs 0 (b+1))
      by (apply (L.prev_links_sub s vs 0 (Zlength s)); auto; lia).
    assert (next_links s vs f (Zlength s))
      by (apply (L.next_links_sub s vs 0 (Zlength s)); auto; lia).
    forward_call (gv, Tsh, v_it, Ews, s, vs, b, f, nullval, nullval, Tsh,
                  (Vundef, (Vundef, Vundef))).
    { unfold cmp_env, cmp_state. rewrite !if_true by auto. cancel. }
    { split; left; auto. }
    Intros vret. destruct vret as [[b' f'] r']. simpl fst in *. simpl snd in *.
    forward.
    match goal with Hi: iter_step nullval s b f b' f' r' |- _ =>
      destruct Hi as [_ Hex2] end.
    specialize (Hex2 eq_refl).
    destruct Hex2 as [[-> [-> [-> [-> ->]]]] | [[Hb1 [-> [-> ->]]] | [Hf1 [-> [-> ->]]]]].
    + Exists (-1) (Zlength s) (-1).
      rewrite (L.Znth_or_null_out s (-1)) by lia.
      rewrite cur_node_neg by lia.
      entailer!.
    + Exists (b-1) f b.
      replace (b-1+1) with b by lia.
      rewrite (nodes_last Ews s vs 0 b) by lia.
      rewrite (tokens_split s 0 b (b+1)) by lia.
      rewrite (tokens_one s b) by lia.
      rewrite (L.Znth_or_null_in s b) by lia.
      rewrite cur_node_pos by lia.
      entailer!.
    + Exists b (f+1) f.
      rewrite (nodes_first Ews s vs f (Zlength s)) by lia.
      rewrite (tokens_split s f (f+1) (Zlength s)) by lia.
      rewrite (tokens_one s f) by lia.
      rewrite (L.Znth_or_null_in s f) by lia.
      rewrite cur_node_pos by lia.
      entailer!.
  - unfold POSTCONDITION, abbreviate. simpl_ret_assert.
    entailer!.
Qed.

Lemma body_client: semax_body Vprog Gprog f_client client_spec.
Proof.
  start_function.
  forward.
  forward.
  forward.
  forward. forward. forward.
  forward_call (gv, v_list, ip, sh, contents, n).
  Intros vret. destruct vret as [s vs]. simpl fst in *; simpl snd in *.
  match goal with Hw: whole s vs |- _ =>
    assert (Hw' := Hw); destruct Hw as [Hlen [Hprev Hnext]] end.
  assert_PROP (forall i, 0 <= i < Zlength s -> isptr (Znth i s)) as Hp.
  { sep_apply (L.nodes_isptr Ews s vs 0 (Zlength s)). entailer!. }
  assert (Hat: at_node s 0).
  { destruct s; [left; auto | right; rewrite Zlength_cons; list_solve]. }
  assert (Hpl: prev_links s vs 0 (Z.min (0+1) (Zlength s)))
    by (apply (L.prev_links_sub s vs 0 (Zlength s)); auto; lia).
  assert (Hpn0: is_pointer_or_null (Znth_or_null s 0)).
  { apply (L.Znth_or_null_pn s 0 0 (Zlength s) Hp). lia. }
  forward.
  make_func_ptr _counting_cmp.
  assert_PROP (isptr (gv _counting_cmp)) as Hcp.
  { sep_apply (func_ptr'_isptr (cmp_spec Rc_client nullval) (gv _counting_cmp)). entailer!. }
  assert (Hcpn: gv _counting_cmp <> nullval)
    by (destruct (gv _counting_cmp); try contradiction; discriminate).
  change (func_ptr' (cmp_spec Rc_client nullval) (gv _counting_cmp))
    with (func_ptr' (cmp_spec Rc_client (gv _counting_cmp)) (gv _counting_cmp)).
  change (Rc_client gv nullval) with (Rc_client gv (gv _counting_cmp)).
  replace (Vlong (Int64.repr (Int.signed (Int.repr 0)))) with nullval by reflexivity.
  assert (Hcpay: cmp_payloads (gv _counting_cmp) vs 0 (Zlength s)) by (right; auto).
  forward_call (gv, Tsh, v_it, Ews, s, vs, 0, gv _counting_cmp, v_key, Tsh,
                (Vint (Int.repr (Znth 0 contents)), (nullval, nullval))).
  { unfold cmp_env, cmp_state. rewrite !if_false by auto. entailer!.
    eexists; reflexivity. }
  Intros vret. destruct vret as [[b0 f0] r0]. simpl fst in *; simpl snd in *.
  match goal with Hi: init_window _ s b0 f0 r0 |- _ =>
    destruct Hi as [Hbf [Hfl [Hr [Hrn _]]]] end.
  forward.
  forward_loop
   (EX b: Z, EX f: Z, EX c: Z, EX fnd: int,
    PROP (-1 <= b < f; f <= Zlength s;
          (c = -1 /\ b = -1 /\ f = Zlength s) \/ (0 <= c < Zlength s))
    LOCAL (temp _l (Znth_or_null s c); temp _found (Vint fnd);
           lvar _it t_it v_it; lvar _key t_dl v_key; lvar _list (tptr t_dl) v_list;
           gvars gv)
    SEP (it_rep Tsh v_it s b f (gv _counting_cmp) v_key;
         cmp_env Rc_client (gv _counting_cmp) v_key Tsh
           (Vint (Int.repr (Znth 0 contents)), (nullval, nullval));
         cmp_state Rc_client gv (gv _counting_cmp);
         mem_mgr gv; data_at Tsh (tptr t_dl) (Znth_or_null s 0) v_list;
         nodes Ews s vs 0 (Zlength s); tokens s 0 (Zlength s);
         data_at sh (tarray tint (Zlength contents))
           (map Vint (map Int.repr contents)) ip))%assert
  continue:
   (EX b: Z, EX f: Z, EX fnd: int,
    PROP (-1 <= b < f; f <= Zlength s)
    LOCAL (temp _found (Vint fnd);
           lvar _it t_it v_it; lvar _key t_dl v_key; lvar _list (tptr t_dl) v_list;
           gvars gv)
    SEP (it_rep Tsh v_it s b f (gv _counting_cmp) v_key;
         cmp_env Rc_client (gv _counting_cmp) v_key Tsh
           (Vint (Int.repr (Znth 0 contents)), (nullval, nullval));
         cmp_state Rc_client gv (gv _counting_cmp);
         mem_mgr gv; data_at Tsh (tptr t_dl) (Znth_or_null s 0) v_list;
         nodes Ews s vs 0 (Zlength s); tokens s 0 (Zlength s);
         data_at sh (tarray tint (Zlength contents))
           (map Vint (map Int.repr contents)) ip))%assert
  break:
   (EX fnd: int,
    PROP ()
    LOCAL (temp _found (Vint fnd);
           lvar _it t_it v_it; lvar _key t_dl v_key; lvar _list (tptr t_dl) v_list;
           gvars gv)
    SEP (it_rep Tsh v_it s (-1) (Zlength s) (gv _counting_cmp) v_key;
         cmp_env Rc_client (gv _counting_cmp) v_key Tsh
           (Vint (Int.repr (Znth 0 contents)), (nullval, nullval));
         cmp_state Rc_client gv (gv _counting_cmp);
         mem_mgr gv; data_at Tsh (tptr t_dl) (Znth_or_null s 0) v_list;
         nodes Ews s vs 0 (Zlength s); tokens s 0 (Zlength s);
         data_at sh (tarray tint (Zlength contents))
           (map Vint (map Int.repr contents)) ip))%assert.
  - destruct Hr as [-> | [c [Hc ->]]].
    + destruct (Hrn eq_refl) as [-> ->].
      Exists (-1) (Zlength s) (-1) (Int.repr 0).
      rewrite (L.Znth_or_null_out s (-1)) by lia.
      entailer!.
    + Exists b0 f0 c (Int.repr 0).
      rewrite (L.Znth_or_null_in s c) by lia.
      entailer!.
  - Intros b f c fnd.
    match goal with Hd: (c = -1 /\ _) \/ _ |- _ =>
      destruct Hd as [[-> [-> ->]] | Hc] end.
    + rewrite (L.Znth_or_null_out s (-1)) by lia.
      forward_if.
      { discriminate. }
      forward.
      Exists fnd. entailer!.
    + assert (Hpc := Hp c Hc).
      rewrite (L.Znth_or_null_in s c) by lia.
      rewrite (L.nodes_focus Ews s vs 0 c (Zlength s)) by lia. Intros.
      forward_if.
      2:{ match goal with Hn: Znth c s = nullval |- _ => rewrite Hn in Hpc; contradiction end. }
      forward.
      Exists b f (Int.add fnd (Int.repr 1)).
      rewrite (L.nodes_focus Ews s vs 0 c (Zlength s)) by lia.
      entailer!.
  - Intros b f fnd.
    rewrite (L.nodes_split Ews s vs 0 (b+1) (Zlength s)) by lia.
    rewrite (L.nodes_split Ews s vs (b+1) f (Zlength s)) by lia.
    assert (prev_links s vs 0 (b+1))
      by (apply (L.prev_links_sub s vs 0 (Zlength s)); auto; lia).
    assert (next_links s vs f (Zlength s))
      by (apply (L.next_links_sub s vs 0 (Zlength s)); auto; lia).
    assert (cmp_payloads (gv _counting_cmp) vs 0 (b+1))
      by (apply (L.cmp_payloads_sub _ vs 0 (Zlength s)); auto; lia).
    assert (cmp_payloads (gv _counting_cmp) vs f (Zlength s))
      by (apply (L.cmp_payloads_sub _ vs 0 (Zlength s)); auto; lia).
    forward_call (gv, Tsh, v_it, Ews, s, vs, b, f, gv _counting_cmp, v_key, Tsh,
                  (Vint (Int.repr (Znth 0 contents)), (nullval, nullval))).
    { cancel. }
    Intros vret. destruct vret as [[b2 f2] r2]. simpl fst in *; simpl snd in *.
    forward.
    match goal with Hi: iter_step _ s b f b2 f2 r2 |- _ =>
      destruct Hi as [[Hb2 [Hf2 [Hr2 Hrn2]]] _] end.
    rewrite (L.nodes_split Ews s vs 0 (b+1) (Zlength s)) by lia.
    rewrite (L.nodes_split Ews s vs (b+1) f (Zlength s)) by lia.
    destruct Hr2 as [-> | [c [Hc2 [_ ->]]]].
    + destruct (Hrn2 eq_refl) as [-> ->].
      Exists (-1) (Zlength s) (-1) fnd.
      rewrite (L.Znth_or_null_out s (-1)) by lia.
      entailer!.
    + Exists b2 f2 c fnd.
      rewrite (L.Znth_or_null_in s c) by lia.
      entailer!.
  - Intros fnd.
    forward.
    forward_call (gv, s, vs).
    unfold cmp_state. rewrite if_false by auto. unfold Rc_client. Intros k.
    forward.
    forward.
    Exists (Int.add fnd k).
    unfold cmp_env. rewrite if_false by auto. Intros.
    unfold it_rep. Intros cur.
    sep_apply func_ptr'_emp.
    unfold Rc_client. Exists k.
    entailer!.
Qed.

Lemma body_main: semax_body Vprog Gprog f_main main_spec.
Proof.
  start_function.
  sep_apply (create_mem_mgr gv).
  forward_call (gv, gv _input, Ews, [6;7;3;4;7], 5).
  { unfold Rc_client. Exists (Int.repr 0). cancel. }
  { change (Zlength [6;7;3;4;7]) with 5. rep_lia. }
  unfold Rc_client. Intros k.
  forward.
  Exists k. entailer!.
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
  semax_func_cons body_counting_cmp.
  semax_func_cons body_client.
  semax_func_cons body_main.
Qed.

Lemma Gprog_lib: forall i, In i [_sglib_dllist_add; _sglib_dllist_get_first;
  _sglib_dllist_get_last; _sglib_dllist_it_init_on_equal; _sglib_dllist_it_init;
  _sglib_dllist_it_next] ->
  initial_world.find_id i Gprog =
  initial_world.find_id i (SglibVST.spec_client9.Gprog Rc_client).
Proof.
  intros i H. simpl in H.
  repeat (destruct H as [<-|H]; [reflexivity|]). contradiction.
Qed.

Print Assumptions prog_correct.
