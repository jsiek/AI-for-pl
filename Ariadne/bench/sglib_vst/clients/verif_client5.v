Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import SglibVST.client5 SglibVST.spec_client5.
Require SglibVST.lib_client5.
Import SglibVST.lib_client5.

Local Open Scope logic.

(* This program uses no comparator. *)
Definition Rc_client : globals -> val -> mpred := fun _ _ => emp.

(* ================================================================== *)
(* Malloc tokens of nodes lo .. hi-1                                  *)
(* ================================================================== *)

Fixpoint toksN (s: list val) (lo: Z) (n: nat) : mpred :=
  match n with
  | O => emp
  | S n' => malloc_token Ews t_dl (Znth lo s) * toksN s (lo+1) n'
  end.

Definition toks (s: list val) (lo hi: Z) : mpred :=
  toksN s lo (Z.to_nat (hi - lo)).
Arguments toks : simpl never.

Lemma toksN_split: forall s a b lo,
  toksN s lo (a+b)%nat = toksN s lo a * toksN s (lo + Z.of_nat a) b.
Proof.
  induction a; intros; simpl.
  - rewrite emp_sepcon. f_equal. lia.
  - rewrite IHa. rewrite sepcon_assoc.
    replace (lo + 1 + Z.of_nat a) with (lo + Z.of_nat (S a)) by lia.
    reflexivity.
Qed.

Lemma toks_split: forall s lo m hi, lo <= m <= hi ->
  toks s lo hi = toks s lo m * toks s m hi.
Proof.
  intros. unfold toks.
  replace (Z.to_nat (hi-lo)) with (Z.to_nat (m-lo) + Z.to_nat (hi-m))%nat by lia.
  rewrite toksN_split. f_equal. f_equal. lia.
Qed.

Lemma toks_empty: forall s lo hi, hi <= lo -> toks s lo hi = emp.
Proof.
  intros. unfold toks. replace (Z.to_nat (hi-lo)) with O by lia. reflexivity.
Qed.

Lemma toks_one: forall s i,
  toks s i (i+1) = malloc_token Ews t_dl (Znth i s).
Proof.
  intros. unfold toks. replace (Z.to_nat (i+1-i)) with 1%nat by lia.
  simpl. apply sepcon_emp.
Qed.

Lemma toks_focus: forall s lo i hi, lo <= i < hi ->
  toks s lo hi =
  toks s lo i * malloc_token Ews t_dl (Znth i s) * toks s (i+1) hi.
Proof.
  intros. rewrite (toks_split s lo i hi) by lia.
  rewrite (toks_split s i (i+1) hi) by lia.
  rewrite toks_one. rewrite sepcon_assoc. reflexivity.
Qed.

Lemma toksN_cons: forall x s n lo, 1 <= lo ->
  toksN (x::s) lo n = toksN s (lo-1) n.
Proof.
  induction n; intros; simpl; auto.
  rewrite Znth_pos_cons by lia. f_equal.
  rewrite IHn by lia. f_equal. lia.
Qed.

Lemma ins0: forall {A} {d: Inhabitant A} (e: A) s, ins 0 e s = e :: s.
Proof. intros. unfold ins. list_solve. Qed.

Lemma toks_ins0: forall e s,
  toks (ins 0 e s) 0 (Zlength s + 1) =
  malloc_token Ews t_dl e * toks s 0 (Zlength s).
Proof.
  intros. rewrite ins0. unfold toks.
  replace (Zlength s + 1 - 0) with (Z.succ (Zlength s - 0)) by lia.
  rewrite Z2Nat.inj_succ by (pose proof (Zlength_nonneg s); lia).
  simpl toksN. rewrite Znth_0_cons. f_equal.
  rewrite toksN_cons by lia. reflexivity.
Qed.

(* ================================================================== *)
(* Pure helpers                                                       *)
(* ================================================================== *)

Lemma whole_nil: whole [] [].
Proof.
  split; auto. split; intros i Hi; rewrite Zlength_nil in Hi; lia.
Qed.

Lemma int_payloads_ins0: forall ev vs vs',
  int_val ev -> int_payloads vs 0 (Zlength vs) ->
  Zlength vs' = Zlength vs + 1 ->
  map pay vs' = ins 0 ev (map pay vs) ->
  int_payloads vs' 0 (Zlength vs + 1).
Proof.
  intros ev vs vs' Hev Hvs Hl Hm. rewrite ins0 in Hm.
  intros i Hi.
  replace (pay (Znth i vs')) with (Znth i (map pay vs'))
    by (rewrite Znth_map by lia; auto).
  rewrite Hm. destruct (zeq i 0).
  - subst. rewrite Znth_0_cons. auto.
  - rewrite Znth_pos_cons by lia. rewrite Znth_map by lia. apply Hvs; lia.
Qed.

Lemma cmp_env_null: forall Rc eqp sh v, cmp_env Rc nullval eqp sh v = emp.
Proof. intros. unfold cmp_env. destruct (Val.eq nullval nullval); [auto|congruence]. Qed.

Lemma cmp_state_null: forall Rc gv, cmp_state Rc gv nullval = emp.
Proof. intros. unfold cmp_state. destruct (Val.eq nullval nullval); [auto|congruence]. Qed.

Lemma it_rep_data_at_: forall sh it s b f scp eqp,
  it_rep sh it s b f scp eqp |-- data_at_ sh t_it it.
Proof.
  intros. unfold it_rep. Intros cur. apply data_at_data_at_.
Qed.

Lemma Zlength_ins0: forall {A} {d: Inhabitant A} (e: A) s,
  Zlength (ins 0 e s) = Zlength s + 1.
Proof. intros. rewrite ins0, Zlength_cons. lia. Qed.

(* ================================================================== *)
(* Funspecs of the client's functions                                 *)
(* ================================================================== *)

Definition build_spec :=
 DECLARE _build
  WITH gv: globals, shl: share, lp: val, sh: share, ip: val,
       il: list int, n: Z
  PRE [ tptr (tptr t_dl), tptr tint, tint ]
    PROP (writable_share shl; readable_share sh; Zlength il = n;
          0 <= n <= Int.max_signed)
    PARAMS (lp; ip; Vint (Int.repr n)) GLOBALS (gv)
    SEP (mem_mgr gv; data_at shl (tptr t_dl) nullval lp;
         data_at sh (tarray tint n) (map Vint il) ip)
  POST [ tint ]
    EX m: Z, EX s: list val, EX vs: list node_v,
    PROP (0 <= m <= n; Zlength s = m; whole s vs; int_payloads vs 0 m)
    RETURN (Vint (Int.repr m))
    SEP (mem_mgr gv; data_at shl (tptr t_dl) (Znth_or_null s 0) lp;
         data_at sh (tarray tint n) (map Vint il) ip;
         nodes Ews s vs 0 m; toks s 0 m).

Definition free_all_spec :=
 DECLARE _free_all
  WITH gv: globals, s: list val, vs: list node_v, j: Z
  PRE [ tptr t_dl ]
    PROP (whole s vs; at_node s j)
    PARAMS (Znth_or_null s j) GLOBALS (gv)
    SEP (mem_mgr gv; nodes Ews s vs 0 (Zlength s); toks s 0 (Zlength s))
  POST [ tvoid ]
    PROP () RETURN () SEP (mem_mgr gv).

Definition client_spec :=
 DECLARE _client
  WITH gv: globals, sh: share, ip: val, il: list int, n: Z
  PRE [ tptr tint, tint ]
    PROP (readable_share sh; Zlength il = n; 0 <= n <= Int.max_signed)
    PARAMS (ip; Vint (Int.repr n)) GLOBALS (gv)
    SEP (mem_mgr gv; data_at sh (tarray tint n) (map Vint il) ip)
  POST [ tuint ]
    EX r: int,
    PROP () RETURN (Vint r)
    SEP (mem_mgr gv; data_at sh (tarray tint n) (map Vint il) ip).

Definition input_vals : list int := map Int.repr [6; 7; 3; 4; 7].

Definition main_spec :=
 DECLARE _main
  WITH gv: globals
  PRE [ ] main_pre prog tt gv
  POST [ tint ]
    PROP () RETURN (Vint (Int.repr 0))
    SEP (mem_mgr gv; data_at Ews (tarray tint 5) (map Vint input_vals) (gv _input);
         has_ext tt).

Definition Gprog : funspecs :=
  SglibVST.spec_client5.Gprog Rc_client ++
  [build_spec; free_all_spec; client_spec; main_spec].

#[export] Existing Instance NullExtension.Espec.

(* ================================================================== *)
(* Library functions: from lib_client5                                *)
(* ================================================================== *)

Lemma Gprog_sub: forall f,
  tycontext_sub (func_tycontext f Vprog (SglibVST.spec_client5.Gprog Rc_client) nil)
                (func_tycontext f Vprog Gprog nil).
Proof.
  intros. unfold Gprog. apply tycontext_sub_Gprog_app1.
  - apply compute_list_norepet_e. reflexivity.
  - apply compute_list_norepet_e. reflexivity.
Qed.

Lemma body_add': semax_body Vprog Gprog f_sglib_dllist_add add_spec.
Proof.
  eapply semax_body_subsumption. apply (SglibVST.lib_client5.body_add Rc_client).
  apply Gprog_sub.
Qed.

Lemma body_get_first': semax_body Vprog Gprog f_sglib_dllist_get_first get_first_spec.
Proof.
  eapply semax_body_subsumption. apply (SglibVST.lib_client5.body_get_first Rc_client).
  apply Gprog_sub.
Qed.

Lemma body_get_last': semax_body Vprog Gprog f_sglib_dllist_get_last get_last_spec.
Proof.
  eapply semax_body_subsumption. apply (SglibVST.lib_client5.body_get_last Rc_client).
  apply Gprog_sub.
Qed.

Lemma body_it_init_on_equal': semax_body Vprog Gprog
  f_sglib_dllist_it_init_on_equal (it_init_on_equal_spec Rc_client).
Proof.
  eapply semax_body_subsumption.
  apply (SglibVST.lib_client5.body_it_init_on_equal Rc_client).
  apply Gprog_sub.
Qed.

Lemma body_it_init': semax_body Vprog Gprog f_sglib_dllist_it_init it_init_spec.
Proof.
  eapply semax_body_subsumption. apply (SglibVST.lib_client5.body_it_init Rc_client).
  apply Gprog_sub.
Qed.

Lemma body_it_next': semax_body Vprog Gprog f_sglib_dllist_it_next (it_next_spec Rc_client).
Proof.
  eapply semax_body_subsumption. apply (SglibVST.lib_client5.body_it_next Rc_client).
  apply Gprog_sub.
Qed.

(* BUILD *)
Lemma body_build: semax_body Vprog Gprog f_build build_spec.
Proof.
  start_function.
  forward.
  forward_loop
    (EX k: Z, EX s: list val, EX vs: list node_v,
     PROP (0 <= k <= n; Zlength s = k; whole s vs; int_payloads vs 0 k)
     LOCAL (temp _m (Vint (Int.repr k)); temp _k (Vint (Int.repr k));
            temp _list lp; temp _input__1 ip; temp _n (Vint (Int.repr n));
            gvars gv)
     SEP (mem_mgr gv; data_at shl (tptr t_dl) (Znth_or_null s 0) lp;
          data_at sh (tarray tint n) (map Vint il) ip;
          nodes Ews s vs 0 k; toks s 0 k))
  continue:
    (EX k: Z, EX s: list val, EX vs: list node_v,
     PROP (0 <= k < n; Zlength s = (k+1)%Z; whole s vs; int_payloads vs 0 (k+1))
     LOCAL (temp _m (Vint (Int.repr (k+1))); temp _k (Vint (Int.repr k));
            temp _list lp; temp _input__1 ip; temp _n (Vint (Int.repr n));
            gvars gv)
     SEP (mem_mgr gv; data_at shl (tptr t_dl) (Znth_or_null s 0) lp;
          data_at sh (tarray tint n) (map Vint il) ip;
          nodes Ews s vs 0 (k+1); toks s 0 (k+1)))
  break:
    (EX k: Z, EX s: list val, EX vs: list node_v,
     PROP (0 <= k <= n; Zlength s = k; whole s vs; int_payloads vs 0 k)
     LOCAL (temp _m (Vint (Int.repr k)); gvars gv)
     SEP (mem_mgr gv; data_at shl (tptr t_dl) (Znth_or_null s 0) lp;
          data_at sh (tarray tint n) (map Vint il) ip;
          nodes Ews s vs 0 k; toks s 0 k)).
  - forward. Exists 0 (@nil val) (@nil node_v).
    rewrite Znth_or_null_out by (rewrite Zlength_nil; lia).
    rewrite nodes_empty, toks_empty by lia. entailer!.
    split; [apply whole_nil| intros i Hi; lia].
  - Intros k s vs.
    forward_if
     (PROP (k < n)
      LOCAL (temp _m (Vint (Int.repr k)); temp _k (Vint (Int.repr k));
             temp _list lp; temp _input__1 ip; temp _n (Vint (Int.repr n));
             gvars gv)
      SEP (mem_mgr gv; data_at shl (tptr t_dl) (Znth_or_null s 0) lp;
           data_at sh (tarray tint n) (map Vint il) ip;
           nodes Ews s vs 0 k; toks s 0 k)).
    + forward. entailer!.
    + forward. Exists k s vs. entailer!.
    + Intros.
      forward_call (t_dl, gv).
      Intros l.
      forward_if
        (PROP (l <> nullval)
         LOCAL (temp _l l; temp _m (Vint (Int.repr k)); temp _k (Vint (Int.repr k));
                temp _list lp; temp _input__1 ip; temp _n (Vint (Int.repr n));
                gvars gv)
         SEP (mem_mgr gv; malloc_token Ews t_dl l; data_at_ Ews t_dl l;
              data_at shl (tptr t_dl) (Znth_or_null s 0) lp;
              data_at sh (tarray tint n) (map Vint il) ip;
              nodes Ews s vs 0 k; toks s 0 k)).
      * if_tac; entailer!.
      * subst l. rewrite if_true by auto.
        forward. Exists k s vs. entailer!.
      * rewrite if_false by auto. forward. entailer!.
      * Intros.
        forward.
        forward.
        assert (Hk: Znth k (map Vint il) = Vint (Znth k il)) by (rewrite Znth_map by lia; auto).
        try rewrite Hk.
        destruct H3 as [Hl1 [Hp1 Hn1]].
        subst k.
        forward_call (shl, lp, Ews, l, Vint (Znth (Zlength s) il), snd (default_val t_dl), s, vs, 0).
        { split; [|split3; auto].
          destruct s; [left; auto | right; rewrite Zlength_cons; rep_lia]. }
        Intros vs'.
        match goal with Hw: whole (ins 0 l s) vs', Hm: map pay vs' = _ |- _ =>
          rename Hw into Hw'; rename Hm into Hm' end.
        forward.
        assert (Hlv: Zlength vs' = Zlength s + 1)
          by (destruct Hw' as [Hw _]; rewrite Hw, Zlength_ins0; lia).
        assert (Hip: int_payloads vs' 0 (Zlength s + 1)).
        { rewrite <- Hl1. apply int_payloads_ins0 with (ev := Vint (Znth (Zlength s) il));
            auto; try lia.
          exists (Znth (Zlength s) il); auto. rewrite Hl1; auto. }
        assert (Hz: Znth_or_null (ins 0 l s) 0 = l).
        { rewrite ins0. rewrite Znth_or_null_in by (rewrite Zlength_cons; rep_lia).
          apply Znth_0_cons. }
        Exists (Zlength s) (ins 0 l s) vs'.
        rewrite Zlength_ins0. rewrite toks_ins0. rewrite Hz.
        entailer!.
  - Intros k s vs.
    forward.
    Exists (Z.add k 1). Exists s vs. entailer!.
  - Intros k s vs.
    forward.
    Exists (Zlength s) s vs. entailer!.
Qed.

(* FREE_ALL *)
Definition cur_node (s: list val) (vs: list node_v) (c: Z) (r: val) : mpred :=
  if Val.eq r nullval then emp
  else data_at Ews t_dl (Znth c vs) r * malloc_token Ews t_dl r.

Lemma body_free_all: semax_body Vprog Gprog f_free_all free_all_spec.
Proof.
  start_function.
  destruct H as [Hl [Hp Hn]]. rename H0 into Hat.
  assert (Hj: (s = [] /\ j = 0) \/ 0 <= j < Zlength s) by exact Hat.
  forward_call (Tsh, v_it, Ews, s, vs, j).
  { split.
    - apply (prev_links_sub s vs 0 (Zlength s)); auto; lia.
    - apply (next_links_sub s vs 0 (Zlength s)); auto; destruct Hj as [[-> ->]|]; simpl; lia. }
  Intros vret. destruct vret as [[b f] r]. simpl fst in *. simpl snd in *.
  rename H into Hiw.
  forward_loop
    (EX b: Z, EX f: Z, EX c: Z, EX r: val,
     PROP (-1 <= b < f; f <= Zlength s;
           (r = nullval /\ b = -1 /\ f = Zlength s) \/
           (b < c < f /\ 0 <= c < Zlength s /\ r = Znth c s /\ isptr r))
     LOCAL (temp _l r; lvar _it t_it v_it; gvars gv)
     SEP (mem_mgr gv; it_rep Tsh v_it s b f nullval nullval;
          nodes Ews s vs 0 (b+1); toks s 0 (b+1);
          nodes Ews s vs f (Zlength s); toks s f (Zlength s);
          cur_node s vs c r))
  continue:
    (EX b: Z, EX f: Z,
     PROP (-1 <= b < f; f <= Zlength s)
     LOCAL (lvar _it t_it v_it; gvars gv)
     SEP (mem_mgr gv; it_rep Tsh v_it s b f nullval nullval;
          nodes Ews s vs 0 (b+1); toks s 0 (b+1);
          nodes Ews s vs f (Zlength s); toks s f (Zlength s)))
  break:
    (PROP ()
     LOCAL (lvar _it t_it v_it; gvars gv)
     SEP (mem_mgr gv; data_at_ Tsh t_it v_it)).
  - destruct Hiw as [Hb [Hf [_ [_ Hex]]]].
    destruct (Hex eq_refl) as [[-> [-> [-> ->]]] | [c [Hc [-> [-> ->]]]]].
    + Exists (-1) 0 0 nullval.
      unfold cur_node. rewrite if_true by auto.
      rewrite !nodes_empty, !toks_empty by (rewrite ?Zlength_nil; lia).
      entailer!.
    + assert_PROP (isptr (Znth c s)).
      { rewrite (nodes_focus Ews s vs 0 c (Zlength s)) by lia. entailer!. }
      Exists (c-1) (c+1) c (Znth c s).
      unfold cur_node. rewrite if_false by (intro Hx; rewrite Hx in H; contradiction).
      rewrite (nodes_focus Ews s vs 0 c (Zlength s)) by lia.
      rewrite (toks_focus s 0 c (Zlength s)) by lia.
      replace (c-1+1) with c by lia.
      entailer!. right; repeat split; auto; lia.
  - Intros b0 f0 c r0.
    destruct H1 as [[-> [-> ->]] | [Hc [Hc' [-> Hp0]]]].
    + unfold cur_node. rewrite if_true by auto.
      forward_if.
      { first [discriminate | contradiction | congruence]. }
      forward.
      rewrite !nodes_empty, !toks_empty by lia.
      sep_apply it_rep_data_at_. entailer!.
    + unfold cur_node. rewrite if_false by (intro Hx; rewrite Hx in Hp0; contradiction).
      forward_if.
      * forward_call (t_dl, Znth c s, gv).
        { rewrite if_false by (intro Hx; rewrite Hx in Hp0; contradiction). cancel. }
        Exists b0 f0. entailer!.
      * destruct (Znth c s); try contradiction; discriminate.
  - Intros b0 f0.
    forward_call (gv, Tsh, v_it, Ews, s, vs, b0, f0, nullval, nullval, Ews,
                  (Vundef, (Vundef, Vundef))).
    { rewrite cmp_env_null, cmp_state_null. cancel. }
    { split; [apply (prev_links_sub s vs 0 (Zlength s)); auto; lia|].
      split; [apply (next_links_sub s vs 0 (Zlength s)); auto; lia|].
      split; left; auto. }
    Intros vret. destruct vret as [[b' f'] r']. simpl fst in *. simpl snd in *.
    rewrite cmp_env_null, cmp_state_null.
    rename H1 into Hst.
    destruct Hst as [Hany Hex]. specialize (Hex eq_refl).
    forward.
    destruct Hex as [[-> [-> [-> [-> ->]]]] | [[Hb [-> [-> ->]]] | [Hf [-> [-> ->]]]]].
    + Exists (-1) (Zlength s) 0 nullval.
      unfold cur_node. rewrite if_true by auto. entailer!.
    + assert_PROP (isptr (Znth b0 s)).
      { rewrite (nodes_focus Ews s vs 0 b0 (b0+1)) by lia. entailer!. }
      Exists (b0-1) f0 b0 (Znth b0 s).
      unfold cur_node. rewrite if_false by (intro Hx; rewrite Hx in H1; contradiction).
      rewrite (nodes_split Ews s vs 0 b0 (b0+1)) by lia.
      rewrite (toks_split s 0 b0 (b0+1)) by lia.
      rewrite nodes_one, toks_one.
      replace (b0-1+1) with b0 by lia.
      entailer!. right; repeat split; auto; lia.
    + assert_PROP (isptr (Znth f0 s)).
      { rewrite (nodes_focus Ews s vs f0 f0 (Zlength s)) by lia. entailer!. }
      Exists b0 (f0+1) f0 (Znth f0 s).
      unfold cur_node. rewrite if_false by (intro Hx; rewrite Hx in H1; contradiction).
      rewrite (nodes_split Ews s vs f0 (f0+1) (Zlength s)) by lia.
      rewrite (toks_split s f0 (f0+1) (Zlength s)) by lia.
      rewrite nodes_one, toks_one.
      entailer!. right; repeat split; auto; lia.
  - unfold POSTCONDITION, abbreviate. simpl_ret_assert. entailer!.
Qed.

Ltac pre_tac s vs :=
  repeat match goal with
  | |- _ /\ _ => split
  | |- at_node _ _ => right; lia
  | |- prev_links _ _ _ _ => apply (prev_links_sub s vs 0 (Zlength s)); auto; lia
  | |- next_links _ _ _ _ => apply (next_links_sub s vs 0 (Zlength s)); auto; lia
  | |- _ => solve [auto]
  end.

(* CLIENT *)
Lemma body_client: semax_body Vprog Gprog f_client client_spec.
Proof.
  start_function.
  forward.
  forward.
  forward.
  forward_call (gv, Tsh, v_list, sh, ip, il, n).
  Intros vret. destruct vret as [[m s] vs]. simpl fst in *. simpl snd in *.
  match goal with
  | H1: 0 <= m <= n, H2: Zlength s = m, H3: whole s vs, H4: int_payloads vs 0 m |- _ =>
      rename H1 into Hmn; rename H2 into Hsm; rename H3 into Hw; rename H4 into Hip
  end.
  subst m.
  pose proof Hw as [Hl [Hp Hn]].
  assert_PROP (forall i, 0 <= i < Zlength s -> isptr (Znth i s)) as Hptr.
  { sep_apply nodes_isptr. entailer!. }
  forward_if
    (PROP (Zlength s <> 0)
     LOCAL (temp _cnt (Vint (Int.repr (Zlength s))); temp _k (Vint (Int.repr 0));
            temp _sum (Vint (Int.repr 0));
            lvar _list (tptr (Tstruct _dllist noattr)) v_list; lvar _it t_it v_it; gvars gv)
     SEP (mem_mgr gv; data_at Tsh (tptr t_dl) (Znth_or_null s 0) v_list;
          data_at_ Tsh t_it v_it;
          data_at sh (tarray tint n) (map Vint il) ip;
          nodes Ews s vs 0 (Zlength s); toks s 0 (Zlength s))).
  { match goal with Hx: Zlength s = 0 |- _ => rename Hx into Hz end.
    apply Zlength_nil_inv in Hz. subst s.
    rewrite Znth_or_null_out by (rewrite Zlength_nil; lia).
    rewrite nodes_empty, toks_empty by (rewrite Zlength_nil; lia).
    forward. Exists (Int.repr 0). entailer!. }
  { forward. entailer!. }
  Intros.
  assert (Hp0: isptr (Znth_or_null s 0))
    by (rewrite Znth_or_null_in by (pose proof (Zlength_nonneg s); lia);
        apply Hptr; pose proof (Zlength_nonneg s); lia).
  forward.
  forward.
  assert (Hat0: at_node s 0) by (right; pose proof (Zlength_nonneg s); lia).
  forward_call (Tsh, v_it, Ews, s, vs, 0).
  { apply (prev_links_sub s vs 0 (Zlength s)); auto; lia. }
  Intros vret. destruct vret as [[b f] r]. simpl fst in *. simpl snd in *.
  match goal with Hx: init_window nullval s b f r |- _ => rename Hx into Hiw end.
  forward.
  (* ---------------- loop 1: find the middle node ---------------- *)
  forward_loop
    (EX b: Z, EX f: Z, EX c: Z, EX r: val, EX k: Z, EX jm: Z,
     PROP (-1 <= b < f; f <= Zlength s; 0 <= jm < Zlength s; 0 <= k;
           (r = nullval /\ b = -1 /\ f = Zlength s) \/
           (b < c < f /\ 0 <= c < Zlength s /\ r = Znth c s /\ k <= f - b - 2))
     LOCAL (temp _l r; temp _k (Vint (Int.repr k)); temp _mid (Znth_or_null s jm);
            temp _cnt (Vint (Int.repr (Zlength s))); temp _sum (Vint (Int.repr 0));
            lvar _list (tptr (Tstruct _dllist noattr)) v_list; lvar _it t_it v_it; gvars gv)
     SEP (mem_mgr gv; data_at Tsh (tptr t_dl) (Znth_or_null s 0) v_list;
          it_rep Tsh v_it s b f nullval nullval;
          data_at sh (tarray tint n) (map Vint il) ip;
          nodes Ews s vs 0 (Zlength s); toks s 0 (Zlength s)))
  continue:
    (EX b: Z, EX f: Z, EX k: Z, EX jm: Z,
     PROP (-1 <= b < f; f <= Zlength s; 0 <= jm < Zlength s; 1 <= k <= f - b - 1)
     LOCAL (temp _k (Vint (Int.repr k)); temp _mid (Znth_or_null s jm);
            temp _cnt (Vint (Int.repr (Zlength s))); temp _sum (Vint (Int.repr 0));
            lvar _list (tptr (Tstruct _dllist noattr)) v_list; lvar _it t_it v_it; gvars gv)
     SEP (mem_mgr gv; data_at Tsh (tptr t_dl) (Znth_or_null s 0) v_list;
          it_rep Tsh v_it s b f nullval nullval;
          data_at sh (tarray tint n) (map Vint il) ip;
          nodes Ews s vs 0 (Zlength s); toks s 0 (Zlength s)))
  break:
    (EX jm: Z,
     PROP (0 <= jm < Zlength s)
     LOCAL (temp _mid (Znth_or_null s jm); temp _sum (Vint (Int.repr 0));
            lvar _list (tptr (Tstruct _dllist noattr)) v_list; lvar _it t_it v_it; gvars gv)
     SEP (mem_mgr gv; data_at Tsh (tptr t_dl) (Znth_or_null s 0) v_list;
          data_at_ Tsh t_it v_it;
          data_at sh (tarray tint n) (map Vint il) ip;
          nodes Ews s vs 0 (Zlength s); toks s 0 (Zlength s))).
  - destruct Hiw as [Hb [Hf [_ [_ Hex]]]].
    destruct (Hex eq_refl) as [[_ [Hs _]] | [c [Hc [-> [-> ->]]]]].
    { subst s. rewrite Zlength_nil in *. lia. }
    Exists (c-1) (c+1) c (Znth c s) 0 0.
    entailer!. right. repeat split; auto; lia.
  - Intros b0 f0 c r0 k jm.
    match goal with Hx: (r0 = nullval /\ _) \/ _ |- _ => rename Hx into Hd end.
    destruct Hd as [[-> [-> ->]] | [Hc [Hc' [-> Hk]]]].
    + forward_if.
      { first [discriminate | contradiction | congruence]. }
      forward. Exists jm.
      sep_apply it_rep_data_at_. entailer!.
    + forward_if.
      { rewrite (nodes_focus Ews s vs 0 c (Zlength s)) by lia. entailer!. }
      * forward_if
          (EX jm': Z,
           PROP (0 <= jm' < Zlength s)
           LOCAL (temp _l (Znth c s); temp _k (Vint (Int.repr k));
                  temp _mid (Znth_or_null s jm');
                  temp _cnt (Vint (Int.repr (Zlength s))); temp _sum (Vint (Int.repr 0));
                  lvar _list (tptr (Tstruct _dllist noattr)) v_list; lvar _it t_it v_it; gvars gv)
           SEP (mem_mgr gv; data_at Tsh (tptr t_dl) (Znth_or_null s 0) v_list;
                it_rep Tsh v_it s b0 f0 nullval nullval;
                data_at sh (tarray tint n) (map Vint il) ip;
                nodes Ews s vs 0 (Zlength s); toks s 0 (Zlength s))).
        -- apply prop_right. intros [_ Hm].
           apply (f_equal Int.signed) in Hm.
           rewrite Int.signed_repr in Hm by rep_lia.
           rewrite Int.signed_mone in Hm. lia.
        -- forward. Exists c. rewrite (Znth_or_null_in s c) by lia. entailer!.
        -- forward. Exists jm. entailer!.
        -- Intros jm'.
           forward.
           Exists b0 f0 (k+1) jm'. entailer!.
      * assert (isptr (Znth c s)) by (apply Hptr; lia).
        destruct (Znth c s); try contradiction; discriminate.
  - Intros b0 f0 k jm.
    rewrite (nodes_split Ews s vs 0 (b0+1) (Zlength s)) by lia.
    rewrite (nodes_split Ews s vs (b0+1) f0 (Zlength s)) by lia.
    forward_call (gv, Tsh, v_it, Ews, s, vs, b0, f0, nullval, nullval, Ews,
                  (Vundef, (Vundef, Vundef))).
    { rewrite cmp_env_null, cmp_state_null. cancel. }
    { split; [apply (prev_links_sub s vs 0 (Zlength s)); auto; lia|].
      split; [apply (next_links_sub s vs 0 (Zlength s)); auto; lia|].
      split; left; auto. }
    Intros vret. destruct vret as [[b' f'] r']. simpl fst in *. simpl snd in *.
    rewrite cmp_env_null, cmp_state_null.
    match goal with Hx: iter_step nullval s b0 f0 b' f' r' |- _ => rename Hx into Hst end.
    destruct Hst as [Hany Hex]. specialize (Hex eq_refl).
    forward.
    destruct Hex as [[-> [-> [-> [-> ->]]]] | [[Hb [-> [-> ->]]] | [Hf [-> [-> ->]]]]].
    + Exists (-1) (Zlength s) 0 nullval k jm.
      rewrite (nodes_split Ews s vs 0 (-1+1) (Zlength s)) by lia.
      rewrite (nodes_split Ews s vs (-1+1) (Zlength s) (Zlength s)) by lia.
      entailer!. rewrite (nodes_empty Ews s vs (Zlength s) (Zlength s)) by lia. auto.
    + Exists (b0-1) f0 b0 (Znth b0 s) k jm.
      rewrite (nodes_split Ews s vs 0 (b0+1) (Zlength s)) by lia.
      rewrite (nodes_split Ews s vs (b0+1) f0 (Zlength s)) by lia.
      entailer!. right; repeat split; auto; lia.
    + Exists b0 (f0+1) f0 (Znth f0 s) k jm.
      rewrite (nodes_split Ews s vs 0 (b0+1) (Zlength s)) by lia.
      rewrite (nodes_split Ews s vs (b0+1) f0 (Zlength s)) by lia.
      entailer!. right; repeat split; auto; lia.
  - (* after loop 1 *)
    Intros jm.
    (* ---------------- get_first and the forward walk ---------------- *)
    rewrite (nodes_split Ews s vs 0 (Z.min (jm+1) (Zlength s)) (Zlength s)) by lia.
    forward_call (Ews, s, vs, jm).
    { cancel. }
    { pre_tac s vs. }
    Intros r1.
    forward_loop
      (EX i: Z, EX sum: int,
       PROP (0 <= i <= Zlength s)
       LOCAL (temp _l (Znth_or_null s i); temp _sum (Vint sum);
              temp _mid (Znth_or_null s jm);
              lvar _list (tptr (Tstruct _dllist noattr)) v_list; lvar _it t_it v_it; gvars gv)
       SEP (mem_mgr gv; data_at Tsh (tptr t_dl) (Znth_or_null s 0) v_list;
            data_at_ Tsh t_it v_it;
            data_at sh (tarray tint n) (map Vint il) ip;
            nodes Ews s vs 0 (Zlength s); toks s 0 (Zlength s)))
    continue:
      (EX i: Z, EX sum: int,
       PROP (0 <= i < Zlength s)
       LOCAL (temp _l (Znth i s); temp _sum (Vint sum);
              temp _mid (Znth_or_null s jm);
              lvar _list (tptr (Tstruct _dllist noattr)) v_list; lvar _it t_it v_it; gvars gv)
       SEP (mem_mgr gv; data_at Tsh (tptr t_dl) (Znth_or_null s 0) v_list;
            data_at_ Tsh t_it v_it;
            data_at sh (tarray tint n) (map Vint il) ip;
            nodes Ews s vs 0 (Zlength s); toks s 0 (Zlength s)))
    break:
      (EX sum: int,
       PROP ()
       LOCAL (temp _sum (Vint sum); temp _mid (Znth_or_null s jm);
              lvar _list (tptr (Tstruct _dllist noattr)) v_list; lvar _it t_it v_it; gvars gv)
       SEP (mem_mgr gv; data_at Tsh (tptr t_dl) (Znth_or_null s 0) v_list;
            data_at_ Tsh t_it v_it;
            data_at sh (tarray tint n) (map Vint il) ip;
            nodes Ews s vs 0 (Zlength s); toks s 0 (Zlength s))).
    + match goal with Hx: r1 = nullval \/ In r1 s |- _ => rename Hx into Hr1 end.
      destruct Hr1 as [-> | Hin].
      * Exists (Zlength s) (Int.repr 0).
        rewrite (Znth_or_null_out s (Zlength s)) by lia.
        rewrite (nodes_split Ews s vs 0 (Z.min (jm+1) (Zlength s)) (Zlength s)) by lia.
        entailer!.
      * apply In_Znth in Hin. destruct Hin as [i [Hi <-]].
        Exists i (Int.repr 0).
        rewrite (Znth_or_null_in s i) by lia.
        rewrite (nodes_split Ews s vs 0 (Z.min (jm+1) (Zlength s)) (Zlength s)) by lia.
        entailer!.
    + Intros i sum.
      destruct (zeq i (Zlength s)).
      * subst i. rewrite (Znth_or_null_out s (Zlength s)) by lia.
        forward_if.
        { first [discriminate | contradiction | congruence]. }
        forward. Exists sum. entailer!.
      * rewrite (Znth_or_null_in s i) by lia.
        assert (Hpi: isptr (Znth i s)) by (apply Hptr; lia).
        forward_if.
        { rewrite (nodes_focus Ews s vs 0 i (Zlength s)) by lia. entailer!. }
        -- rewrite (nodes_focus Ews s vs 0 i (Zlength s)) by lia. Intros.
           assert (Hpay: int_val (pay (Znth i vs))) by (apply Hip; lia).
           destruct (Znth i vs) as [pi [ni qi]] eqn:Ei.
           destruct Hpay as [xi Hxi]. simpl in Hxi. subst pi.
           forward.
           forward.
           Exists i (Int.add sum xi).
           entailer!.
        -- destruct (Znth i s); try contradiction; discriminate.
    + Intros i sum.
      assert (Hni: nxt (Znth i vs) = Znth_or_null s (i+1)) by (apply Hn; lia).
      assert (Hpn: is_pointer_or_null (Znth_or_null s (i+1)))
        by (apply (Znth_or_null_pn s (i+1) 0 (Zlength s)); auto; lia).
      rewrite (nodes_focus Ews s vs 0 i (Zlength s)) by lia. Intros.
      destruct (Znth i vs) as [pi [ni qi]] eqn:Ei.
      unfold nxt in Hni; simpl in Hni. subst ni.
      forward.
      Exists (i+1) sum.
      entailer!.
      rewrite (nodes_focus Ews s vs 0 i (Zlength s)) by lia. rewrite Ei. cancel.
    + (* ---------------- get_last and the backward walk ---------------- *)
      Intros sum.
      rewrite (nodes_split Ews s vs 0 jm (Zlength s)) by lia.
      forward_call (Ews, s, vs, jm).
      { cancel. }
      { pre_tac s vs. }
      Intros r2.
      forward_loop
        (EX i: Z, EX sum: int,
         PROP (-1 <= i < Zlength s)
         LOCAL (temp _l (Znth_or_null s i); temp _sum (Vint sum);
                temp _mid (Znth_or_null s jm);
                lvar _list (tptr (Tstruct _dllist noattr)) v_list; lvar _it t_it v_it; gvars gv)
         SEP (mem_mgr gv; data_at Tsh (tptr t_dl) (Znth_or_null s 0) v_list;
              data_at_ Tsh t_it v_it;
              data_at sh (tarray tint n) (map Vint il) ip;
              nodes Ews s vs 0 (Zlength s); toks s 0 (Zlength s)))
      continue:
        (EX i: Z, EX sum: int,
         PROP (0 <= i < Zlength s)
         LOCAL (temp _l (Znth i s); temp _sum (Vint sum);
                temp _mid (Znth_or_null s jm);
                lvar _list (tptr (Tstruct _dllist noattr)) v_list; lvar _it t_it v_it; gvars gv)
         SEP (mem_mgr gv; data_at Tsh (tptr t_dl) (Znth_or_null s 0) v_list;
              data_at_ Tsh t_it v_it;
              data_at sh (tarray tint n) (map Vint il) ip;
              nodes Ews s vs 0 (Zlength s); toks s 0 (Zlength s)))
      break:
        (EX sum: int,
         PROP ()
         LOCAL (temp _sum (Vint sum); temp _mid (Znth_or_null s jm);
                lvar _list (tptr (Tstruct _dllist noattr)) v_list; lvar _it t_it v_it; gvars gv)
         SEP (mem_mgr gv; data_at Tsh (tptr t_dl) (Znth_or_null s 0) v_list;
              data_at_ Tsh t_it v_it;
              data_at sh (tarray tint n) (map Vint il) ip;
              nodes Ews s vs 0 (Zlength s); toks s 0 (Zlength s))).
      * match goal with Hx: r2 = nullval \/ In r2 s |- _ => rename Hx into Hr2 end.
        destruct Hr2 as [-> | Hin].
        -- Exists (-1) sum.
           rewrite (Znth_or_null_out s (-1)) by lia.
           rewrite (nodes_split Ews s vs 0 jm (Zlength s)) by lia.
           entailer!.
        -- apply In_Znth in Hin. destruct Hin as [i [Hi <-]].
           Exists i sum.
           rewrite (Znth_or_null_in s i) by lia.
           rewrite (nodes_split Ews s vs 0 jm (Zlength s)) by lia.
           entailer!.
      * Intros i sum2.
        destruct (zeq i (-1)).
        -- subst i. rewrite (Znth_or_null_out s (-1)) by lia.
           forward_if.
           { first [discriminate | contradiction | congruence]. }
           forward. Exists sum2. entailer!.
        -- rewrite (Znth_or_null_in s i) by lia.
           assert (Hpi: isptr (Znth i s)) by (apply Hptr; lia).
           forward_if.
           { rewrite (nodes_focus Ews s vs 0 i (Zlength s)) by lia. entailer!. }
           ++ rewrite (nodes_focus Ews s vs 0 i (Zlength s)) by lia. Intros.
              assert (Hpay: int_val (pay (Znth i vs))) by (apply Hip; lia).
              destruct (Znth i vs) as [pi [ni qi]] eqn:Ei.
              destruct Hpay as [xi Hxi]. simpl in Hxi. subst pi.
              forward.
              forward.
              Exists i (Int.add sum2 xi).
              entailer!.
           ++ destruct (Znth i s); try contradiction; discriminate.
      * Intros i sum2.
        assert (Hqi: prv (Znth i vs) = Znth_or_null s (i-1)) by (apply Hp; lia).
        assert (Hpn: is_pointer_or_null (Znth_or_null s (i-1)))
          by (apply (Znth_or_null_pn s (i-1) 0 (Zlength s)); auto; lia).
        rewrite (nodes_focus Ews s vs 0 i (Zlength s)) by lia. Intros.
        destruct (Znth i vs) as [pi [ni qi]] eqn:Ei.
        unfold prv in Hqi; simpl in Hqi. subst qi.
        forward.
        Exists (i-1) sum2.
        entailer!.
        rewrite (nodes_focus Ews s vs 0 i (Zlength s)) by lia. rewrite Ei. cancel.
      * (* ---------------- free_all and return ---------------- *)
        Intros sum2.
        forward_call (gv, s, vs, jm).
        { pre_tac s vs. }
        forward.
        Exists sum2. entailer!.
Qed.

Lemma body_main: semax_body Vprog Gprog f_main main_spec.
Proof.
  start_function.
  sep_apply (create_mem_mgr gv).
  forward_call (gv, Ews, gv _input, input_vals, 5).
  forward.
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
  semax_func_cons body_client.
  semax_func_cons body_main.
Qed.
