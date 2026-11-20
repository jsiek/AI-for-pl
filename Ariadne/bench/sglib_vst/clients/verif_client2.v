Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import SglibVST.client2 SglibVST.spec_client2.
Require SglibVST.lib_client2.
Require VST.veric.semax_prog.

Local Open Scope logic.

(* This client uses no comparator. *)
Definition Rc_client : globals -> val -> mpred := fun _ _ => emp.

#[export] Existing Instance NullExtension.Espec.

(* ================================================================== *)
(* Malloc tokens of the nodes lo .. hi-1 of s                          *)
(* ================================================================== *)

Fixpoint toksL (l: list val) : mpred :=
  match l with
  | nil => emp
  | x :: l' => malloc_token Ews t_dl x * toksL l'
  end.

Lemma toksL_app: forall l1 l2, toksL (l1 ++ l2) = toksL l1 * toksL l2.
Proof.
  induction l1; intros; simpl.
  - rewrite emp_sepcon. auto.
  - rewrite IHl1, sepcon_assoc. auto.
Qed.

Definition toks (s: list val) (lo hi: Z) : mpred :=
  toksL (sublist lo hi s).

Lemma toks_split: forall s lo m hi, 0 <= lo <= m -> m <= hi <= Zlength s ->
  toks s lo hi = toks s lo m * toks s m hi.
Proof.
  intros. unfold toks. rewrite (sublist_split lo m hi) by lia.
  apply toksL_app.
Qed.

Lemma toks_one: forall s i, 0 <= i < Zlength s ->
  toks s i (i+1) = malloc_token Ews t_dl (Znth i s).
Proof.
  intros. unfold toks. rewrite sublist_one by lia. simpl. apply sepcon_emp.
Qed.

Lemma toks_empty: forall s lo, toks s lo lo = emp.
Proof. intros. unfold toks. rewrite sublist_nil. reflexivity. Qed.

Lemma toks_cons: forall x s,
  toks (x::s) 0 (Zlength s + 1) = malloc_token Ews t_dl x * toks s 0 (Zlength s).
Proof.
  intros. unfold toks. rewrite !sublist_same; auto. rewrite Zlength_cons; lia.
Qed.

Lemma ins0: forall {A} {d: Inhabitant A} (x: A) l, ins 0 x l = x :: l.
Proof.
  intros. unfold ins. rewrite sublist_nil. simpl. rewrite sublist_same; auto.
Qed.

Lemma Znth_or_null_cons0: forall x s, Znth_or_null (x::s) 0 = x.
Proof.
  intros. unfold Znth_or_null. rewrite Zlength_cons.
  pose proof (Zlength_nonneg s).
  destruct (zle 0 0); [|lia]. destruct (zlt 0 (Z.succ (Zlength s))); [|lia].
  apply Znth_0_cons.
Qed.

Lemma at_node0: forall s, at_node s 0.
Proof.
  intros. destruct s. left; auto. right. rewrite Zlength_cons.
  pose proof (Zlength_nonneg s). lia.
Qed.

Lemma cmp_env_null: forall eqp sheq veq,
  cmp_env Rc_client nullval eqp sheq veq = emp.
Proof. intros. unfold cmp_env. rewrite if_true by auto. auto. Qed.

Lemma cmp_state_null: forall gv, cmp_state Rc_client gv nullval = emp.
Proof. intros. unfold cmp_state. rewrite if_true by auto. auto. Qed.

Ltac side :=
  repeat match goal with |- _ /\ _ => split end;
  try apply at_node0;
  try (left; reflexivity);
  try (eapply SglibVST.lib_client2.prev_links_sub; [eassumption | lia | lia]);
  try (eapply SglibVST.lib_client2.next_links_sub; [eassumption | lia | lia]);
  auto; try lia.

Lemma Znth_or_null0_pn: forall sh s vs,
  nodes sh s vs 0 (Zlength s) |-- !! is_pointer_or_null (Znth_or_null s 0).
Proof.
  intros. eapply derives_trans.
  apply (SglibVST.lib_client2.nodes_isptr sh s vs 0 (Zlength s)).
  apply prop_derives. intros.
  apply (SglibVST.lib_client2.Znth_or_null_pn s 0 0 (Zlength s)); auto.
  pose proof (Zlength_nonneg s); lia.
Qed.

(* fails on any goal left over: every [all: fail_show] below closes nothing *)
Ltac fail_show := match goal with |- ?G => idtac "OPEN GOAL:" G; fail 100 end.

Ltac nullcontra :=
  first [ match goal with Hn: false = true |- _ => discriminate Hn end
        | match goal with Hn: ?x <> ?x |- _ => exfalso; apply Hn; reflexivity end
        | match goal with Hn: ?p = nullval, Hi: isptr ?p |- _ =>
            rewrite Hn in Hi; contradiction end
        | match goal with Hn: ?p = nullval, Hi: ?p <> nullval |- _ =>
            contradiction end
        | fail_show ].

Ltac disj :=
  try solve [left; repeat split; auto; lia | right; repeat split; auto; lia].

Lemma whole_cons: forall e s vs, whole (ins 0 e s) vs -> whole (e::s) vs.
Proof. intros. rewrite ins0 in H. auto. Qed.

(* ================================================================== *)
(* Funspecs of the client's own functions                              *)
(* ================================================================== *)

Definition free_all_spec :=
 DECLARE _free_all
  WITH gv: globals, s: list val, vs: list node_v
  PRE [ tptr t_dl ]
    PROP (whole s vs)
    PARAMS (Znth_or_null s 0) GLOBALS (gv)
    SEP (mem_mgr gv; nodes Ews s vs 0 (Zlength s); toks s 0 (Zlength s))
  POST [ tvoid ]
    PROP () RETURN () SEP (mem_mgr gv).

Definition client_spec :=
 DECLARE _client
  WITH gv: globals, sh: share, inp: val, n: Z, xs: list int
  PRE [ tptr tint, tint ]
    PROP (readable_share sh; 0 <= n <= Zlength xs;
          Zlength xs <= Int.max_signed)
    PARAMS (inp; Vint (Int.repr n)) GLOBALS (gv)
    SEP (mem_mgr gv; data_at sh (tarray tint (Zlength xs)) (map Vint xs) inp)
  POST [ tvoid ]
    PROP () RETURN ()
    SEP (mem_mgr gv; data_at sh (tarray tint (Zlength xs)) (map Vint xs) inp).

Definition input_vals : list int := map Int.repr [6;7;3;4;7].

Definition main_spec :=
 DECLARE _main
  WITH gv: globals
  PRE [ ] main_pre prog tt gv
  POST [ tint ]
    PROP () RETURN (Vint (Int.repr 0))
    SEP (mem_mgr gv; has_ext tt;
         data_at Ews (tarray tint 5) (map Vint input_vals) (gv _input)).

Definition Gprog : funspecs :=
  ltac:(with_library prog [add_spec; get_first_spec; get_last_spec;
                           it_init_on_equal_spec Rc_client; it_init_spec;
                           it_next_spec Rc_client;
                           free_all_spec; client_spec; main_spec]).

(* ================================================================== *)
(* Library functions: from lib_client2                                 *)
(* ================================================================== *)

Lemma Gprog_sub: forall f,
  tycontext_sub (func_tycontext f Vprog (SglibVST.spec_client2.Gprog Rc_client) nil)
                (func_tycontext f Vprog Gprog nil).
Proof.
  intros. apply VST.veric.semax_prog.func_tycontext_sub.
  - apply incl_refl.
  - unfold incl, Gprog, SglibVST.spec_client2.Gprog. intros x Hx.
    repeat (destruct Hx as [Hx|Hx]; [subst x; repeat (first [now left | right]) |]).
    destruct Hx.
  - unfold Gprog, Vprog. simpl. repeat constructor; simpl; intuition discriminate.
Qed.

Ltac lib_body L :=
  eapply semax_body_subsumption; [apply L | apply Gprog_sub].

Lemma body_add: semax_body Vprog Gprog f_sglib_dllist_add add_spec.
Proof. lib_body (SglibVST.lib_client2.body_add Rc_client). Qed.
Lemma body_get_first:
  semax_body Vprog Gprog f_sglib_dllist_get_first get_first_spec.
Proof. lib_body (SglibVST.lib_client2.body_get_first Rc_client). Qed.
Lemma body_get_last:
  semax_body Vprog Gprog f_sglib_dllist_get_last get_last_spec.
Proof. lib_body (SglibVST.lib_client2.body_get_last Rc_client). Qed.
Lemma body_it_init_on_equal:
  semax_body Vprog Gprog f_sglib_dllist_it_init_on_equal
    (it_init_on_equal_spec Rc_client).
Proof. lib_body (SglibVST.lib_client2.body_it_init_on_equal Rc_client). Qed.
Lemma body_it_init:
  semax_body Vprog Gprog f_sglib_dllist_it_init it_init_spec.
Proof. lib_body (SglibVST.lib_client2.body_it_init Rc_client). Qed.
Lemma body_it_next:
  semax_body Vprog Gprog f_sglib_dllist_it_next (it_next_spec Rc_client).
Proof. lib_body (SglibVST.lib_client2.body_it_next Rc_client). Qed.

(* ================================================================== *)
(* free_all                                                            *)
(* ================================================================== *)

Lemma body_free_all: semax_body Vprog Gprog f_free_all free_all_spec.
Proof.
  start_function.
  destruct H as [Hlen [Hprev Hnext]].
  assert_PROP (forall i, 0 <= i < Zlength s -> isptr (Znth i s)) as Hp.
  { sep_apply (SglibVST.lib_client2.nodes_isptr Ews s vs 0 (Zlength s)). entailer!. }
  forward_call (Tsh, v_it, Ews, s, vs, 0).
  { side. }
  Intros vret. destruct vret as [[b0 f0] r0]. simpl fst in *. simpl snd in *.
  forward_loop (EX b: Z, EX f: Z, EX c: Z, EX l: val,
    PROP (-1 <= b < f; f <= Zlength s;
          (l = nullval /\ b = -1 /\ f = Zlength s) \/
          (b < c < f /\ l = Znth c s /\ isptr l))
    LOCAL (temp _l l; lvar _it t_it v_it; gvars gv)
    SEP (it_rep Tsh v_it s b f nullval nullval;
         nodes Ews s vs 0 (b+1); nodes Ews s vs f (Zlength s);
         toks s 0 (b+1); toks s f (Zlength s);
         (if Val.eq l nullval then emp
          else data_at Ews t_dl (Znth c vs) l * malloc_token Ews t_dl l);
         mem_mgr gv))%assert
    break: (PROP () LOCAL (lvar _it t_it v_it; gvars gv)
            SEP (data_at_ Tsh t_it v_it; mem_mgr gv))%assert.
  - (* entry *)
    destruct H as [Hb [Hf [Hr [Hrn Hex]]]].
    destruct (Hex eq_refl) as [[-> [-> [-> ->]]] | [c [Hc [-> [-> ->]]]]].
    + Exists (-1) 0 0 nullval. rewrite if_true by auto.
      change (Zlength (@nil val)) with 0.
      replace (-1+1) with 0 by lia.
      rewrite !SglibVST.lib_client2.nodes_empty by lia.
      rewrite !toks_empty. entailer!.
    + Exists (c-1) (c+1) c (Znth c s).
      assert (isptr (Znth c s)) by (apply Hp; lia).
      rewrite if_false by (intro Hn; rewrite Hn in H; contradiction).
      rewrite (SglibVST.lib_client2.nodes_focus Ews s vs 0 c (Zlength s)) by lia.
      rewrite (toks_split s 0 c (Zlength s)) by lia.
      rewrite (toks_split s c (c+1) (Zlength s)) by lia.
      rewrite toks_one by lia.
      replace (c-1+1) with c by lia.
      entailer!; disj.
      all: fail_show.
  - (* body *)
    Intros b f c l.
    clear H.
    match goal with Hd: (_ = nullval /\ _) \/ _ |- _ => rename Hd into Hdisj end.
    destruct Hdisj as [[-> [-> ->]] | [Hc [-> Hl]]].
    { (* l = NULL: leave the loop *)
      rewrite if_true by auto.
      forward_if.
      { nullcontra. }
      forward.
      replace (-1+1) with 0 by lia.
      rewrite !SglibVST.lib_client2.nodes_empty by lia. rewrite !toks_empty.
      unfold it_rep. Intros cur.
      entailer!.
      all: try (sep_apply (data_at_data_at_ Tsh t_it); cancel).
      all: fail_show. }
    rewrite if_false by (intro Hn; rewrite Hn in Hl; contradiction).
    forward_if.
    2: { nullcontra. }
    + forward_call (t_dl, Znth c s, gv).
      { rewrite if_false by (intro Hn; rewrite Hn in Hl; contradiction).
        sep_apply (data_at_data_at_ Ews t_dl (Znth c vs) (Znth c s)). cancel. }
      forward_call (gv, Tsh, v_it, Ews, s, vs, b, f, nullval, nullval, Ews,
                    (Vundef, (Vundef, Vundef))).
      { rewrite cmp_env_null, cmp_state_null. cancel. }
      { side. }
      Intros vret. destruct vret as [[b' f'] r]. simpl fst in *. simpl snd in *.
      rewrite cmp_env_null, cmp_state_null.
      forward.
      destruct H2 as [_ Hex].
      specialize (Hex eq_refl).
      destruct Hex as [[-> [-> [-> [-> ->]]]] | [[Hb0 [-> [-> ->]]] | [Hfl [-> [-> ->]]]]].
      * Exists (-1) (Zlength s) 0 nullval. rewrite if_true by auto. entailer!; disj.
        all: fail_show.
      * assert (Hpt: isptr (Znth b s)) by (apply Hp; lia).
        Exists (b-1) f b (Znth b s).
        rewrite if_false by (intro Hn; rewrite Hn in Hpt; contradiction).
        rewrite (SglibVST.lib_client2.nodes_split Ews s vs 0 b (b+1)) by lia.
        rewrite SglibVST.lib_client2.nodes_one.
        rewrite (toks_split s 0 b (b+1)) by lia. rewrite toks_one by lia.
        replace (b-1+1) with b by lia.
        entailer!; disj.
        all: fail_show.
      * assert (Hpt: isptr (Znth f s)) by (apply Hp; lia).
        Exists b (f+1) f (Znth f s).
        rewrite if_false by (intro Hn; rewrite Hn in Hpt; contradiction).
        rewrite (SglibVST.lib_client2.nodes_split Ews s vs f (f+1) (Zlength s)) by lia.
        rewrite SglibVST.lib_client2.nodes_one.
        rewrite (toks_split s f (f+1) (Zlength s)) by lia. rewrite toks_one by lia.
        entailer!; disj.
        all: fail_show.
  - (* after the loop *)
    entailer!.
    all: fail_show.
Qed.

(* ================================================================== *)
(* client                                                              *)
(* ================================================================== *)

Lemma body_client: semax_body Vprog Gprog f_client client_spec.
Proof.
  start_function.
  forward. forward.
  forward_loop (EX k: Z, EX sa: list val, EX vsa: list node_v, EX xa: list int,
                EX sb: list val, EX vsb: list node_v,
    PROP (0 <= k <= n; whole sa vsa; map pay vsa = map Vint xa; whole sb vsb)
    LOCAL (temp _k (Vint (Int.repr k)); temp _input__1 inp;
           temp _n (Vint (Int.repr n));
           lvar _it t_it v_it; lvar _b (tptr t_dl) v_b; lvar _a (tptr t_dl) v_a;
           gvars gv)
    SEP (mem_mgr gv; data_at sh (tarray tint (Zlength xs)) (map Vint xs) inp;
         data_at Tsh (tptr t_dl) (Znth_or_null sa 0) v_a;
         data_at Tsh (tptr t_dl) (Znth_or_null sb 0) v_b;
         data_at_ Tsh t_it v_it;
         nodes Ews sa vsa 0 (Zlength sa); toks sa 0 (Zlength sa);
         nodes Ews sb vsb 0 (Zlength sb); toks sb 0 (Zlength sb)))
    continue: (EX k: Z, EX sa: list val, EX vsa: list node_v, EX xa: list int,
                EX sb: list val, EX vsb: list node_v,
    PROP (0 <= k < n; whole sa vsa; map pay vsa = map Vint xa; whole sb vsb)
    LOCAL (temp _k (Vint (Int.repr k)); temp _input__1 inp;
           temp _n (Vint (Int.repr n));
           lvar _it t_it v_it; lvar _b (tptr t_dl) v_b; lvar _a (tptr t_dl) v_a;
           gvars gv)
    SEP (mem_mgr gv; data_at sh (tarray tint (Zlength xs)) (map Vint xs) inp;
         data_at Tsh (tptr t_dl) (Znth_or_null sa 0) v_a;
         data_at Tsh (tptr t_dl) (Znth_or_null sb 0) v_b;
         data_at_ Tsh t_it v_it;
         nodes Ews sa vsa 0 (Zlength sa); toks sa 0 (Zlength sa);
         nodes Ews sb vsb 0 (Zlength sb); toks sb 0 (Zlength sb)))
    break: (EX sa: list val, EX vsa: list node_v, EX xa: list int,
            EX sb: list val, EX vsb: list node_v,
    PROP (whole sa vsa; map pay vsa = map Vint xa; whole sb vsb)
    LOCAL (lvar _it t_it v_it; lvar _b (tptr t_dl) v_b; lvar _a (tptr t_dl) v_a;
           gvars gv)
    SEP (mem_mgr gv; data_at sh (tarray tint (Zlength xs)) (map Vint xs) inp;
         data_at Tsh (tptr t_dl) (Znth_or_null sa 0) v_a;
         data_at Tsh (tptr t_dl) (Znth_or_null sb 0) v_b;
         data_at_ Tsh t_it v_it;
         nodes Ews sa vsa 0 (Zlength sa); toks sa 0 (Zlength sa);
         nodes Ews sb vsb 0 (Zlength sb); toks sb 0 (Zlength sb))).
  - (* entry *)
    try forward.
    Exists 0 (@nil val) (@nil node_v) (@nil int) (@nil val) (@nil node_v).
    rewrite !(SglibVST.lib_client2.Znth_or_null_out [] 0) by (rewrite Zlength_nil; lia).
    change (Zlength (@nil val)) with 0.
    rewrite !SglibVST.lib_client2.nodes_empty by lia. rewrite !toks_empty.
    entailer!.
    all: try (unfold whole, prev_links, next_links; repeat split; try reflexivity;
              intros i Hi; rewrite ?Zlength_nil in Hi; lia).
    all: fail_show.
  - (* body *)
    Intros k sa vsa xa sb vsb.
    forward_if.
    2: { forward. Exists sa vsa xa sb vsb. entailer!. }
    forward_call (t_dl, gv).
    Intros l.
    destruct (eq_dec l nullval) as [Hl0|Hl0].
    { subst l. try rewrite if_true by auto.
      forward_if.
      - forward. Exists sa vsa xa sb vsb. entailer!. all: fail_show.
      - nullcontra. }
    try rewrite if_false by auto.
    Intros.
    forward_if.
    { nullcontra. }
    forward.
    forward.
    forward_if (EX sa: list val, EX vsa: list node_v, EX xa: list int,
                EX sb: list val, EX vsb: list node_v,
      PROP (0 <= k < n; whole sa vsa; map pay vsa = map Vint xa; whole sb vsb)
      LOCAL (temp _k (Vint (Int.repr k)); temp _input__1 inp;
             temp _n (Vint (Int.repr n));
             lvar _it t_it v_it; lvar _b (tptr t_dl) v_b; lvar _a (tptr t_dl) v_a;
             gvars gv)
      SEP (mem_mgr gv; data_at sh (tarray tint (Zlength xs)) (map Vint xs) inp;
           data_at Tsh (tptr t_dl) (Znth_or_null sa 0) v_a;
           data_at Tsh (tptr t_dl) (Znth_or_null sb 0) v_b;
           data_at_ Tsh t_it v_it;
           nodes Ews sa vsa 0 (Zlength sa); toks sa 0 (Zlength sa);
           nodes Ews sb vsb 0 (Zlength sb); toks sb 0 (Zlength sb))).
    + apply prop_right. intros [_ Hm].
      apply (f_equal Int.signed) in Hm.
      rewrite Int.signed_repr in Hm by rep_lia. rewrite Int.signed_mone in Hm.
      discriminate.
    + forward_call (Tsh, v_a, Ews, l, Vint (Znth k xs), snd (default_val t_dl),
                    sa, vsa, 0).
      { side. }
      Intros vsa'.
      rewrite ins0 in *.
      Exists (l::sa) vsa' (Znth k xs :: xa) sb vsb.
      rewrite Znth_or_null_cons0. rewrite Zlength_cons.
      replace (Z.succ (Zlength sa)) with (Zlength sa + 1) by lia.
      rewrite toks_cons.
      entailer!.
      all: try (match goal with Hm: map pay _ = _ :: map pay _ |- _ => rewrite Hm end;
                rewrite H3; reflexivity).
      all: fail_show.
    + forward_call (Tsh, v_b, Ews, l, Vint (Znth k xs), snd (default_val t_dl),
                    sb, vsb, 0).
      { side. }
      Intros vsb'.
      rewrite ins0 in *.
      Exists sa vsa xa (l::sb) vsb'.
      rewrite Znth_or_null_cons0. rewrite Zlength_cons.
      replace (Z.succ (Zlength sb)) with (Zlength sb + 1) by lia.
      rewrite toks_cons.
      entailer!.
      all: fail_show.
    + Intros sa' vsa' xa' sb' vsb'.
      Exists k sa' vsa' xa' sb' vsb'. entailer!.
      all: fail_show.
  - (* increment *)
    Intros k sa vsa xa sb vsb.
    forward.
    Exists (k+1) sa vsa xa sb vsb. entailer!.
    all: fail_show.
  - (* second phase *)
    Intros sa vsa xa sb vsb.
    match goal with Hw: whole sa vsa |- _ => destruct Hw as [Hlen [Hprev Hnext]] end.
    match goal with Hw: map pay vsa = map Vint xa |- _ => rename Hw into Hmap end.
    assert_PROP (forall i, 0 <= i < Zlength sa -> isptr (Znth i sa)) as Hp.
    { sep_apply (SglibVST.lib_client2.nodes_isptr Ews sa vsa 0 (Zlength sa)). entailer!. }
    assert (Hxl: Zlength xa = Zlength sa).
    { rewrite <- (Zlength_map _ _ Vint), <- Hmap, Zlength_map. auto. }
    assert_PROP (is_pointer_or_null (Znth_or_null sa 0)) as Hpa.
    { sep_apply (Znth_or_null0_pn Ews sa vsa). entailer!. }
    forward.
    forward_call (Tsh, v_it, Ews, sa, vsa, 0).
    { side. }
    Intros vret. destruct vret as [[b0 f0] r0]. simpl fst in *. simpl snd in *.
    try forward.
    forward_loop (EX bw: Z, EX fw: Z, EX l: val, EX sb: list val, EX vsb: list node_v,
      PROP (-1 <= bw < fw; fw <= Zlength sa;
            l = nullval \/ (exists c, bw < c < fw /\ l = Znth c sa);
            whole sb vsb)
      LOCAL (temp _l l; lvar _it t_it v_it; lvar _b (tptr t_dl) v_b;
             lvar _a (tptr t_dl) v_a; gvars gv)
      SEP (mem_mgr gv; data_at sh (tarray tint (Zlength xs)) (map Vint xs) inp;
           data_at Tsh (tptr t_dl) (Znth_or_null sa 0) v_a;
           data_at Tsh (tptr t_dl) (Znth_or_null sb 0) v_b;
           it_rep Tsh v_it sa bw fw nullval nullval;
           nodes Ews sa vsa 0 (Zlength sa); toks sa 0 (Zlength sa);
           nodes Ews sb vsb 0 (Zlength sb); toks sb 0 (Zlength sb)))
      continue: (EX bw: Z, EX fw: Z, EX sb: list val, EX vsb: list node_v,
      PROP (-1 <= bw < fw; fw <= Zlength sa; whole sb vsb)
      LOCAL (lvar _it t_it v_it; lvar _b (tptr t_dl) v_b;
             lvar _a (tptr t_dl) v_a; gvars gv)
      SEP (mem_mgr gv; data_at sh (tarray tint (Zlength xs)) (map Vint xs) inp;
           data_at Tsh (tptr t_dl) (Znth_or_null sa 0) v_a;
           data_at Tsh (tptr t_dl) (Znth_or_null sb 0) v_b;
           it_rep Tsh v_it sa bw fw nullval nullval;
           nodes Ews sa vsa 0 (Zlength sa); toks sa 0 (Zlength sa);
           nodes Ews sb vsb 0 (Zlength sb); toks sb 0 (Zlength sb)))
      break: (EX bw: Z, EX fw: Z, EX sb: list val, EX vsb: list node_v,
      PROP (whole sb vsb)
      LOCAL (lvar _it t_it v_it; lvar _b (tptr t_dl) v_b;
             lvar _a (tptr t_dl) v_a; gvars gv)
      SEP (mem_mgr gv; data_at sh (tarray tint (Zlength xs)) (map Vint xs) inp;
           data_at Tsh (tptr t_dl) (Znth_or_null sa 0) v_a;
           data_at Tsh (tptr t_dl) (Znth_or_null sb 0) v_b;
           it_rep Tsh v_it sa bw fw nullval nullval;
           nodes Ews sa vsa 0 (Zlength sa); toks sa 0 (Zlength sa);
           nodes Ews sb vsb 0 (Zlength sb); toks sb 0 (Zlength sb))).
    + (* entry *)
      lazymatch goal with Hi: init_window _ _ _ _ _ |- _ =>
        destruct Hi as [Hb [Hf [Hr [Hrn _]]]] end.
      Exists b0 f0 r0 sb vsb. entailer!.
      all: try (destruct Hr as [Hr | [c [Hc Hr]]]; [left; auto | right; exists c; auto]).
      all: fail_show.
    + (* body *)
      Intros bw fw l sb' vsb'.
      match goal with Hd: l = nullval \/ _ |- _ => rename Hd into Hdisj end.
      destruct Hdisj as [-> | [c [Hc ->]]].
      { forward_if.
        - nullcontra.
        - forward. Exists bw fw sb' vsb'. entailer!. all: fail_show. }
      assert (Hpt: isptr (Znth c sa)) by (apply Hp; lia).
      rewrite (SglibVST.lib_client2.nodes_focus Ews sa vsa 0 c (Zlength sa)) by lia.
      forward_if.
      2: { nullcontra. }
      forward_call (t_dl, gv).
      Intros cp.
      destruct (eq_dec cp nullval) as [Hc0|Hc0].
      { subst cp. try rewrite if_true by auto.
        forward_if.
        - forward. Exists bw fw sb' vsb'.
          rewrite (SglibVST.lib_client2.nodes_focus Ews sa vsa 0 c (Zlength sa)) by lia.
          entailer!. all: fail_show.
        - nullcontra. }
      try rewrite if_false by auto. Intros.
      forward_if.
      { nullcontra. }
      assert (Hpc: pay (Znth c vsa) = Vint (Znth c xa)).
      { rewrite <- (Znth_map c pay) by lia. rewrite Hmap. rewrite Znth_map by lia. auto. }
      destruct (Znth c vsa) as [pc [nc qc]] eqn:Ec.
      unfold pay in Hpc; simpl in Hpc. subst pc.
      Intros.
      forward.
      forward.
      forward_call (Tsh, v_b, Ews, cp, Vint (Znth c xa), (Vundef, Vundef),
                    sb', vsb', 0).
      { side. }
      Intros vsb''.
      rewrite ins0 in *.
      Exists bw fw (cp::sb') vsb''.
      rewrite Znth_or_null_cons0. rewrite Zlength_cons.
      replace (Z.succ (Zlength sb')) with (Zlength sb' + 1) by lia.
      rewrite toks_cons.
      rewrite (SglibVST.lib_client2.nodes_focus Ews sa vsa 0 c (Zlength sa)) by lia.
      rewrite Ec.
      entailer!.
      all: fail_show.
    + (* increment *)
      Intros bw fw sb' vsb'.
      rewrite (SglibVST.lib_client2.nodes_split Ews sa vsa 0 (bw+1) (Zlength sa)) by lia.
      rewrite (SglibVST.lib_client2.nodes_split Ews sa vsa (bw+1) fw (Zlength sa)) by lia.
      forward_call (gv, Tsh, v_it, Ews, sa, vsa, bw, fw, nullval, nullval, Ews,
                    (Vundef, (Vundef, Vundef))).
      { rewrite cmp_env_null, cmp_state_null. cancel. }
      { side. }
      Intros vret. destruct vret as [[b' f'] r]. simpl fst in *. simpl snd in *.
      rewrite cmp_env_null, cmp_state_null.
      lazymatch goal with Hs: iter_step _ _ _ _ _ _ _ |- _ =>
        destruct Hs as [[Hb' [Hf' [Hr _]]] _] end.
      forward.
      Exists b' f' r sb' vsb'.
      rewrite (SglibVST.lib_client2.nodes_split Ews sa vsa 0 (bw+1) (Zlength sa)) by lia.
      rewrite (SglibVST.lib_client2.nodes_split Ews sa vsa (bw+1) fw (Zlength sa)) by lia.
      entailer!.
      all: try (destruct Hr as [Hr | [c [Hc [_ Hr]]]];
                [left; auto | right; exists c; split; auto; lia]).
      all: fail_show.
    + (* after the loop *)
      Intros bw fw sb' vsb'.
      assert_PROP (is_pointer_or_null (Znth_or_null sb' 0)) as Hpb.
      { sep_apply (Znth_or_null0_pn Ews sb' vsb'). entailer!. }
      forward.
      forward_call (gv, sa, vsa).
      { split; auto. }
      forward.
      forward_call (gv, sb', vsb').
      unfold it_rep. Intros cur.
      entailer!.
      all: try (sep_apply (data_at_data_at_ Tsh t_it); cancel).
      all: fail_show.
Qed.

(* ================================================================== *)
(* main                                                                *)
(* ================================================================== *)

Lemma body_main: semax_body Vprog Gprog f_main main_spec.
Proof.
  start_function.
  sep_apply (create_mem_mgr gv).
  change (data_at Ews (tarray tint 5)
            (map Vint [Int.repr 6; Int.repr 7; Int.repr 3; Int.repr 4; Int.repr 7])
            (gv _input))
    with (data_at Ews (tarray tint (Zlength input_vals)) (map Vint input_vals)
            (gv _input)).
  forward_call (gv, Ews, gv _input, 5, input_vals).
  { change (Zlength input_vals) with 5. repeat split; auto; rep_lia. }
  change (Zlength input_vals) with 5.
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
  semax_func_cons body_free_all.
  semax_func_cons body_client.
  semax_func_cons body_main.
Qed.
