Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import SglibVST.clientb1a SglibVST.spec_clientb1a.
Require SglibVST.lib_clientb1a.
Import SglibVST.lib_clientb1a.  (* helper lemmas on nodes, links *)

#[export] Existing Instance NullExtension.Espec.

Local Open Scope logic.

(* This program uses no comparator. *)
Definition Rc_client : globals -> val -> mpred := fun _ _ => emp.

(* ================================================================== *)
(* Helpers                                                            *)
(* ================================================================== *)

Fixpoint toksl (l: list val) : mpred :=
  match l with
  | nil => emp
  | p :: l' => malloc_token Ews t_dl p * toksl l'
  end.

Lemma iter_sepcon_app: forall l1 l2, toksl (l1 ++ l2) = toksl l1 * toksl l2.
Proof.
  induction l1; intros; simpl.
  - rewrite emp_sepcon. auto.
  - rewrite IHl1. rewrite sepcon_assoc. auto.
Qed.

Definition toks (s: list val) (lo hi: Z) : mpred := toksl (sublist lo hi s).

Lemma toks_empty: forall s lo hi, hi <= lo -> toks s lo hi = emp.
Proof. intros. unfold toks. rewrite sublist_nil_gen by lia. reflexivity. Qed.

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

Lemma toks_cons: forall p s,
  toks (p::s) 0 (Zlength s + 1) = malloc_token Ews t_dl p * toks s 0 (Zlength s).
Proof.
  intros. unfold toks.
  rewrite sublist_same by (rewrite ?Zlength_cons; lia).
  rewrite sublist_same by lia. reflexivity.
Qed.

Lemma ins0: forall {A} {d: Inhabitant A} (x: A) l, ins 0 x l = x :: l.
Proof.
  intros. unfold ins. rewrite sublist_nil_gen by lia.
  rewrite sublist_same by lia. reflexivity.
Qed.

Lemma cmp_env_null: forall Rc e sh v, cmp_env Rc nullval e sh v = emp.
Proof. intros. unfold cmp_env. destruct (Val.eq nullval nullval); congruence. Qed.

Lemma cmp_state_null: forall Rc gv, cmp_state Rc gv nullval = emp.
Proof. intros. unfold cmp_state. destruct (Val.eq nullval nullval); congruence. Qed.

Lemma at_node0: forall s, at_node s 0.
Proof.
  intros. unfold at_node. destruct s; [left; auto|right].
  rewrite Zlength_cons. pose proof (Zlength_nonneg s). lia.
Qed.

Lemma int_payloads_cons: forall (s: list val) vs vs' x,
  Zlength vs = Zlength s -> Zlength vs' = Zlength s + 1 ->
  map pay vs' = Vint x :: map pay vs ->
  int_payloads vs 0 (Zlength s) -> int_payloads vs' 0 (Zlength s + 1).
Proof.
  intros s vs vs' x L1 L2 Hm Hi i Hr.
  replace (pay (Znth i vs')) with (Znth i (map pay vs')) by (rewrite Znth_map by lia; auto).
  rewrite Hm. destruct (zeq i 0).
  - subst. rewrite Znth_0_cons. exists x; auto.
  - rewrite Znth_pos_cons by lia. rewrite Znth_map by lia. apply Hi. lia.
Qed.

Lemma pn_all: forall s i, (forall i, 0 <= i < Zlength s -> isptr (Znth i s)) ->
  is_pointer_or_null (Znth_or_null s i).
Proof.
  intros. apply (Znth_or_null_pn s i 0 (Zlength s)); auto. lia.
Qed.

(* the node the client holds between it_init/it_next and free *)
Definition cur (vs: list node_v) (c: Z) (r: val) : mpred :=
  if eq_dec r nullval then emp
  else data_at Ews t_dl (Znth c vs) r * malloc_token Ews t_dl r.

Lemma cur_null: forall vs c, cur vs c nullval = emp.
Proof. intros. unfold cur. rewrite if_true by auto. auto. Qed.

Lemma cur_ptr: forall vs c r, isptr r ->
  cur vs c r = data_at Ews t_dl (Znth c vs) r * malloc_token Ews t_dl r.
Proof.
  intros. unfold cur. rewrite if_false; auto.
  intro; subst; contradiction.
Qed.

(* ================================================================== *)
(* Specs                                                              *)
(* ================================================================== *)

Definition b1_spec :=
 DECLARE _b1
  WITH gv: globals, sh: share, inp: val, il: list int, n: Z
  PRE [ tptr tint, tint ]
    PROP (readable_share sh; 0 <= n <= Zlength il; n <= Int.max_signed)
    PARAMS (inp; Vint (Int.repr n)) GLOBALS (gv)
    SEP (data_at sh (tarray tint (Zlength il)) (map Vint il) inp; mem_mgr gv)
  POST [ tint ]
    EX r: int,
    PROP ()
    RETURN (Vint r)
    SEP (data_at sh (tarray tint (Zlength il)) (map Vint il) inp; mem_mgr gv).

Definition input_contents : list int := map Int.repr [6;7;3;4;7].

Definition main_spec :=
 DECLARE _main
  WITH gv: globals
  PRE [ ] main_pre prog tt gv
  POST [ tint ]
    PROP ()
    RETURN (Vint (Int.repr 0))
    SEP (mem_mgr gv; has_ext tt;
         data_at Ews (tarray tint 5) (map Vint input_contents) (gv _input)).

Definition Gprog : funspecs :=
  ltac:(with_library prog [add_spec; get_first_spec; get_last_spec;
                           it_init_on_equal_spec Rc_client; it_init_spec;
                           it_next_spec Rc_client; b1_spec; main_spec]).

Lemma Gprog_check:
  forall i, In i [_sglib_dllist_add; _sglib_dllist_get_first;
                  _sglib_dllist_get_last; _sglib_dllist_it_init_on_equal;
                  _sglib_dllist_it_init; _sglib_dllist_it_next] ->
  VST.veric.initial_world.find_id i Gprog =
  VST.veric.initial_world.find_id i (SglibVST.spec_clientb1a.Gprog Rc_client).
Proof.
  intros i H. simpl in H.
  repeat (destruct H as [<-|H]; [reflexivity|]). contradiction.
Qed.

(* ================================================================== *)
(* Library functions, from lib_clientb1a                              *)
(* ================================================================== *)

Lemma subVG_lib:
  tycontext_subVG Vprog (SglibVST.spec_clientb1a.Gprog Rc_client) Vprog Gprog.
Proof.
  split.
  - apply sub_option_get.
    set (A1 := make_tycontext_g Vprog (SglibVST.spec_clientb1a.Gprog Rc_client)).
    set (A2 := make_tycontext_g Vprog Gprog).
    compute in A1; compute in A2; subst A1 A2.
    repeat (apply Forall_cons; [reflexivity | ]); apply Forall_nil.
  - apply subsume_spec_get.
    set (A1 := make_tycontext_s (SglibVST.spec_clientb1a.Gprog Rc_client)).
    set (A2 := make_tycontext_s Gprog).
    let a := make_ground_PTree A1 in change A1 with a; clear A1.
    let a := make_ground_PTree A2 in change A2 with a; clear A2.
    repeat (apply Forall_cons; [apply subsumespec_refl | ]).
    apply Forall_nil.
Qed.

Ltac from_lib L :=
  eapply semax_body_subsumption; [apply (L Rc_client) |];
  apply tycontext_sub_i99; apply subVG_lib.

Lemma body_add: semax_body Vprog Gprog f_sglib_dllist_add add_spec.
Proof. from_lib SglibVST.lib_clientb1a.body_add. Qed.

Lemma body_get_first:
  semax_body Vprog Gprog f_sglib_dllist_get_first get_first_spec.
Proof. from_lib SglibVST.lib_clientb1a.body_get_first. Qed.

Lemma body_get_last:
  semax_body Vprog Gprog f_sglib_dllist_get_last get_last_spec.
Proof. from_lib SglibVST.lib_clientb1a.body_get_last. Qed.

Lemma body_it_init_on_equal:
  semax_body Vprog Gprog f_sglib_dllist_it_init_on_equal
    (it_init_on_equal_spec Rc_client).
Proof. from_lib SglibVST.lib_clientb1a.body_it_init_on_equal. Qed.

Lemma body_it_init:
  semax_body Vprog Gprog f_sglib_dllist_it_init it_init_spec.
Proof. from_lib SglibVST.lib_clientb1a.body_it_init. Qed.

Lemma body_it_next:
  semax_body Vprog Gprog f_sglib_dllist_it_next (it_next_spec Rc_client).
Proof. from_lib SglibVST.lib_clientb1a.body_it_next. Qed.

(* ================================================================== *)
(* b1                                                                 *)
(* ================================================================== *)

Ltac absurd_if := first [contradiction | discriminate | congruence].

Ltac fin_inv := first [solve [left; repeat split; auto; lia] | solve [right; split; [lia|]; split; [lia|auto]] | idtac].

Lemma body_b1: semax_body Vprog Gprog f_b1 b1_spec.
Proof.
  start_function.
  forward. forward. forward.
  (* loop 1: build *)
  forward_loop
    (EX k: Z, EX s: list val, EX vs: list node_v,
     PROP (0 <= k <= n; Zlength s = k; whole s vs; int_payloads vs 0 k)
     LOCAL (temp _k (Vint (Int.repr k)); temp _last (Vint (Int.repr 0));
            temp _input__1 inp; temp _n (Vint (Int.repr n)); gvars gv;
            lvar _the_list (tptr (Tstruct _dllist noattr)) v_the_list;
            lvar _it (Tstruct _sglib_dllist_iterator noattr) v_it)
     SEP (data_at Tsh (tptr t_dl) (Znth_or_null s 0) v_the_list;
          nodes Ews s vs 0 k; toks s 0 k;
          data_at_ Tsh t_it v_it; mem_mgr gv;
          data_at sh (tarray tint (Zlength il)) (map Vint il) inp))
  continue:
    (EX k: Z, EX s: list val, EX vs: list node_v,
     PROP (0 <= k < n; Zlength s = (k + 1)%Z; whole s vs; int_payloads vs 0 (k+1))
     LOCAL (temp _k (Vint (Int.repr k)); temp _last (Vint (Int.repr 0));
            temp _input__1 inp; temp _n (Vint (Int.repr n)); gvars gv;
            lvar _the_list (tptr (Tstruct _dllist noattr)) v_the_list;
            lvar _it (Tstruct _sglib_dllist_iterator noattr) v_it)
     SEP (data_at Tsh (tptr t_dl) (Znth_or_null s 0) v_the_list;
          nodes Ews s vs 0 (k+1); toks s 0 (k+1);
          data_at_ Tsh t_it v_it; mem_mgr gv;
          data_at sh (tarray tint (Zlength il)) (map Vint il) inp))
  break:
    (EX s: list val, EX vs: list node_v,
     PROP (whole s vs; int_payloads vs 0 (Zlength s))
     LOCAL (temp _last (Vint (Int.repr 0)); gvars gv;
            lvar _the_list (tptr (Tstruct _dllist noattr)) v_the_list;
            lvar _it (Tstruct _sglib_dllist_iterator noattr) v_it)
     SEP (data_at Tsh (tptr t_dl) (Znth_or_null s 0) v_the_list;
          nodes Ews s vs 0 (Zlength s); toks s 0 (Zlength s);
          data_at_ Tsh t_it v_it; mem_mgr gv;
          data_at sh (tarray tint (Zlength il)) (map Vint il) inp)).
  { forward. Exists 0 (@nil val) (@nil node_v).
    rewrite nodes_empty, toks_empty by lia. entailer!.
    split; [|intros i Hi; lia].
    split; [reflexivity|]. split; intros i Hi; rewrite Zlength_nil in Hi; lia. }
  { Intros k s vs. subst k.
    forward_if.
    2:{ forward. Exists s vs. entailer!. }
    forward_call (t_dl, gv).
    Intros p.
    destruct (eq_dec p nullval) as [Hp|Hp].
    { forward_if.
      { forward. Exists s vs. entailer!. }
      { absurd_if. } }
    Intros.
    forward_if.
    { absurd_if. }
    assert (Hlen: Zlength s < Zlength il) by lia.
    forward.
    forward.
    forward_call (Tsh, v_the_list, Ews, p, Vint (Znth (Zlength s) il),
                  (Vundef, Vundef), s, vs, 0).
    { repeat match goal with |- _ /\ _ => split end;
        first [apply at_node0 | assumption | auto]. }
    Intros vs'.
    rewrite ins0 in *.
    Exists (Zlength s) (p :: s) vs'.
    match goal with Hw: whole (p :: s) vs' |- _ => pose proof Hw as [Hl2 _] end.
    match goal with Hw: whole s vs |- _ => pose proof Hw as [Hl1 _] end.
    rewrite Zlength_cons in Hl2.
    entailer!.
    - split; [rewrite Zlength_cons; lia|].
      apply (int_payloads_cons s vs vs' (Znth (Zlength s) il)); auto; lia.
    - rewrite toks_cons.
      rewrite Znth_or_null_in by (rewrite Zlength_cons; pose proof (Zlength_nonneg s); lia).
      rewrite Znth_0_cons. cancel. }
  { Intros k s vs. forward. Exists (k+1) s vs. entailer!. }
  (* loop 2: walk *)
  Intros s vs.
  assert_PROP (forall i, 0 <= i < Zlength s -> isptr (Znth i s)) as Hptr.
  { sep_apply (nodes_isptr Ews s vs 0 (Zlength s)). entailer!. }
  match goal with Hw: whole s vs |- _ => rename Hw into Hwhole end.
  match goal with Hw: int_payloads vs 0 _ |- _ => rename Hw into Hint end.
  pose proof Hwhole as [Hlv [Hprev Hnext]].
  forward_loop
    (EX i: Z, EX li: int,
     PROP (0 <= i <= Zlength s)
     LOCAL (temp _l (Znth_or_null s i); temp _last (Vint li); gvars gv;
            lvar _the_list (tptr (Tstruct _dllist noattr)) v_the_list;
            lvar _it (Tstruct _sglib_dllist_iterator noattr) v_it)
     SEP (data_at Tsh (tptr t_dl) (Znth_or_null s 0) v_the_list;
          nodes Ews s vs 0 (Zlength s); toks s 0 (Zlength s);
          data_at_ Tsh t_it v_it; mem_mgr gv;
          data_at sh (tarray tint (Zlength il)) (map Vint il) inp))
  continue:
    (EX i: Z, EX li: int,
     PROP (0 <= i < Zlength s)
     LOCAL (temp _l (Znth i s); temp _last (Vint li); gvars gv;
            lvar _the_list (tptr (Tstruct _dllist noattr)) v_the_list;
            lvar _it (Tstruct _sglib_dllist_iterator noattr) v_it)
     SEP (data_at Tsh (tptr t_dl) (Znth_or_null s 0) v_the_list;
          nodes Ews s vs 0 (Zlength s); toks s 0 (Zlength s);
          data_at_ Tsh t_it v_it; mem_mgr gv;
          data_at sh (tarray tint (Zlength il)) (map Vint il) inp))
  break:
    (EX li: int,
     PROP ()
     LOCAL (temp _last (Vint li); gvars gv;
            lvar _the_list (tptr (Tstruct _dllist noattr)) v_the_list;
            lvar _it (Tstruct _sglib_dllist_iterator noattr) v_it)
     SEP (data_at Tsh (tptr t_dl) (Znth_or_null s 0) v_the_list;
          nodes Ews s vs 0 (Zlength s); toks s 0 (Zlength s);
          data_at_ Tsh t_it v_it; mem_mgr gv;
          data_at sh (tarray tint (Zlength il)) (map Vint il) inp)).
  { forward.
    { entailer!. apply (pn_all s 0 Hptr). }
    Exists 0 (Int.repr 0). entailer!. }
  { Intros i li.
    destruct (zlt i (Zlength s)).
    - rewrite Znth_or_null_in by lia.
      assert (Hpi := Hptr i ltac:(lia)).
      rewrite (nodes_focus Ews s vs 0 i (Zlength s)) by lia. Intros.
      destruct (Hint i ltac:(lia)) as [x Hx].
      destruct (Znth i vs) as [pi [ni qi]] eqn:Ev.
      simpl in Hx. subst pi.
      forward_if.
      2:{ match goal with Hn: Znth i s = nullval |- _ => rewrite Hn in Hpi end.
          contradiction. }
      forward.
      Exists i x. entailer!.
      rewrite (nodes_focus Ews s vs 0 i (Zlength s)) by lia. rewrite Ev. cancel.
    - rewrite Znth_or_null_out by lia.
      forward_if.
      { absurd_if. }
      forward. Exists li. entailer!. }
  { Intros i li.
    rewrite (nodes_focus Ews s vs 0 i (Zlength s)) by lia. Intros.
    assert (Hn := Hnext i ltac:(lia)).
    destruct (Znth i vs) as [pi [ni qi]] eqn:Ev.
    unfold nxt in Hn; simpl in Hn. subst ni.
    forward.
    { entailer!. apply (pn_all s (i+1) Hptr). }
    Exists (i+1) li. entailer!.
    rewrite (nodes_focus Ews s vs 0 i (Zlength s)) by lia. rewrite Ev. cancel. }
  (* loop 3: iterate and free *)
  Intros li.
  forward.
  { entailer!. apply (pn_all s 0 Hptr). }
  forward_call (Tsh, v_it, Ews, s, vs, 0).
  { repeat match goal with |- _ /\ _ => split end;
      first [apply at_node0 | assumption | (eapply prev_links_sub; eauto; lia) | auto]. }
  Intros vret. destruct vret as [[b f] r]. simpl fst in *; simpl snd in *.
  forward.
  forward_loop
    (EX b: Z, EX f: Z, EX c: Z, EX r: val,
     PROP (-1 <= b < f; f <= Zlength s;
           (r = nullval /\ b = -1 /\ f = Zlength s) \/
           (b < c < f /\ 0 <= c < Zlength s /\ r = Znth c s))
     LOCAL (temp _l r; temp _last (Vint li); gvars gv;
            lvar _the_list (tptr (Tstruct _dllist noattr)) v_the_list;
            lvar _it (Tstruct _sglib_dllist_iterator noattr) v_it)
     SEP (data_at Tsh (tptr t_dl) (Znth_or_null s 0) v_the_list;
          it_rep Tsh v_it s b f nullval nullval;
          nodes Ews s vs 0 (b+1); nodes Ews s vs f (Zlength s);
          toks s 0 (b+1); toks s f (Zlength s); cur vs c r;
          mem_mgr gv;
          data_at sh (tarray tint (Zlength il)) (map Vint il) inp))
  continue:
    (EX b: Z, EX f: Z,
     PROP (-1 <= b < f; f <= Zlength s)
     LOCAL (temp _last (Vint li); gvars gv;
            lvar _the_list (tptr (Tstruct _dllist noattr)) v_the_list;
            lvar _it (Tstruct _sglib_dllist_iterator noattr) v_it)
     SEP (data_at Tsh (tptr t_dl) (Znth_or_null s 0) v_the_list;
          it_rep Tsh v_it s b f nullval nullval;
          nodes Ews s vs 0 (b+1); nodes Ews s vs f (Zlength s);
          toks s 0 (b+1); toks s f (Zlength s);
          mem_mgr gv;
          data_at sh (tarray tint (Zlength il)) (map Vint il) inp))
  break:
    (PROP ()
     LOCAL (temp _last (Vint li); gvars gv;
            lvar _the_list (tptr (Tstruct _dllist noattr)) v_the_list;
            lvar _it (Tstruct _sglib_dllist_iterator noattr) v_it)
     SEP (data_at Tsh (tptr t_dl) (Znth_or_null s 0) v_the_list;
          it_rep Tsh v_it s (-1) (Zlength s) nullval nullval;
          mem_mgr gv;
          data_at sh (tarray tint (Zlength il)) (map Vint il) inp)).
  { match goal with Hw: init_window _ _ _ _ _ |- _ =>
      destruct Hw as [Hb [Hf [_ [_ Hex]]]] end.
    destruct (Hex eq_refl) as [[-> [-> [-> ->]]] | [c [Hc [-> [-> ->]]]]].
    - Exists (-1) 0 0 nullval. rewrite cur_null.
      entailer!.
    - Exists (c-1) (c+1) c (Znth c s).
      rewrite cur_ptr by (apply Hptr; lia).
      rewrite (nodes_focus Ews s vs 0 c (Zlength s)) by lia.
      rewrite (toks_split s 0 c (Zlength s)) by lia.
      rewrite (toks_split s c (c+1) (Zlength s)) by lia.
      rewrite toks_one by lia.
      replace (c-1+1) with c by lia.
      entailer!.
      right. split; [lia|]. split; [lia|auto]. }
  { Intros b0 f0 c r0.
    match goal with Hd: (_ = nullval /\ _) \/ _ |- _ =>
      destruct Hd as [[-> [-> ->]] | [Hc [Hc' ->]]] end.
    - rewrite cur_null.
      forward_if.
      { absurd_if. }
      forward.
      rewrite !nodes_empty by lia. rewrite !toks_empty by lia.
      entailer!.
    - assert (Hpc := Hptr c ltac:(lia)).
      rewrite cur_ptr by auto. Intros.
      forward_if.
      2:{ match goal with Hn: Znth c s = nullval |- _ => rewrite Hn in Hpc end.
          contradiction. }
      forward_call (t_dl, Znth c s, gv).
      { rewrite if_false by (intro Hx; rewrite Hx in Hpc; contradiction).
        cancel. }
      Exists b0 f0. entailer!. }
  { Intros b0 f0.
    forward_call (gv, Tsh, v_it, Ews, s, vs, b0, f0, nullval, nullval,
                  Ews, (Vundef, (Vundef, Vundef))).
    { rewrite cmp_env_null, cmp_state_null. cancel. }
    { repeat match goal with |- _ /\ _ => split end;
        first [ assumption | lia
              | (eapply prev_links_sub; eauto; lia)
              | (eapply next_links_sub; eauto; lia)
              | (left; reflexivity) | auto ]. }
    Intros vret. destruct vret as [[b' f'] r']. simpl fst in *; simpl snd in *.
    rewrite cmp_env_null, cmp_state_null.
    match goal with Hi: iter_step _ _ _ _ _ _ _ |- _ =>
      destruct Hi as [_ Hex] end.
    specialize (Hex eq_refl).
    forward.
    destruct Hex as [[-> [-> [-> [-> ->]]]] | [[Hb [-> [-> ->]]] | [Hf [-> [-> ->]]]]].
    - Exists (-1) (Zlength s) 0 nullval. rewrite cur_null. entailer!; fin_inv.
    - Exists (b0-1) f0 b0 (Znth b0 s).
      rewrite cur_ptr by (apply Hptr; lia).
      rewrite (nodes_split Ews s vs 0 b0 (b0+1)) by lia.
      rewrite nodes_one.
      rewrite (toks_split s 0 b0 (b0+1)) by lia.
      rewrite toks_one by lia.
      replace (b0-1+1) with b0 by lia.
      entailer!; fin_inv.
    - Exists b0 (f0+1) f0 (Znth f0 s).
      rewrite cur_ptr by (apply Hptr; lia).
      rewrite (nodes_split Ews s vs f0 (f0+1) (Zlength s)) by lia.
      rewrite nodes_one.
      rewrite (toks_split s f0 (f0+1) (Zlength s)) by lia.
      rewrite toks_one by lia.
      entailer!; fin_inv. }
  unfold it_rep. Intros cur0.
  forward.
  Exists li. entailer!.
Qed.

(* ================================================================== *)
(* main                                                               *)
(* ================================================================== *)

Lemma body_main: semax_body Vprog Gprog f_main main_spec.
Proof.
  start_function.
  sep_apply (create_mem_mgr gv).
  forward_call (gv, Ews, gv _input, input_contents, 5).
  { assert (Zlength input_contents = 5) by reflexivity. lia. }
  change (Zlength input_contents) with 5.
  forward.
  rewrite (sepcon_comm _ (data_at _ _ _ _)). rewrite sepcon_assoc. apply derives_refl.
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
