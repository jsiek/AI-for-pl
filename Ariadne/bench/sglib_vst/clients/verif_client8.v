Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import SglibVST.client8 SglibVST.spec_client8.
Require SglibVST.lib_client8.

Local Open Scope logic.

(* This program uses no comparator. *)
Definition Rc_client : globals -> val -> mpred := fun _ _ => emp.

#[export] Existing Instance NullExtension.Espec.

(* ================================================================== *)
(* Client-side predicates and lemmas                                  *)
(* ================================================================== *)

(* malloc tokens of nodes lo .. hi-1 *)
Fixpoint toks_list (l: list val) : mpred :=
  match l with
  | [] => emp
  | x :: r => malloc_token Ews t_dl x * toks_list r
  end.

Lemma toks_list_app: forall l1 l2,
  toks_list (l1 ++ l2) = toks_list l1 * toks_list l2.
Proof.
  induction l1; intros; simpl.
  - rewrite emp_sepcon. auto.
  - rewrite IHl1. rewrite sepcon_assoc. auto.
Qed.

Definition toks (s: list val) (lo hi: Z) : mpred :=
  toks_list (sublist lo hi s).

(* the node the loop is about to free (nothing when NULL) *)
Definition cur_node (l: val) : mpred :=
  if eq_dec l nullval then emp
  else (malloc_token Ews t_dl l * data_at_ Ews t_dl l).

Lemma toks_empty: forall s i, toks s i i = emp.
Proof. intros. unfold toks. rewrite sublist_nil. reflexivity. Qed.

Lemma toks_split: forall s lo m hi, 0 <= lo <= m -> m <= hi <= Zlength s ->
  toks s lo hi = toks s lo m * toks s m hi.
Proof.
  intros. unfold toks. rewrite (sublist_split lo m hi) by lia.
  apply toks_list_app.
Qed.

Lemma toks_empty2: forall s lo hi, hi <= lo -> toks s lo hi = emp.
Proof. intros. unfold toks. rewrite sublist_nil_gen by lia. reflexivity. Qed.

Lemma toks_one: forall s i, 0 <= i < Zlength s ->
  toks s i (i+1) = malloc_token Ews t_dl (Znth i s).
Proof.
  intros. unfold toks. rewrite sublist_len_1 by lia. simpl. apply sepcon_emp.
Qed.

Lemma toks_cons: forall e s,
  toks (e :: s) 0 (Zlength s + 1) = malloc_token Ews t_dl e * toks s 0 (Zlength s).
Proof.
  intros. unfold toks.
  rewrite sublist_same by list_solve.
  rewrite sublist_same by lia. reflexivity.
Qed.

Lemma ins0: forall {A} {d: Inhabitant A} (x: A) l, ins 0 x l = x :: l.
Proof.
  intros. unfold ins. rewrite sublist_nil. rewrite sublist_same by lia. reflexivity.
Qed.

Lemma Znth_or_null_nil: forall i, Znth_or_null [] i = nullval.
Proof. intros. apply lib_client8.Znth_or_null_out. rewrite Zlength_nil. lia. Qed.

Lemma Znth_or_null_cons0: forall (e: val) s, Znth_or_null (e :: s) 0 = e.
Proof.
  intros. rewrite lib_client8.Znth_or_null_in by (rewrite Zlength_cons; list_solve).
  apply Znth_0_cons.
Qed.

Lemma at_node0: forall s, at_node s 0.
Proof.
  intros. unfold at_node. destruct s.
  - left; auto.
  - right. rewrite Zlength_cons. list_solve.
Qed.

Lemma whole_nil: whole [] [].
Proof.
  unfold whole, prev_links, next_links. rewrite !Zlength_nil.
  split; auto. split; intros; lia.
Qed.

Lemma cmp_env_null: forall e sh v, cmp_env Rc_client nullval e sh v = emp.
Proof. intros. unfold cmp_env. rewrite if_true by auto. auto. Qed.

Lemma cmp_state_null: forall gv, cmp_state Rc_client gv nullval = emp.
Proof. intros. unfold cmp_state. rewrite if_true by auto. auto. Qed.

Lemma cur_node_null: cur_node nullval = emp.
Proof. unfold cur_node. rewrite if_true by auto. auto. Qed.

Lemma cur_node_intro: forall v p, isptr p ->
  data_at Ews t_dl v p * malloc_token Ews t_dl p |-- cur_node p.
Proof.
  intros. unfold cur_node.
  rewrite if_false by (intro; subst; contradiction).
  cancel.
Qed.

(* ================================================================== *)
(* Funspecs                                                           *)
(* ================================================================== *)

Definition build_spec :=
 DECLARE _build
  WITH gv: globals, shl: share, lp: val, ip: val, sh: share, contents: list int
  PRE [ tptr (tptr t_dl), tptr tint, tint ]
    PROP (writable_share shl; readable_share sh;
          Zlength contents <= Int.max_signed)
    PARAMS (lp; ip; Vint (Int.repr (Zlength contents))) GLOBALS (gv)
    SEP (mem_mgr gv;
         data_at sh (tarray tint (Zlength contents)) (map Vint contents) ip;
         data_at shl (tptr t_dl) nullval lp)
  POST [ tint ]
    EX s: list val, EX vs: list node_v,
    PROP (whole s vs)
    RETURN (Vint (Int.repr (Zlength s)))
    SEP (mem_mgr gv;
         data_at sh (tarray tint (Zlength contents)) (map Vint contents) ip;
         data_at shl (tptr t_dl) (Znth_or_null s 0) lp;
         nodes Ews s vs 0 (Zlength s); toks s 0 (Zlength s)).

Definition client_spec :=
 DECLARE _client
  WITH gv: globals, ip: val, sh: share, contents: list int
  PRE [ tptr tint, tint ]
    PROP (readable_share sh; Zlength contents <= Int.max_signed)
    PARAMS (ip; Vint (Int.repr (Zlength contents))) GLOBALS (gv)
    SEP (mem_mgr gv;
         data_at sh (tarray tint (Zlength contents)) (map Vint contents) ip)
  POST [ tvoid ]
    PROP () RETURN ()
    SEP (mem_mgr gv;
         data_at sh (tarray tint (Zlength contents)) (map Vint contents) ip).

Definition input_contents : list int := map Int.repr [6;7;3;4;7].

Definition main_spec :=
 DECLARE _main
  WITH gv: globals
  PRE [ ] main_pre prog tt gv
  POST [ tint ]
    PROP () RETURN (Vint (Int.repr 0))
    SEP (mem_mgr gv;
         data_at Ews (tarray tint 5) (map Vint input_contents) (gv _input);
         has_ext tt).

Definition Gprog : funspecs :=
  ltac:(with_library prog [add_spec; get_first_spec; get_last_spec;
                           it_init_on_equal_spec Rc_client; it_init_spec;
                           it_next_spec Rc_client;
                           build_spec; client_spec; main_spec]).

(* ================================================================== *)
(* Library functions: from lib_client8                                *)
(* ================================================================== *)

Lemma subVG: tycontext_subVG Vprog (SglibVST.spec_client8.Gprog Rc_client) Vprog Gprog.
Proof.
  split.
  - apply sub_option_get;
    let A1 := fresh "A1" in let A2 := fresh "A2" in
    set (A1 := make_tycontext_g Vprog (SglibVST.spec_client8.Gprog Rc_client));
    set (A2 := make_tycontext_g Vprog Gprog);
    compute in A1; compute in A2; subst A1 A2;
    repeat (apply Forall_cons; [reflexivity | ]); apply Forall_nil.
  - apply subsume_spec_get;
    let A1 := fresh "A1" in let A2 := fresh "A2" in
    set (A1 := make_tycontext_s (SglibVST.spec_client8.Gprog Rc_client));
    set (A2 := make_tycontext_s Gprog);
    let a := make_ground_PTree A1 in change A1 with a; clear A1;
    let a := make_ground_PTree A2 in change A2 with a; clear A2;
    repeat (apply Forall_cons; [apply subsumespec_refl | ]);
    apply Forall_nil.
Qed.

Ltac from_lib L :=
  eapply semax_body_subsumption; [apply L | apply tycontext_sub_i99; exact subVG].

Lemma body_add: semax_body Vprog Gprog f_sglib_dllist_add add_spec.
Proof. from_lib (lib_client8.body_add Rc_client). Qed.
Lemma body_get_first:
  semax_body Vprog Gprog f_sglib_dllist_get_first get_first_spec.
Proof. from_lib (lib_client8.body_get_first Rc_client). Qed.
Lemma body_get_last:
  semax_body Vprog Gprog f_sglib_dllist_get_last get_last_spec.
Proof. from_lib (lib_client8.body_get_last Rc_client). Qed.
Lemma body_it_init_on_equal:
  semax_body Vprog Gprog f_sglib_dllist_it_init_on_equal
    (it_init_on_equal_spec Rc_client).
Proof. from_lib (lib_client8.body_it_init_on_equal Rc_client). Qed.
Lemma body_it_init:
  semax_body Vprog Gprog f_sglib_dllist_it_init it_init_spec.
Proof. from_lib (lib_client8.body_it_init Rc_client). Qed.
Lemma body_it_next:
  semax_body Vprog Gprog f_sglib_dllist_it_next (it_next_spec Rc_client).
Proof. from_lib (lib_client8.body_it_next Rc_client). Qed.

(* ================================================================== *)
(* build                                                              *)
(* ================================================================== *)

Lemma body_build: semax_body Vprog Gprog f_build build_spec.
Proof.
  start_function.
  forward.
  forward_loop (EX k: Z, EX s: list val, EX vs: list node_v,
    PROP (0 <= k <= Zlength contents; Zlength s = k; whole s vs)
    LOCAL (temp _m (Vint (Int.repr k)); temp _k (Vint (Int.repr k));
           temp _list lp; temp _input__1 ip;
           temp _n (Vint (Int.repr (Zlength contents))); gvars gv)
    SEP (mem_mgr gv;
         data_at sh (tarray tint (Zlength contents)) (map Vint contents) ip;
         data_at shl (tptr t_dl) (Znth_or_null s 0) lp;
         nodes Ews s vs 0 k; toks s 0 k))
  continue: (EX k: Z, EX s: list val, EX vs: list node_v,
    PROP (0 <= k < Zlength contents; Zlength s = (k + 1)%Z; whole s vs)
    LOCAL (temp _m (Vint (Int.repr (k+1)%Z)); temp _k (Vint (Int.repr k));
           temp _list lp; temp _input__1 ip;
           temp _n (Vint (Int.repr (Zlength contents))); gvars gv)
    SEP (mem_mgr gv;
         data_at sh (tarray tint (Zlength contents)) (map Vint contents) ip;
         data_at shl (tptr t_dl) (Znth_or_null s 0) lp;
         nodes Ews s vs 0 (k+1)%Z; toks s 0 (k+1)%Z))
  break: (EX s: list val, EX vs: list node_v,
    PROP (whole s vs)
    LOCAL (temp _m (Vint (Int.repr (Zlength s))); gvars gv)
    SEP (mem_mgr gv;
         data_at sh (tarray tint (Zlength contents)) (map Vint contents) ip;
         data_at shl (tptr t_dl) (Znth_or_null s 0) lp;
         nodes Ews s vs 0 (Zlength s); toks s 0 (Zlength s))).
  - forward. Exists 0 (@nil val) (@nil node_v).
    rewrite Znth_or_null_nil, lib_client8.nodes_empty by lia. rewrite toks_empty.
    entailer!. apply whole_nil.
  - Intros k s vs.
    forward_if.
    2: { forward. Exists s vs. subst k. entailer!. }
    forward_call (t_dl, gv).
    Intros l.
    forward_if (PROP (l <> nullval)
      LOCAL (temp _l l; temp _m (Vint (Int.repr k)); temp _k (Vint (Int.repr k));
             temp _list lp; temp _input__1 ip;
             temp _n (Vint (Int.repr (Zlength contents))); gvars gv)
      SEP (mem_mgr gv; malloc_token Ews t_dl l; data_at_ Ews t_dl l;
           data_at sh (tarray tint (Zlength contents)) (map Vint contents) ip;
           data_at shl (tptr t_dl) (Znth_or_null s 0) lp;
           nodes Ews s vs 0 k; toks s 0 k)).
    + if_tac; entailer!.
    + rewrite if_true by auto. forward. Exists s vs. subst k. entailer!.
    + rewrite if_false by auto. forward. entailer!.
    + Intros.
      forward. forward.
      subst k.
      forward_call (shl, lp, Ews, l, Vint (Znth (Zlength s) contents), (Vundef, Vundef), s, vs, 0).
      { apply at_node0. }
      Intros vs'.
      rewrite ins0 in *.
      forward.
      Exists (Zlength s) (l :: s) vs'.
      rewrite Znth_or_null_cons0, toks_cons.
      entailer!.
      list_solve.
  - Intros k s vs. forward. Exists (k+1) s vs. entailer!.
  - Intros s vs. forward. Exists s vs. entailer!.
Qed.

(* ================================================================== *)
(* client                                                             *)
(* ================================================================== *)

Lemma body_client: semax_body Vprog Gprog f_client client_spec.
Proof.
  start_function.
  forward.
  change (Vlong (Int64.repr (Int.signed (Int.repr 0)))) with nullval.
  forward_call (gv, Tsh, v_list, ip, sh, contents).
  Intros sv. destruct sv as [s vs]. cbn [fst snd] in *.
  match goal with Hw: whole _ _ |- _ => pose proof Hw as [Hlen [Hp Hn]] end.
  assert_PROP (forall i, 0 <= i < Zlength s -> isptr (Znth i s)) as Hptr.
  { sep_apply (lib_client8.nodes_isptr Ews s vs 0 (Zlength s)). entailer!. }
  forward.
  { entailer!. apply (lib_client8.Znth_or_null_pn s 0 0 (Zlength s)); auto; lia. }
  forward_call (Tsh, v_it, Ews, s, vs, 0).
  { split; [apply at_node0 | eapply lib_client8.prev_links_sub; [exact Hp | lia | lia]]. }
  Intros vret. destruct vret as [[b f] r]. cbn [fst snd] in *.
  forward.
  forward_loop (EX b: Z, EX f: Z, EX l: val,
    PROP (-1 <= b < f; f <= Zlength s; l = nullval -> b = -1 /\ f = Zlength s)
    LOCAL (temp _l l; lvar _it (Tstruct _sglib_dllist_iterator noattr) v_it;
           lvar _list (tptr (Tstruct _dllist noattr)) v_list; gvars gv)
    SEP (mem_mgr gv;
         data_at sh (tarray tint (Zlength contents)) (map Vint contents) ip;
         data_at Tsh (tptr t_dl) (Znth_or_null s 0) v_list;
         it_rep Tsh v_it s b f nullval nullval;
         nodes Ews s vs 0 (b+1); toks s 0 (b+1);
         nodes Ews s vs f (Zlength s); toks s f (Zlength s); cur_node l))
  continue: (EX b: Z, EX f: Z,
    PROP (-1 <= b < f; f <= Zlength s)
    LOCAL (lvar _it (Tstruct _sglib_dllist_iterator noattr) v_it;
           lvar _list (tptr (Tstruct _dllist noattr)) v_list; gvars gv)
    SEP (mem_mgr gv;
         data_at sh (tarray tint (Zlength contents)) (map Vint contents) ip;
         data_at Tsh (tptr t_dl) (Znth_or_null s 0) v_list;
         it_rep Tsh v_it s b f nullval nullval;
         nodes Ews s vs 0 (b+1); toks s 0 (b+1);
         nodes Ews s vs f (Zlength s); toks s f (Zlength s)))
  break: (PROP ()
    LOCAL (lvar _it (Tstruct _sglib_dllist_iterator noattr) v_it;
           lvar _list (tptr (Tstruct _dllist noattr)) v_list; gvars gv)
    SEP (mem_mgr gv;
         data_at sh (tarray tint (Zlength contents)) (map Vint contents) ip;
         data_at Tsh (tptr t_dl) (Znth_or_null s 0) v_list;
         it_rep Tsh v_it s (-1) (Zlength s) nullval nullval;
         nodes Ews s vs 0 (-1+1); nodes Ews s vs (Zlength s) (Zlength s))).
  - destruct H1 as [Hbf [Hf [_ [Hnull Hex]]]]. specialize (Hex eq_refl).
    destruct Hex as [[-> [-> [-> ->]]] | [c [Hc [-> [-> ->]]]]].
    + Exists (-1) 0 nullval. rewrite cur_node_null.
      rewrite Zlength_nil in *.
      rewrite !lib_client8.nodes_empty by lia. rewrite !toks_empty2 by lia.
      entailer!.
    + Exists (c-1) (c+1) (Znth c s).
      replace (c-1+1) with c by lia.
      rewrite (lib_client8.nodes_focus Ews s vs 0 c (Zlength s)) by lia.
      rewrite (toks_split s 0 c (Zlength s)) by lia.
      rewrite (toks_split s c (c+1) (Zlength s)) by lia.
      rewrite toks_one by lia.
      sep_apply (cur_node_intro (Znth c vs) (Znth c s)); [apply Hptr; lia|].
      entailer!.
  - clear H1 b f r. Intros b f l.
    assert_PROP (is_pointer_or_null l).
    { unfold cur_node. destruct (eq_dec l nullval); entailer!. }
    forward_if.
    { unfold cur_node; destruct (eq_dec l nullval); entailer!. }
    { unfold cur_node. forward_call (t_dl, l, gv). Exists b f. entailer!. }
    { forward. destruct (H3 H5) as [-> ->]. subst l. rewrite cur_node_null.
      rewrite !toks_empty2 by lia. entailer!. }
  - clear H1 b f r. Intros b f.
    forward_call (gv, Tsh, v_it, Ews, s, vs, b, f, nullval, nullval, Ews, (Vundef, (Vundef, Vundef))).
    { rewrite cmp_env_null, cmp_state_null. cancel. }
    { split; [eapply lib_client8.prev_links_sub; [exact Hp | lia | lia] |].
      split; [eapply lib_client8.next_links_sub; [exact Hn | lia | lia] |].
      split; left; auto. }
    Intros vret. destruct vret as [[b' f'] r]. cbn [fst snd] in *.
    rewrite cmp_env_null, cmp_state_null.
    forward.
    match goal with Hs: iter_step _ _ _ _ _ _ _ |- _ => destruct Hs as [_ Hex] end.
    specialize (Hex eq_refl). unfold step_exact in Hex.
    destruct Hex as [[-> [-> [-> [-> ->]]]] | [[Hb0 [-> [-> ->]]] | [Hf0 [-> [-> ->]]]]].
    + Exists (-1) (Zlength s) nullval. rewrite cur_node_null. entailer!.
    + Exists (b-1) f (Znth b s).
      replace (b-1+1) with b by lia.
      rewrite (lib_client8.nodes_split Ews s vs 0 b (b+1)) by lia.
      rewrite lib_client8.nodes_one.
      rewrite (toks_split s 0 b (b+1)) by lia.
      rewrite toks_one by lia.
      sep_apply (cur_node_intro (Znth b vs) (Znth b s)); [apply Hptr; lia|].
      entailer!.
      match goal with Hz: Znth b s = nullval |- _ =>
        specialize (Hptr b ltac:(lia)); rewrite Hz in Hptr; contradiction end.
    + Exists b (f+1) (Znth f s).
      rewrite (lib_client8.nodes_split Ews s vs f (f+1) (Zlength s)) by lia.
      rewrite lib_client8.nodes_one.
      rewrite (toks_split s f (f+1) (Zlength s)) by lia.
      rewrite toks_one by lia.
      sep_apply (cur_node_intro (Znth f vs) (Znth f s)); [apply Hptr; lia|].
      entailer!.
      match goal with Hz: Znth f s = nullval |- _ =>
        specialize (Hptr f ltac:(lia)); rewrite Hz in Hptr; contradiction end.
  - clear H1 b f r.
    forward_call (gv, Tsh, v_it, Ews, s, vs, (-1)%Z, Zlength s, nullval, nullval, Ews, (Vundef, (Vundef, Vundef))).
    { rewrite cmp_env_null, cmp_state_null. cancel. }
    { split; [intros i Hi; lia |].
      split; [eapply lib_client8.next_links_sub;
              [exact Hn | pose proof (Zlength_nonneg s); lia | lia] |].
      split; left; auto. }
    Intros vret. destruct vret as [[b' f'] r]. cbn [fst snd] in *.
    rewrite cmp_env_null, cmp_state_null.
    unfold it_rep. Intros cur.
    rewrite !lib_client8.nodes_empty by lia.
    entailer!.
Qed.

Lemma body_main: semax_body Vprog Gprog f_main main_spec.
Proof.
  start_function.
  sep_apply (create_mem_mgr gv).
  forward_call (gv, gv _input, Ews, input_contents).
  { cbv; discriminate. }
  change (Zlength input_contents) with 5.
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
  semax_func_cons body_client.
  semax_func_cons body_main.
Qed.
