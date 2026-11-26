Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import SglibVST.client3 SglibVST.spec_client3.
Require SglibVST.lib_client3.

Local Open Scope logic.

(* This program uses no comparator. *)
Definition Rc_client : globals -> val -> mpred := fun _ _ => emp.

(* ================================================================== *)
(* Client predicates and lemmas                                       *)
(* ================================================================== *)

(* the malloc tokens of a sequence of nodes *)
Fixpoint toks (s: list val) : mpred :=
  match s with
  | [] => emp
  | p :: s' => malloc_token Ews t_dl p * toks s'
  end.

Lemma toks_nil: toks [] = emp.
Proof. reflexivity. Qed.

Lemma toks_cons: forall p s, toks (p :: s) = malloc_token Ews t_dl p * toks s.
Proof. reflexivity. Qed.

Lemma toks_app: forall s1 s2, toks (s1 ++ s2) = toks s1 * toks s2.
Proof.
  induction s1; intros; simpl.
  - rewrite emp_sepcon. auto.
  - rewrite IHs1. rewrite sepcon_assoc. auto.
Qed.

Lemma toks_last: forall s b, 0 <= b < Zlength s ->
  toks (sublist 0 (b+1) s) = toks (sublist 0 b s) * malloc_token Ews t_dl (Znth b s).
Proof.
  intros. rewrite (sublist_split 0 b (b+1)) by lia.
  rewrite toks_app. rewrite sublist_len_1 by lia. simpl.
  rewrite sepcon_emp. auto.
Qed.

Lemma toks_first: forall s f, 0 <= f < Zlength s ->
  toks (sublist f (Zlength s) s) =
  malloc_token Ews t_dl (Znth f s) * toks (sublist (f+1) (Zlength s) s).
Proof.
  intros. rewrite (sublist_split f (f+1) (Zlength s)) by lia.
  rewrite toks_app. rewrite sublist_len_1 by lia. simpl.
  rewrite sepcon_emp. auto.
Qed.

Lemma toks_focus: forall s c, 0 <= c < Zlength s ->
  toks s = toks (sublist 0 c s) * malloc_token Ews t_dl (Znth c s) *
           toks (sublist (c+1) (Zlength s) s).
Proof.
  intros.
  replace (toks s) with (toks (sublist 0 c s ++ sublist c (Zlength s) s))
    by (f_equal; rewrite <- sublist_split by lia; apply sublist_same; lia).
  rewrite toks_app. rewrite toks_first by lia. rewrite sepcon_assoc. auto.
Qed.

Lemma ins0: forall {A} {d: Inhabitant A} (x: A) l, ins 0 x l = x :: l.
Proof. intros. unfold ins. list_solve. Qed.

Lemma Znth_or_null_cons0: forall p s, Znth_or_null (p :: s) 0 = p.
Proof.
  intros. unfold Znth_or_null. rewrite Zlength_cons.
  destruct (zle 0 0); [|lia]. destruct (zlt 0 (Z.succ (Zlength s))); [|list_solve].
  apply Znth_0_cons.
Qed.

Lemma Znth_or_null_nil: forall j, Znth_or_null [] j = nullval.
Proof.
  intros. unfold Znth_or_null. rewrite Zlength_nil.
  destruct (zle 0 j); auto. destruct (zlt j 0); auto. lia.
Qed.

Lemma int_payloads_cons: forall vs vs' x,
  map pay vs' = Vint x :: map pay vs ->
  int_payloads vs 0 (Zlength vs) -> int_payloads vs' 0 (Zlength vs').
Proof.
  intros vs vs' x H H0 i Hi.
  assert (L: Zlength vs' = Zlength vs + 1).
  { apply (f_equal (@Zlength _)) in H.
    rewrite Zlength_map, Zlength_cons, Zlength_map in H. lia. }
  replace (pay (Znth i vs')) with (Znth i (map pay vs'))
    by (rewrite Znth_map; auto; lia).
  rewrite H. destruct (zeq i 0).
  - subst. rewrite Znth_0_cons. unfold int_val. exists x; auto.
  - rewrite Znth_pos_cons by lia. rewrite Znth_map by lia. apply H0; lia.
Qed.

Lemma cmp_env_null: forall Rc eqp sheq veq,
  cmp_env Rc nullval eqp sheq veq = emp.
Proof. intros. unfold cmp_env. rewrite if_true; auto. Qed.

Lemma cmp_state_null: forall Rc gv, cmp_state Rc gv nullval = emp.
Proof. intros. unfold cmp_state. rewrite if_true; auto. Qed.

(* the node the client holds during an iteration step (none when NULL) *)
Definition cur (l: val) (v: node_v) : mpred :=
  if eq_dec l nullval then emp
  else data_at Ews t_dl v l * malloc_token Ews t_dl l.

Lemma cur_null: forall v, cur nullval v = emp.
Proof. intros. unfold cur. rewrite if_true; auto. Qed.

Lemma cur_ptr: forall l v, l <> nullval ->
  cur l v = data_at Ews t_dl v l * malloc_token Ews t_dl l.
Proof. intros. unfold cur. rewrite if_false; auto. Qed.

Lemma isptr_neq_null:forall p, isptr p -> p <> nullval.
Proof. intros p H E. subst. simpl in H. contradiction. Qed.

Lemma whole_nil: whole [] [].
Proof.
  unfold whole, prev_links, next_links.
  split; [reflexivity|]. split; intros i Hi; rewrite Zlength_nil in Hi; lia.
Qed.

(* ================================================================== *)
(* Funspecs                                                           *)
(* ================================================================== *)

Definition build_spec :=
 DECLARE _build
  WITH gv: globals, lp: val, sh: share, inp: val, n: Z, contents: list Z
  PRE [ tptr (tptr t_dl), tptr tint, tint ]
    PROP (readable_share sh; 0 <= n <= Zlength contents;
          Zlength contents <= Int.max_signed)
    PARAMS (lp; inp; Vint (Int.repr n)) GLOBALS (gv)
    SEP (mem_mgr gv; data_at Ews (tptr t_dl) nullval lp;
         data_at sh (tarray tint (Zlength contents))
           (map Vint (map Int.repr contents)) inp)
  POST [ tint ]
    EX s: list val, EX vs: list node_v,
    PROP (whole s vs; int_payloads vs 0 (Zlength s); Zlength s <= n)
    RETURN (Vint (Int.repr (Zlength s)))
    SEP (mem_mgr gv; data_at Ews (tptr t_dl) (Znth_or_null s 0) lp;
         nodes Ews s vs 0 (Zlength s); toks s;
         data_at sh (tarray tint (Zlength contents))
           (map Vint (map Int.repr contents)) inp).

Definition client_spec :=
 DECLARE _client
  WITH gv: globals, sh: share, inp: val, n: Z, contents: list Z
  PRE [ tptr tint, tint ]
    PROP (readable_share sh; 0 <= n <= Zlength contents;
          Zlength contents <= Int.max_signed)
    PARAMS (inp; Vint (Int.repr n)) GLOBALS (gv)
    SEP (mem_mgr gv; data_at Ews (tptr t_dl) nullval (gv _the_list);
         data_at sh (tarray tint (Zlength contents))
           (map Vint (map Int.repr contents)) inp)
  POST [ tuint ]
    EX r: int,
    PROP ()
    RETURN (Vint r)
    SEP (mem_mgr gv; data_at Ews (tptr t_dl) nullval (gv _the_list);
         data_at sh (tarray tint (Zlength contents))
           (map Vint (map Int.repr contents)) inp).

Definition input_contents : list Z := [6; 7; 3; 4; 7].

Definition main_spec :=
 DECLARE _main
  WITH gv: globals
  PRE [ ] main_pre prog tt gv
  POST [ tint ]
    PROP ()
    RETURN (Vint (Int.repr 0))
    SEP (mem_mgr gv; has_ext tt;
         data_at Ews (tarray tint 5) (map Vint (map Int.repr input_contents))
           (gv _input);
         data_at Ews (tptr t_dl) nullval (gv _the_list)).

Definition Gprog : funspecs :=
  ltac:(with_library prog [add_spec; get_first_spec; get_last_spec;
                           it_init_on_equal_spec Rc_client; it_init_spec;
                           it_next_spec Rc_client;
                           build_spec; client_spec; main_spec]).

(* ================================================================== *)
(* The library functions, from lib_client3                            *)
(* ================================================================== *)

Lemma subVG: tycontext_subVG Vprog (SglibVST.spec_client3.Gprog Rc_client)
                             Vprog Gprog.
Proof.
  split.
  - apply sub_option_get.
    set (A1 := make_tycontext_g Vprog (SglibVST.spec_client3.Gprog Rc_client)).
    set (A2 := make_tycontext_g Vprog Gprog).
    compute in A1; compute in A2; subst A1 A2.
    repeat (apply Forall_cons; [reflexivity | ]); apply Forall_nil.
  - apply subsume_spec_get.
    set (A1 := make_tycontext_s (SglibVST.spec_client3.Gprog Rc_client)).
    set (A2 := make_tycontext_s Gprog).
    let a := make_ground_PTree A1 in change A1 with a; clear A1.
    let a := make_ground_PTree A2 in change A2 with a; clear A2.
    repeat (apply Forall_cons; [apply subsumespec_refl | ]).
    apply Forall_nil.
Qed.

Lemma body_add: semax_body Vprog Gprog f_sglib_dllist_add add_spec.
Proof.
  pose proof subVG.
  apply_semax_body (SglibVST.lib_client3.body_add Rc_client).
Qed.

Lemma body_get_first:
  semax_body Vprog Gprog f_sglib_dllist_get_first get_first_spec.
Proof.
  pose proof subVG.
  apply_semax_body (SglibVST.lib_client3.body_get_first Rc_client).
Qed.

Lemma body_get_last:
  semax_body Vprog Gprog f_sglib_dllist_get_last get_last_spec.
Proof.
  pose proof subVG.
  apply_semax_body (SglibVST.lib_client3.body_get_last Rc_client).
Qed.

Lemma body_it_init_on_equal:
  semax_body Vprog Gprog f_sglib_dllist_it_init_on_equal
    (it_init_on_equal_spec Rc_client).
Proof.
  pose proof subVG.
  apply_semax_body (SglibVST.lib_client3.body_it_init_on_equal Rc_client).
Qed.

Lemma body_it_init:
  semax_body Vprog Gprog f_sglib_dllist_it_init it_init_spec.
Proof.
  pose proof subVG.
  apply_semax_body (SglibVST.lib_client3.body_it_init Rc_client).
Qed.

Lemma body_it_next:
  semax_body Vprog Gprog f_sglib_dllist_it_next (it_next_spec Rc_client).
Proof.
  pose proof subVG.
  apply_semax_body (SglibVST.lib_client3.body_it_next Rc_client).
Qed.

(* ================================================================== *)
(* build                                                              *)
(* ================================================================== *)

Lemma body_build: semax_body Vprog Gprog f_build build_spec.
Proof.
  start_function.
  forward.
  forward_loop
    (EX k: Z, EX s: list val, EX vs: list node_v,
     PROP (0 <= k <= n; Zlength s <= k; whole s vs;
           int_payloads vs 0 (Zlength s))
     LOCAL (temp _m (Vint (Int.repr (Zlength s))); temp _k (Vint (Int.repr k));
            temp _list lp; temp _input__1 inp; temp _n (Vint (Int.repr n));
            gvars gv)
     SEP (mem_mgr gv; data_at Ews (tptr t_dl) (Znth_or_null s 0) lp;
          nodes Ews s vs 0 (Zlength s); toks s;
          data_at sh (tarray tint (Zlength contents))
            (map Vint (map Int.repr contents)) inp))
  continue:
    (EX k: Z, EX s: list val, EX vs: list node_v,
     PROP (0 <= k < n; Zlength s <= k + 1; whole s vs;
           int_payloads vs 0 (Zlength s))
     LOCAL (temp _m (Vint (Int.repr (Zlength s))); temp _k (Vint (Int.repr k));
            temp _list lp; temp _input__1 inp; temp _n (Vint (Int.repr n));
            gvars gv)
     SEP (mem_mgr gv; data_at Ews (tptr t_dl) (Znth_or_null s 0) lp;
          nodes Ews s vs 0 (Zlength s); toks s;
          data_at sh (tarray tint (Zlength contents))
            (map Vint (map Int.repr contents)) inp))
  break:
    (EX s: list val, EX vs: list node_v,
     PROP (whole s vs; int_payloads vs 0 (Zlength s); Zlength s <= n)
     LOCAL (temp _m (Vint (Int.repr (Zlength s))))
     SEP (mem_mgr gv; data_at Ews (tptr t_dl) (Znth_or_null s 0) lp;
          nodes Ews s vs 0 (Zlength s); toks s;
          data_at sh (tarray tint (Zlength contents))
            (map Vint (map Int.repr contents)) inp)).
  - (* entry *)
    forward.
    Exists 0 (@nil val) (@nil node_v).
    rewrite Znth_or_null_nil, toks_nil, Zlength_nil.
    rewrite SglibVST.lib_client3.nodes_empty by lia.
    entailer!.
    split; [apply whole_nil|]. intros i Hi; lia.
  - (* body *)
    Intros k s vs.
    forward_if.
    + forward_call (t_dl, gv).
      Intros l.
      forward_if.
      * if_tac; entailer!.
      * rewrite if_true by auto.
        forward.
        Exists s vs. entailer!.
      * rewrite if_false by auto.
        Intros.
        forward.
        forward.
        match goal with Hw: whole _ _ |- _ => destruct Hw as [Hlen [Hp Hn]] end.
        forward_call (Ews, lp, Ews, l, Vint (Int.repr (Znth k contents)),
                      (Vundef, Vundef), s, vs, 0).
        { split.
          - destruct s; [left; auto | right; rewrite Zlength_cons; list_solve].
          - split; auto. }
        Intros vs'.
        match goal with Hw: whole _ vs' |- _ => rename Hw into Hw' end.
        match goal with Hm: map pay vs' = _ |- _ => rename Hm into Hm' end.
        rewrite ins0 in *.
        forward.
        Exists k (l :: s) vs'.
        rewrite Znth_or_null_cons0, toks_cons, Zlength_cons.
        replace (Z.succ (Zlength s)) with (Zlength s + 1) by lia.
        entailer!.
        replace (Zlength s + 1) with (Zlength vs')
          by (destruct Hw' as [Hl' _]; rewrite Hl', Zlength_cons; lia).
        eapply int_payloads_cons with (vs := vs); [exact Hm' | rewrite Hlen; auto].
    + forward.
      Exists s vs. entailer!.
  - (* increment *)
    Intros k s vs.
    forward.
    Exists (k+1) s vs. entailer!.
  - Intros s vs.
    forward.
    Exists s vs. entailer!.
Qed.

(* ================================================================== *)
(* client                                                             *)
(* ================================================================== *)

Lemma body_client: semax_body Vprog Gprog f_client client_spec.
Proof.
  start_function.
  forward.
  forward_call (gv, gv _the_list, sh, inp, n, contents).
  Intros vret. destruct vret as [s vs]. simpl fst in *. simpl snd in *.
  match goal with Hw: whole _ _ |- _ => destruct Hw as [Hlen [Hp Hn]] end.
  match goal with H: int_payloads _ _ _ |- _ => rename H into Hpay end.
  assert_PROP (forall i, 0 <= i < Zlength s -> isptr (Znth i s)) as Hptr.
  { sep_apply (SglibVST.lib_client3.nodes_isptr Ews s vs 0 (Zlength s)).
    entailer!. }
  forward.
  { entailer!. apply (SglibVST.lib_client3.Znth_or_null_pn s 0 0 (Zlength s)); auto.
    destruct s; [right; left; rewrite Zlength_nil; lia| right; right; rewrite Zlength_cons; list_solve]. }
  forward_call (Tsh, v_it, Ews, s, vs, 0).
  { split.
    - destruct s; [left; auto | right; rewrite Zlength_cons; list_solve].
    - eapply SglibVST.lib_client3.prev_links_sub; eauto; lia. }
  Intros vret.
  destruct vret as [[b0 f0] r0]. simpl fst in *. simpl snd in *.
  match goal with H: init_window _ _ _ _ _ |- _ =>
    destruct H as [Hb0 [Hf0 [_ [_ Hex0]]]] end.
  specialize (Hex0 eq_refl).
  forward.
  forward_loop
    (EX b: Z, EX f: Z, EX l: val, EX c: Z, EX sm: int,
     PROP (-1 <= b < f; f <= Zlength s;
           (l = nullval /\ b = -1 /\ f = Zlength s) \/
           (b < c < f /\ 0 <= c < Zlength s /\ l = Znth c s))
     LOCAL (temp _l l; temp _sum (Vint sm); lvar _it t_it v_it; gvars gv;
            temp _input__1 inp; temp _n (Vint (Int.repr n)))
     SEP (it_rep Tsh v_it s b f nullval nullval;
          nodes Ews s vs 0 (b+1); nodes Ews s vs f (Zlength s);
          toks (sublist 0 (b+1) s); toks (sublist f (Zlength s) s);
          cur l (Znth c vs);
          mem_mgr gv; data_at Ews (tptr t_dl) (Znth_or_null s 0) (gv _the_list);
          data_at sh (tarray tint (Zlength contents))
            (map Vint (map Int.repr contents)) inp))
  continue:
    (EX b: Z, EX f: Z, EX sm: int,
     PROP (-1 <= b < f; f <= Zlength s)
     LOCAL (temp _sum (Vint sm); lvar _it t_it v_it; gvars gv;
            temp _input__1 inp; temp _n (Vint (Int.repr n)))
     SEP (it_rep Tsh v_it s b f nullval nullval;
          nodes Ews s vs 0 (b+1); nodes Ews s vs f (Zlength s);
          toks (sublist 0 (b+1) s); toks (sublist f (Zlength s) s);
          mem_mgr gv; data_at Ews (tptr t_dl) (Znth_or_null s 0) (gv _the_list);
          data_at sh (tarray tint (Zlength contents))
            (map Vint (map Int.repr contents)) inp))
  break:
    (EX sm: int,
     PROP ()
     LOCAL (temp _sum (Vint sm); lvar _it t_it v_it; gvars gv;
            temp _input__1 inp; temp _n (Vint (Int.repr n)))
     SEP (it_rep Tsh v_it s (-1) (Zlength s) nullval nullval;
          mem_mgr gv; data_at Ews (tptr t_dl) (Znth_or_null s 0) (gv _the_list);
          data_at sh (tarray tint (Zlength contents))
            (map Vint (map Int.repr contents)) inp)).
  - (* entry *)
    destruct Hex0 as [[Hr [Hs [Hb Hf]]] | [c [Hc [Hr [Hb Hf]]]]].
    + subst s r0 b0 f0.
      Exists (-1) 0 nullval 0 (Int.repr 0).
      rewrite cur_null.
      rewrite Zlength_nil.
      replace (-1+1) with 0 by lia.
      rewrite !SglibVST.lib_client3.nodes_empty by lia.
      autorewrite with sublist. simpl toks.
      entailer!.
    + subst r0 b0 f0.
      rewrite (SglibVST.lib_client3.nodes_focus Ews s vs 0 c (Zlength s)) by lia.
      rewrite (toks_focus s c) by lia.
      Exists (c-1) (c+1) (Znth c s) c (Int.repr 0).
      rewrite cur_ptr by (apply isptr_neq_null; apply Hptr; lia).
      replace (c-1+1) with c by lia.
      entailer!.
      right. split; [lia|split; [lia|auto]].
  - (* body *)
    Intros b f l c sm.
    match goal with H: _ \/ _ |- _ => rename H into Hl end.
    forward_if.
    + unfold cur. if_tac; entailer!.
    + destruct Hl as [[Hl _] | [Hc [Hc' Hl]]].
      { subst l. match goal with H: _ |- _ => solve [contradiction H; auto] end. }
      subst l.
      rewrite cur_ptr by (apply isptr_neq_null; apply Hptr; lia).
      assert (int_val (pay (Znth c vs))) as [iv Hiv] by (apply Hpay; lia).
      destruct (Znth c vs) as [pv [nv pp]] eqn:E.
      unfold pay in Hiv. simpl in Hiv. subst pv.
      Intros.
      forward.
      forward.
      forward_call (t_dl, Znth c s, gv).
      { rewrite if_false by (apply isptr_neq_null; apply Hptr; lia). cancel. }
      Exists b f (Int.add sm iv).
      entailer!.
    + destruct Hl as [[Hl [Hb Hf]] | [Hc [Hc' Hl]]].
      2:{ assert (isptr l) by (subst l; apply Hptr; lia).
          match goal with H: _ |- _ => solve [rewrite H in *; simpl in *; contradiction] end. }
      subst l b f.
      forward.
      Exists sm.
      rewrite cur_null.
      replace (-1+1) with 0 by lia.
      rewrite !SglibVST.lib_client3.nodes_empty by lia.
      autorewrite with sublist. simpl toks.
      entailer!.
  - (* it_next *)
    Intros b f sm.
    assert (prev_links s vs 0 (b+1))
      by (eapply SglibVST.lib_client3.prev_links_sub; eauto; lia).
    assert (next_links s vs f (Zlength s))
      by (eapply SglibVST.lib_client3.next_links_sub; eauto; lia).
    forward_call (gv, Tsh, v_it, Ews, s, vs, b, f, nullval, nullval, Ews,
                  (Vundef, (Vundef, Vundef))).
    { rewrite cmp_env_null, cmp_state_null. cancel. }
    { split; left; auto. }
    Intros vret.
    destruct vret as [[b' f'] r]. simpl fst in *. simpl snd in *.
    rewrite cmp_env_null, cmp_state_null.
    match goal with H: iter_step _ _ _ _ _ _ _ |- _ => destruct H as [_ Hex] end.
    specialize (Hex eq_refl). unfold step_exact in Hex.
    forward.
    destruct Hex as [[Hr [Hb [Hf [Hb' Hf']]]] | [[Hb [Hr [Hb' Hf']]] | [Hf [Hr [Hb' Hf']]]]].
    + subst r b' f' b f.
      Exists (-1) (Zlength s) nullval 0 sm.
      rewrite cur_null.
      entailer!.
    + subst r b' f'.
      rewrite (SglibVST.lib_client3.nodes_split Ews s vs 0 b (b+1)) by lia.
      rewrite SglibVST.lib_client3.nodes_one.
      rewrite toks_last by lia.
      Exists (b-1) f (Znth b s) b sm.
      rewrite cur_ptr by (apply isptr_neq_null; apply Hptr; lia).
      replace (b-1+1) with b by lia.
      entailer!.
      right. split; [lia|split; [lia|auto]].
    + subst r b' f'.
      rewrite (SglibVST.lib_client3.nodes_split Ews s vs f (f+1) (Zlength s)) by lia.
      rewrite SglibVST.lib_client3.nodes_one.
      rewrite toks_first by lia.
      Exists b (f+1) (Znth f s) f sm.
      rewrite cur_ptr by (apply isptr_neq_null; apply Hptr; lia).
      entailer!.
      right. split; [lia|split; [lia|auto]].
  - (* after the loop *)
    Intros sm.
    unfold it_rep. Intros cur0.
    forward.
    forward.
    Exists sm.
    entailer!.
Qed.

(* ================================================================== *)
(* main                                                               *)
(* ================================================================== *)

Lemma body_main: semax_body Vprog Gprog f_main main_spec.
Proof.
  start_function.
  sep_apply (create_mem_mgr gv).
  forward_call (gv, Ews, gv _input, 5, input_contents).
  { unfold input_contents. rewrite !Zlength_cons, Zlength_nil. rep_lia. }
  forward_call (gv, Ews, gv _input, 3, input_contents).
  { unfold input_contents. rewrite !Zlength_cons, Zlength_nil. rep_lia. }
  forward.
  unfold input_contents. simpl Zlength. cancel.
Qed.

#[export] Existing Instance NullExtension.Espec.

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
