Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import SglibVST.client1 SglibVST.spec_client1.
Require SglibVST.lib_client1.

Local Open Scope logic.

(* This program uses no comparator. *)
Definition Rc_client : globals -> val -> mpred := fun _ _ => emp.

(* ================================================================== *)
(* Helpers                                                            *)
(* ================================================================== *)

Fixpoint tokl (l: list val) : mpred :=
  match l with
  | [] => emp
  | p :: l' => malloc_token Ews t_dl p * tokl l'
  end.

Lemma iter_sepcon_app: forall l1 l2, tokl (l1 ++ l2) = tokl l1 * tokl l2.
Proof.
  induction l1; intros; simpl.
  - rewrite emp_sepcon; auto.
  - rewrite IHl1, sepcon_assoc; auto.
Qed.

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
  intros. unfold toks. rewrite sublist_one by lia. simpl. apply sepcon_emp.
Qed.

Lemma toks_empty: forall s i, toks s i i = emp.
Proof. intros. unfold toks. rewrite sublist_nil. reflexivity. Qed.

Lemma toks_emp: forall s lo hi, hi <= lo -> toks s lo hi = emp.
Proof. intros. unfold toks. rewrite sublist_nil_gen by lia. reflexivity. Qed.

Lemma toks_nil: forall lo hi, toks [] lo hi = emp.
Proof. intros. unfold toks. rewrite sublist_of_nil. reflexivity. Qed.

Lemma isptr_nonnull: forall p, isptr p -> p <> nullval.
Proof. intros. destruct p; try contradiction; discriminate. Qed.

Lemma ins0: forall {A} {d: Inhabitant A} (x: A) l, ins 0 x l = x :: l.
Proof. intros. unfold ins. autorewrite with sublist. reflexivity. Qed.

Lemma toks_cons: forall x s,
  toks (x :: s) 0 (Zlength s + 1) = malloc_token Ews t_dl x * toks s 0 (Zlength s).
Proof.
  intros. unfold toks.
  rewrite (sublist_same 0 (Zlength s + 1) (x :: s)) by list_solve.
  rewrite sublist_same by lia. reflexivity.
Qed.

Lemma toks_ins: forall j e s, 0 <= j <= Zlength s ->
  toks (ins j e s) 0 (Zlength s + 1) = toks s 0 (Zlength s) * malloc_token Ews t_dl e.
Proof.
  intros. unfold toks.
  rewrite (sublist_split 0 j (Zlength s) s) by lia.
  rewrite (sublist_same 0 (Zlength s + 1) (ins j e s))
    by (try reflexivity; rewrite SglibVST.lib_client1.Zlength_ins; lia).
  unfold ins. rewrite !iter_sepcon_app. simpl.
  apply pred_ext; cancel.
Qed.

Lemma Forall_ins: forall {A} {d: Inhabitant A} (P: A -> Prop) j x l,
  Forall P l -> P x -> Forall P (ins j x l).
Proof.
  intros. unfold ins. apply Forall_app. split.
  - apply Forall_sublist; auto.
  - constructor; auto. apply Forall_sublist; auto.
Qed.

Lemma whole_nil: whole [] [].
Proof.
  unfold whole, prev_links, next_links. split; [reflexivity|].
  split; intros i Hi; rewrite Zlength_nil in Hi; lia.
Qed.

Lemma In_Znth_ex: forall (l: list val) x, In x l ->
  exists i, 0 <= i < Zlength l /\ Znth i l = x.
Proof.
  induction l; simpl; intros x H; [contradiction|].
  destruct H as [<-|H].
  - exists 0. rewrite Zlength_cons. split.
    + pose proof (Zlength_nonneg l); lia.
    + apply Znth_0_cons.
  - destruct (IHl x H) as [i [Hi Hx]]. exists (i+1). rewrite Zlength_cons.
    split; [lia|]. rewrite Znth_pos_cons by lia.
    replace (i+1-1) with i by lia. auto.
Qed.

Lemma pay_int: forall vs i, Forall int_val (map pay vs) -> 0 <= i < Zlength vs ->
  int_val (pay (Znth i vs)).
Proof.
  intros. rewrite Forall_forall in H. apply H.
  rewrite <- Znth_map by auto. apply Znth_In. rewrite Zlength_map; auto.
Qed.

Lemma Znth_or_null_nil: forall i, Znth_or_null [] i = nullval.
Proof.
  intros. apply SglibVST.lib_client1.Znth_or_null_out. rewrite Zlength_nil. lia.
Qed.

Lemma nodes_nil: forall sh vs lo hi, hi <= lo -> nodes sh [] vs lo hi = emp.
Proof. intros. apply SglibVST.lib_client1.nodes_empty. auto. Qed.

(* ================================================================== *)
(* Funspecs                                                           *)
(* ================================================================== *)

Definition build_spec :=
 DECLARE _build
  WITH gv: globals, lp: val, sh: share, inp: val, n: Z, contents: list int
  PRE [ tptr (tptr t_dl), tptr tint, tint ]
    PROP (readable_share sh; 0 <= n <= Int.max_signed; Zlength contents = n)
    PARAMS (lp; inp; Vint (Int.repr n)) GLOBALS (gv)
    SEP (mem_mgr gv; data_at sh (tarray tint n) (map Vint contents) inp;
         data_at Tsh (tptr t_dl) nullval lp)
  POST [ tint ]
    EX s: list val, EX vs: list node_v,
    PROP (whole s vs; Forall int_val (map pay vs); Zlength s <= n)
    RETURN (Vint (Int.repr (Zlength s)))
    SEP (mem_mgr gv; data_at sh (tarray tint n) (map Vint contents) inp;
         data_at Tsh (tptr t_dl) (Znth_or_null s 0) lp;
         nodes Ews s vs 0 (Zlength s); toks s 0 (Zlength s)).

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
  WITH gv: globals, sh: share, inp: val, n: Z, contents: list int
  PRE [ tptr tint, tint ]
    PROP (readable_share sh; 0 <= n <= Int.max_signed; Zlength contents = n)
    PARAMS (inp; Vint (Int.repr n)) GLOBALS (gv)
    SEP (mem_mgr gv; data_at sh (tarray tint n) (map Vint contents) inp)
  POST [ tuint ]
    EX r: int,
    PROP () RETURN (Vint r)
    SEP (mem_mgr gv; data_at sh (tarray tint n) (map Vint contents) inp).

Definition input_contents : list int := map Int.repr [6; 7; 3; 4; 7].

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
                           build_spec; free_all_spec; client_spec; main_spec]).

#[export] Existing Instance NullExtension.Espec.

(* ================================================================== *)
(* Library functions, from lib_client1                                *)
(* ================================================================== *)

Lemma subVG: tycontext_subVG Vprog (SglibVST.spec_client1.Gprog Rc_client) Vprog Gprog.
Proof.
  split.
  - apply sub_option_get.
    set (A1 := make_tycontext_g Vprog (SglibVST.spec_client1.Gprog Rc_client)).
    set (A2 := make_tycontext_g Vprog Gprog).
    compute in A1; compute in A2; subst A1 A2.
    repeat (apply Forall_cons; [reflexivity | ]); apply Forall_nil.
  - apply subsume_spec_get.
    set (A1 := make_tycontext_s (SglibVST.spec_client1.Gprog Rc_client)).
    set (A2 := make_tycontext_s Gprog).
    let a := make_ground_PTree A1 in change A1 with a; clear A1.
    let a := make_ground_PTree A2 in change A2 with a; clear A2.
    repeat (apply Forall_cons; [apply subsumespec_refl | ]).
    apply Forall_nil.
Qed.

Lemma body_add: semax_body Vprog Gprog f_sglib_dllist_add add_spec.
Proof. pose proof subVG. apply_semax_body (SglibVST.lib_client1.body_add Rc_client). Qed.
Lemma body_get_first: semax_body Vprog Gprog f_sglib_dllist_get_first get_first_spec.
Proof. pose proof subVG. apply_semax_body (SglibVST.lib_client1.body_get_first Rc_client). Qed.
Lemma body_get_last: semax_body Vprog Gprog f_sglib_dllist_get_last get_last_spec.
Proof. pose proof subVG. apply_semax_body (SglibVST.lib_client1.body_get_last Rc_client). Qed.
Lemma body_it_init_on_equal: semax_body Vprog Gprog f_sglib_dllist_it_init_on_equal
  (it_init_on_equal_spec Rc_client).
Proof. pose proof subVG. apply_semax_body (SglibVST.lib_client1.body_it_init_on_equal Rc_client). Qed.
Lemma body_it_init: semax_body Vprog Gprog f_sglib_dllist_it_init it_init_spec.
Proof. pose proof subVG. apply_semax_body (SglibVST.lib_client1.body_it_init Rc_client). Qed.
Lemma body_it_next: semax_body Vprog Gprog f_sglib_dllist_it_next (it_next_spec Rc_client).
Proof. pose proof subVG. apply_semax_body (SglibVST.lib_client1.body_it_next Rc_client). Qed.

Local Notation find_id := VST.veric.initial_world.find_id.
Lemma lib_specs_agree:
  find_id _sglib_dllist_add Gprog = find_id _sglib_dllist_add (SglibVST.spec_client1.Gprog Rc_client) /\
  find_id _sglib_dllist_get_first Gprog = find_id _sglib_dllist_get_first (SglibVST.spec_client1.Gprog Rc_client) /\
  find_id _sglib_dllist_get_last Gprog = find_id _sglib_dllist_get_last (SglibVST.spec_client1.Gprog Rc_client) /\
  find_id _sglib_dllist_it_init_on_equal Gprog = find_id _sglib_dllist_it_init_on_equal (SglibVST.spec_client1.Gprog Rc_client) /\
  find_id _sglib_dllist_it_init Gprog = find_id _sglib_dllist_it_init (SglibVST.spec_client1.Gprog Rc_client) /\
  find_id _sglib_dllist_it_next Gprog = find_id _sglib_dllist_it_next (SglibVST.spec_client1.Gprog Rc_client).
Proof. repeat split; reflexivity. Qed.

(* ================================================================== *)
(* Client functions                                                   *)
(* ================================================================== *)

Lemma body_build: semax_body Vprog Gprog f_build build_spec.
Proof.
  start_function.
  forward.
  try forward.
  forward_loop (EX k: Z, EX s: list val, EX vs: list node_v,
    PROP (0 <= k <= n; Zlength s = k; whole s vs; Forall int_val (map pay vs))
    LOCAL (temp _m (Vint (Int.repr k)); temp _k (Vint (Int.repr k));
           temp _list lp; temp _input__1 inp; temp _n (Vint (Int.repr n));
           gvars gv)
    SEP (mem_mgr gv; data_at sh (tarray tint n) (map Vint contents) inp;
         data_at Tsh (tptr t_dl) (Znth_or_null s 0) lp;
         nodes Ews s vs 0 k; toks s 0 k))
  continue: (EX k: Z, EX s: list val, EX vs: list node_v,
    PROP ((0 <= k < n)%Z; Zlength s = (k + 1)%Z; whole s vs; Forall int_val (map pay vs))
    LOCAL (temp _m (Vint (Int.repr (k + 1))); temp _k (Vint (Int.repr k));
           temp _list lp; temp _input__1 inp; temp _n (Vint (Int.repr n));
           gvars gv)
    SEP (mem_mgr gv; data_at sh (tarray tint n) (map Vint contents) inp;
         data_at Tsh (tptr t_dl) (Znth_or_null s 0) lp;
         nodes Ews s vs 0 (k + 1); toks s 0 (k + 1)))
  break: (EX s: list val, EX vs: list node_v,
    PROP ((Zlength s <= n)%Z; whole s vs; Forall int_val (map pay vs))
    LOCAL (temp _m (Vint (Int.repr (Zlength s))))
    SEP (mem_mgr gv; data_at sh (tarray tint n) (map Vint contents) inp;
         data_at Tsh (tptr t_dl) (Znth_or_null s 0) lp;
         nodes Ews s vs 0 (Zlength s); toks s 0 (Zlength s))).
  forward.
  - Exists 0 (@nil val) (@nil node_v).
    rewrite Znth_or_null_nil, nodes_nil, toks_empty by lia.
    entailer!. apply whole_nil.
  - Intros k s vs.
    forward_if.
    + forward_call (t_dl, gv).
      Intros l.
      forward_if.
      { if_tac; entailer!. }
      * subst l. rewrite if_true by auto.
        forward. Exists s vs. entailer!.
      * rewrite if_false by auto. Intros.
        forward.
        forward.
        subst k.
        forward_call (Tsh, lp, Ews, l, Vint (Znth (Zlength s) contents), snd (default_val t_dl), s, vs, 0%Z).
        { destruct s; [left; auto | right; list_solve]. }
        Intros vs'.
        forward.
        rewrite ins0 in *.
        Exists (Zlength s) (l :: s) vs'.
        rewrite (SglibVST.lib_client1.Znth_or_null_in (l :: s) 0) by list_solve.
        rewrite toks_cons. rewrite Znth_0_cons.
        entailer!.
        { split; [list_solve|].
          match goal with Hm: map pay vs' = _ |- _ => rewrite Hm end.
          constructor; auto. eexists; reflexivity. }
    + forward. Exists s vs. entailer!.
  - Intros k s vs. forward. Exists (k + 1) s vs. entailer!.
  - Intros s vs. forward. Exists s vs. entailer!.
Qed.

Lemma body_free_all: semax_body Vprog Gprog f_free_all free_all_spec.
Proof.
  start_function.
  rename H into Hwh, H0 into Hat.
  assert (Hwh' := Hwh). destruct Hwh' as [Hlen [Hprev Hnext]].
  assert (Hj: 0 <= j <= Zlength s).
  { destruct Hat as [[-> ->]|?]; [rewrite Zlength_nil; lia | lia]. }
  assert_PROP (forall i, 0 <= i < Zlength s -> isptr (Znth i s)) as Hp.
  { sep_apply (SglibVST.lib_client1.nodes_isptr Ews s vs 0 (Zlength s)). entailer!. }
  forward_call (Tsh, v_it, Ews, s, vs, j).
  { repeat split; auto;
    first [ apply (SglibVST.lib_client1.prev_links_sub s vs 0 (Zlength s)); auto; lia
          | apply (SglibVST.lib_client1.next_links_sub s vs 0 (Zlength s)); auto; lia ]. }
  Intros vret. destruct vret as [[b0 f0] r0]. simpl fst in *. simpl snd in *.
  match goal with Hw: init_window _ _ _ _ _ |- _ => rename Hw into Hiw end.
  forward_loop (EX b: Z, EX f: Z, EX l: val,
    PROP ((-1 <= b < f)%Z; (f <= Zlength s)%Z;
          (l = nullval /\ b = -1 /\ f = Zlength s) \/
          ((exists c, b < c < f /\ l = Znth c s) /\ isptr l))
    LOCAL (temp _l l; lvar _it t_it v_it; gvars gv)
    SEP (it_rep Tsh v_it s b f nullval nullval;
         nodes Ews s vs 0 (b+1); nodes Ews s vs f (Zlength s);
         toks s 0 (b+1); toks s f (Zlength s);
         if eq_dec l nullval then emp
         else (malloc_token Ews t_dl l * data_at_ Ews t_dl l);
         mem_mgr gv))
  continue: (EX b: Z, EX f: Z,
    PROP ((-1 <= b < f)%Z; (f <= Zlength s)%Z)
    LOCAL (lvar _it t_it v_it; gvars gv)
    SEP (it_rep Tsh v_it s b f nullval nullval;
         nodes Ews s vs 0 (b+1); nodes Ews s vs f (Zlength s);
         toks s 0 (b+1); toks s f (Zlength s);
         mem_mgr gv))
  break: (EX b: Z, EX f: Z,
    PROP ()
    LOCAL (lvar _it t_it v_it; gvars gv)
    SEP (it_rep Tsh v_it s b f nullval nullval; mem_mgr gv)).
  - unfold init_window in Hiw.
    destruct Hiw as [Hb [Hf [_ [_ Hx]]]]. specialize (Hx eq_refl).
    destruct Hx as [[Hr [Hs [Hb' Hf']]] | [c [Hc [Hr [Hb' Hf']]]]].
    + subst. Exists (-1) 0 nullval. rewrite if_true by auto.
      rewrite !SglibVST.lib_client1.nodes_empty by (rewrite ?Zlength_nil; lia).
      rewrite !toks_nil.
      entailer!.
    + subst r0 b0 f0. Exists (c-1) (c+1) (Znth c s).
      replace (c-1+1) with c by lia.
      rewrite (SglibVST.lib_client1.nodes_focus Ews s vs 0 c (Zlength s)) by lia.
      rewrite (toks_split s 0 c (Zlength s)) by lia.
      rewrite (toks_split s c (c+1) (Zlength s)) by lia.
      rewrite toks_one by lia.
      rewrite if_false by (apply isptr_nonnull; apply Hp; lia).
      entailer!.
      { right. split; [exists c; split; [lia | auto] | apply Hp; lia]. }
  - Intros b f l.
    forward_if.
    { if_tac; entailer!. }
    + forward_call (t_dl, l, gv).
      Exists b f. entailer!.
    + forward.
      match goal with Hd: (l = nullval /\ _) \/ _ |- _ => destruct Hd as [[_ [-> ->]] | [_ Hpl]] end.
      2:{ subst l. contradiction. }
      Exists (-1) (Zlength s). rewrite if_true by auto.
      rewrite !SglibVST.lib_client1.nodes_empty by lia.
      rewrite !toks_emp by lia.
      entailer!.
  - Intros b f.
    forward_call (gv, Tsh, v_it, Ews, s, vs, b, f, nullval, nullval, Tsh, (Vundef, (Vundef, Vundef))).
    { unfold cmp_env, cmp_state. rewrite !if_true by auto. cancel. }
    { repeat split; auto;
      first [ apply (SglibVST.lib_client1.prev_links_sub s vs 0 (Zlength s)); auto; lia
            | apply (SglibVST.lib_client1.next_links_sub s vs 0 (Zlength s)); auto; lia
            | left; auto ]. }
    Intros vret. destruct vret as [[b' f'] r]. simpl fst in *. simpl snd in *.
    forward.
    unfold cmp_env, cmp_state. rewrite !if_true by auto.
    match goal with Hs: iter_step _ _ _ _ _ _ _ |- _ => rename Hs into Hst end.
    unfold iter_step in Hst. destruct Hst as [_ Hex].
    specialize (Hex eq_refl).
    destruct Hex as [[Hr [Hb1 [Hf1 [Hb2 Hf2]]]] | [[Hb0 [Hr [Hb2 Hf2]]] | [Hf0 [Hr [Hb2 Hf2]]]]].
    + subst. Exists (-1) (Zlength s) nullval. rewrite if_true by auto.
      entailer!.
    + subst b' f' r. Exists (b-1) f (Znth b s).
      replace (b-1+1) with b by lia.
      rewrite (SglibVST.lib_client1.nodes_split Ews s vs 0 b (b+1)) by lia.
      rewrite SglibVST.lib_client1.nodes_one.
      rewrite (toks_split s 0 b (b+1)) by lia.
      rewrite toks_one by lia.
      rewrite if_false by (apply isptr_nonnull; apply Hp; lia).
      entailer!.
      { right. split; [exists b; split; [lia | auto] | apply Hp; lia]. }
    + subst b' f' r. Exists b (f+1) (Znth f s).
      rewrite (SglibVST.lib_client1.nodes_split Ews s vs f (f+1) (Zlength s)) by lia.
      rewrite SglibVST.lib_client1.nodes_one.
      rewrite (toks_split s f (f+1) (Zlength s)) by lia.
      rewrite toks_one by lia.
      rewrite if_false by (apply isptr_nonnull; apply Hp; lia).
      entailer!.
      { right. split; [exists f; split; [lia | auto] | apply Hp; lia]. }
  - Intros b f.
    unfold abbreviate in POSTCONDITION. subst POSTCONDITION.
    simpl RA_normal.
    match goal with |- ENTAIL ?D, ?P |-- (fun rho => @?Q rho * stackframe_of ?fn rho) =>
      change (ENTAIL D, P |-- PROPx [] (LOCALx [] (SEPx [mem_mgr gv])) * stackframe_of fn) end.
    unfold it_rep. Intros cur.
    entailer!.
Qed.

Ltac pfin c jm0 Hp :=
  repeat first [ progress intros | split | lia
               | solve [left; repeat split; auto; lia]
               | solve [right; split; [exists c; split; [lia | auto] | apply Hp; lia]]
               | solve [exists jm0; split; [lia | auto]]
               | solve [auto] ].

Lemma body_client: semax_body Vprog Gprog f_client client_spec.
Proof.
  start_function.
  forward. forward. forward.
  forward_call (gv, v_list, sh, inp, n, contents).
  Intros vret. destruct vret as [s vs]. simpl fst in *. simpl snd in *.
  match goal with H: whole s vs |- _ => rename H into Hwh end.
  match goal with H: Forall int_val _ |- _ => rename H into Hint end.
  match goal with H: Zlength s <= n |- _ => rename H into Hsn end.
  assert (Hwh' := Hwh). destruct Hwh' as [Hlen [Hprev Hnext]].
  assert_PROP (forall i, 0 <= i < Zlength s -> isptr (Znth i s)) as Hp.
  { sep_apply (SglibVST.lib_client1.nodes_isptr Ews s vs 0 (Zlength s)). entailer!. }
  try forward.
  forward_if.
  { (* cnt == 0: the list is empty *)
    assert (Hz: Zlength s = 0).
    { auto. }
    rewrite Hz.
    rewrite (SglibVST.lib_client1.Znth_or_null_out s 0) by lia.
    rewrite SglibVST.lib_client1.nodes_empty by lia. rewrite toks_empty.
    forward.
    Exists (Int.repr 0). entailer!. }
  assert (Hs0: 0 < Zlength s).
  { pose proof (Zlength_nonneg s).
    first [ lia
          | match goal with H: Int.repr _ <> Int.repr 0 |- _ =>
              destruct (zeq (Zlength s) 0) as [Hz|]; [rewrite Hz in H; contradiction | lia] end ]. }
  rewrite (SglibVST.lib_client1.Znth_or_null_in s 0) by lia.
  assert (Hp0: isptr (Znth 0 s)) by (apply Hp; lia).
  do 3 (forward; try solve [entailer!; destruct (Znth 0 s); try contradiction; simpl; auto]).
  forward_call (Tsh, v_it, Ews, s, vs, 0).
  { rewrite (SglibVST.lib_client1.Znth_or_null_in s 0) by lia. entailer!. }
  { split; [right; lia|].
    apply (SglibVST.lib_client1.prev_links_sub s vs 0 (Zlength s)); auto; lia. }
  Intros vret. destruct vret as [[b0 f0] r0]. simpl fst in *. simpl snd in *.
  match goal with Hw: init_window _ _ _ _ _ |- _ => rename Hw into Hiw end.
  try forward.
  (* first iteration: find the middle node *)
  forward_loop (EX b: Z, EX f: Z, EX l: val, EX k: Z, EX mm: val,
    PROP ((-1 <= b < f)%Z; (f <= Zlength s)%Z;
          (l = nullval /\ b = -1 /\ f = Zlength s) \/
          ((exists c, b < c < f /\ l = Znth c s) /\ isptr l);
          (l <> nullval -> k = f - b - 2)%Z; (0 <= k <= Zlength s)%Z;
          exists jm, (0 <= jm < Zlength s)%Z /\ mm = Znth jm s)
    LOCAL (temp _l l; temp _k (Vint (Int.repr k)); temp _m mm;
           temp _h (Znth 0 s); temp _cnt (Vint (Int.repr (Zlength s)));
           temp _sum (Vint (Int.repr 0));
           lvar _list (tptr t_dl) v_list; lvar _it t_it v_it; gvars gv)
    SEP (it_rep Tsh v_it s b f nullval nullval;
         nodes Ews s vs 0 (Zlength s); toks s 0 (Zlength s);
         data_at Tsh (tptr t_dl) (Znth 0 s) v_list; mem_mgr gv;
         data_at sh (tarray tint n) (map Vint contents) inp))
  continue: (EX b: Z, EX f: Z, EX k: Z, EX mm: val,
    PROP ((-1 <= b < f)%Z; (f <= Zlength s)%Z; (k = f - b - 1)%Z;
          exists jm, (0 <= jm < Zlength s)%Z /\ mm = Znth jm s)
    LOCAL (temp _k (Vint (Int.repr k)); temp _m mm;
           temp _h (Znth 0 s); temp _cnt (Vint (Int.repr (Zlength s)));
           temp _sum (Vint (Int.repr 0));
           lvar _list (tptr t_dl) v_list; lvar _it t_it v_it; gvars gv)
    SEP (it_rep Tsh v_it s b f nullval nullval;
         nodes Ews s vs 0 (Zlength s); toks s 0 (Zlength s);
         data_at Tsh (tptr t_dl) (Znth 0 s) v_list; mem_mgr gv;
         data_at sh (tarray tint n) (map Vint contents) inp))
  break: (EX b: Z, EX f: Z, EX mm: val,
    PROP (exists jm, (0 <= jm < Zlength s)%Z /\ mm = Znth jm s)
    LOCAL (temp _m mm;
           temp _h (Znth 0 s); temp _sum (Vint (Int.repr 0));
           lvar _list (tptr t_dl) v_list; lvar _it t_it v_it; gvars gv)
    SEP (it_rep Tsh v_it s b f nullval nullval;
         nodes Ews s vs 0 (Zlength s); toks s 0 (Zlength s);
         data_at Tsh (tptr t_dl) (Znth 0 s) v_list; mem_mgr gv;
         data_at sh (tarray tint n) (map Vint contents) inp)).
  - unfold init_window in Hiw.
    destruct Hiw as [Hb [Hf [_ [_ Hx]]]]. specialize (Hx eq_refl).
    destruct Hx as [[Hr [Hs [Hb' Hf']]] | [c [Hc [Hr [Hb' Hf']]]]].
    { subst s. rewrite Zlength_nil in Hs0. lia. }
    subst r0 b0 f0. Exists (c-1) (c+1) (Znth c s) 0 (Znth 0 s).
    entailer!.
    repeat first [ progress intros | split | lia
                 | solve [right; split; [exists c; split; [lia | auto] | apply Hp; lia]]
                 | solve [exists 0; split; [lia | auto]] | solve [auto] ].
  - Intros b f l k mm.
    match goal with H: (l = nullval /\ _) \/ _ |- _ => rename H into Hd end.
    match goal with H: l <> nullval -> _ |- _ => rename H into Hk end.
    match goal with H: exists jm, _ /\ mm = _ |- _ => rename H into Hmm end.
    forward_if.
    { destruct Hd as [[-> _] | [[c [Hc ->]] _]].
      - entailer!.
      - rewrite (SglibVST.lib_client1.nodes_focus Ews s vs 0 c (Zlength s)) by lia.
        entailer!. }
    + destruct Hd as [[? _] | [[c [Hc Hl]] Hpl]]; [contradiction|].
      specialize (Hk ltac:(auto)).
      forward_if (EX mm2: val,
        PROP (exists jm, (0 <= jm < Zlength s)%Z /\ mm2 = Znth jm s)
        LOCAL (temp _l l; temp _k (Vint (Int.repr k)); temp _m mm2;
               temp _h (Znth 0 s); temp _cnt (Vint (Int.repr (Zlength s)));
               temp _sum (Vint (Int.repr 0));
               lvar _list (tptr t_dl) v_list; lvar _it t_it v_it; gvars gv)
        SEP (it_rep Tsh v_it s b f nullval nullval;
             nodes Ews s vs 0 (Zlength s); toks s 0 (Zlength s);
             data_at Tsh (tptr t_dl) (Znth 0 s) v_list; mem_mgr gv;
             data_at sh (tarray tint n) (map Vint contents) inp)).
      { apply prop_right. intros [_ Hm]. apply (f_equal Int.signed) in Hm.
        rewrite Int.signed_repr in Hm by rep_lia. rewrite Int.signed_mone in Hm. lia. }
      * forward. Exists l. entailer!. exists c. split; [lia | auto].
      * forward. Exists mm. entailer!.
      * Intros mm2.
        assert (Hk1: 0 <= k + 1 <= Int.max_signed) by rep_lia.
        forward.
        Exists b f (k+1) mm2. entailer!.
    + forward.
      Exists b f mm. entailer!.
  - Intros b f k mm.
    match goal with H: exists jm, _ /\ mm = _ |- _ => destruct H as [jm0 [Hjm0 Hmm0]] end.
    rewrite (SglibVST.lib_client1.nodes_split Ews s vs 0 (b+1) (Zlength s)) by lia.
    rewrite (SglibVST.lib_client1.nodes_split Ews s vs (b+1) f (Zlength s)) by lia.
    forward_call (gv, Tsh, v_it, Ews, s, vs, b, f, nullval, nullval, Tsh, (Vundef, (Vundef, Vundef))).
    { unfold cmp_env, cmp_state. rewrite !if_true by auto. cancel. }
    { repeat split; auto;
      first [ apply (SglibVST.lib_client1.prev_links_sub s vs 0 (Zlength s)); auto; lia
            | apply (SglibVST.lib_client1.next_links_sub s vs 0 (Zlength s)); auto; lia
            | left; auto ]. }
    Intros vret. destruct vret as [[b' f'] r]. simpl fst in *. simpl snd in *.
    forward.
    unfold cmp_env, cmp_state. rewrite !if_true by auto.
    match goal with Hs: iter_step _ _ _ _ _ _ _ |- _ => rename Hs into Hst end.
    unfold iter_step in Hst. destruct Hst as [_ Hex].
    specialize (Hex eq_refl).
    rewrite (SglibVST.lib_client1.nodes_split Ews s vs 0 (b+1) (Zlength s)) by lia.
    rewrite (SglibVST.lib_client1.nodes_split Ews s vs (b+1) f (Zlength s)) by lia.
    destruct Hex as [[Hr [Hb1 [Hf1 [Hb2 Hf2]]]] | [[Hb0 [Hr [Hb2 Hf2]]] | [Hf0 [Hr [Hb2 Hf2]]]]].
    + subst b' f' r. subst b f.
      Exists (-1) (Zlength s) nullval k mm.
      entailer!.
      pfin 0 jm0 Hp.
    + subst b' f' r. Exists (b-1) f (Znth b s) k mm.
      entailer!.
      pfin b jm0 Hp.
    + subst b' f' r. Exists b (f+1) (Znth f s) k mm.
      entailer!.
      pfin f jm0 Hp.
  - (* after the first iteration *)
    Intros b f mm.
    match goal with H: exists jm, _ /\ mm = _ |- _ => destruct H as [jm [Hjm ->]] end.
    forward_call (t_dl, gv).
    Intros e.
    forward_if (EX s2: list val, EX vs2: list node_v, EX jh: Z,
      PROP (whole s2 vs2; Forall int_val (map pay vs2); (0 <= jh < Zlength s2)%Z;
            Znth 0 s = Znth jh s2)
      LOCAL (temp _h (Znth 0 s); temp _sum (Vint (Int.repr 0));
             lvar _list (tptr t_dl) v_list; lvar _it t_it v_it; gvars gv)
      SEP (it_rep Tsh v_it s b f nullval nullval;
           nodes Ews s2 vs2 0 (Zlength s2); toks s2 0 (Zlength s2);
           data_at_ Tsh (tptr t_dl) v_list; mem_mgr gv;
           data_at sh (tarray tint n) (map Vint contents) inp)).
    { if_tac; entailer!. }
    + rewrite if_false by auto. Intros.
      forward. forward.
      rewrite <- (SglibVST.lib_client1.Znth_or_null_in s jm) by lia.
      forward_call (Tsh, v_list, Ews, e, Vint (Int.repr 0), snd (default_val t_dl), s, vs, jm).
      { right; lia. }
      Intros vs'.
      match goal with H: map pay vs' = _ |- _ => rename H into Hm end.
      assert (Hjh: Znth 0 s = Znth (if zeq jm 0 then 1 else 0) (ins jm e s)).
      { destruct (zeq jm 0).
        - subst jm. rewrite SglibVST.lib_client1.Znth_ins by lia. simpl. reflexivity.
        - rewrite SglibVST.lib_client1.Znth_ins by lia.
          destruct (zlt 0 jm); [reflexivity | lia]. }
      assert (Hf': Forall int_val (map pay vs')).
      { rewrite Hm. apply Forall_ins; auto. eexists; reflexivity. }
      Exists (ins jm e s) vs' (if zeq jm 0 then 1 else 0).
      rewrite SglibVST.lib_client1.Zlength_ins by lia.
      rewrite toks_ins by lia.
      sep_apply (data_at_data_at_ Tsh (tptr t_dl) e v_list).
      entailer!.
      destruct (zeq jm 0); lia.
    + forward. Exists s vs 0. rewrite if_true by auto.
      sep_apply (data_at_data_at_ Tsh (tptr t_dl) (Znth 0 s) v_list).
      entailer!.
    + Intros s2 vs2 jh.
      match goal with H: whole s2 vs2 |- _ => rename H into Hwh2 end.
      match goal with H: Forall int_val (map pay vs2) |- _ => rename H into Hint2 end.
      match goal with H: Znth 0 s = Znth jh s2 |- _ => rename H into Hh end.
      assert (Hwh2' := Hwh2). destruct Hwh2' as [Hlen2 [Hprev2 Hnext2]].
      assert_PROP (forall i, 0 <= i < Zlength s2 -> isptr (Znth i s2)) as Hp2.
      { sep_apply (SglibVST.lib_client1.nodes_isptr Ews s2 vs2 0 (Zlength s2)). entailer!. }
      rewrite Hh.
      rewrite <- (SglibVST.lib_client1.Znth_or_null_in s2 jh) by lia.
      assert (Emin: jh + 1 = Z.min (jh + 1) (Zlength s2)) by lia.
      rewrite (SglibVST.lib_client1.nodes_split Ews s2 vs2 0 (jh+1) (Zlength s2)) by lia.
      rewrite Emin.
      forward_call (Ews, s2, vs2, jh).
      { cancel. }
      { split; [right; lia|].
        apply (SglibVST.lib_client1.prev_links_sub s2 vs2 0 (Zlength s2)); auto; lia. }
      Intros r.
      rewrite <- Emin.
      try forward.
      forward_loop (EX i: Z, EX sumv: int,
        PROP ((0 <= i <= Zlength s2)%Z)
        LOCAL (temp _l (Znth_or_null s2 i); temp _sum (Vint sumv);
               temp _h (Znth_or_null s2 jh);
               lvar _list (tptr t_dl) v_list; lvar _it t_it v_it; gvars gv)
        SEP (it_rep Tsh v_it s b f nullval nullval;
             nodes Ews s2 vs2 0 (Zlength s2); toks s2 0 (Zlength s2);
             data_at_ Tsh (tptr t_dl) v_list; mem_mgr gv;
             data_at sh (tarray tint n) (map Vint contents) inp))
      continue: (EX i: Z, EX sumv: int,
        PROP ((0 <= i < Zlength s2)%Z)
        LOCAL (temp _l (Znth i s2); temp _sum (Vint sumv);
               temp _h (Znth_or_null s2 jh);
               lvar _list (tptr t_dl) v_list; lvar _it t_it v_it; gvars gv)
        SEP (it_rep Tsh v_it s b f nullval nullval;
             nodes Ews s2 vs2 0 (Zlength s2); toks s2 0 (Zlength s2);
             data_at_ Tsh (tptr t_dl) v_list; mem_mgr gv;
             data_at sh (tarray tint n) (map Vint contents) inp))
      break: (EX sumv: int,
        PROP ()
        LOCAL (temp _sum (Vint sumv);
               temp _h (Znth_or_null s2 jh);
               lvar _list (tptr t_dl) v_list; lvar _it t_it v_it; gvars gv)
        SEP (it_rep Tsh v_it s b f nullval nullval;
             nodes Ews s2 vs2 0 (Zlength s2); toks s2 0 (Zlength s2);
             data_at_ Tsh (tptr t_dl) v_list; mem_mgr gv;
             data_at sh (tarray tint n) (map Vint contents) inp)).
      * rewrite (SglibVST.lib_client1.nodes_split Ews s2 vs2 0 (jh+1) (Zlength s2)) by lia.
        match goal with H: r = nullval \/ In r s2 |- _ => destruct H as [Hr | Hr] end.
        -- subst r. Exists (Zlength s2) (Int.repr 0).
           rewrite (SglibVST.lib_client1.Znth_or_null_out s2 (Zlength s2)) by lia.
           entailer!.
        -- destruct (In_Znth_ex s2 r Hr) as [i [Hi Hri]].
           Exists i (Int.repr 0).
           rewrite (SglibVST.lib_client1.Znth_or_null_in s2 i) by lia.
           rewrite Hri. entailer!.
      * Intros i sumv.
        forward_if.
        { destruct (zlt i (Zlength s2)).
          - rewrite (SglibVST.lib_client1.Znth_or_null_in s2 i) by lia.
            rewrite (SglibVST.lib_client1.nodes_focus Ews s2 vs2 0 i (Zlength s2)) by lia.
            entailer!.
          - rewrite (SglibVST.lib_client1.Znth_or_null_out s2 i) by lia.
            entailer!. }
        -- assert (Hi: i < Zlength s2).
           { destruct (zlt i (Zlength s2)); auto.
             rewrite (SglibVST.lib_client1.Znth_or_null_out s2 i) in * by lia.
             contradiction. }
           rewrite (SglibVST.lib_client1.Znth_or_null_in s2 i) by lia.
           destruct (pay_int vs2 i Hint2 ltac:(lia)) as [x Hx].
           rewrite (SglibVST.lib_client1.nodes_focus Ews s2 vs2 0 i (Zlength s2)) by lia.
           destruct (Znth i vs2) as [pi [ni qi]] eqn:Ei.
           unfold pay in Hx; simpl in Hx. subst pi.
           Intros.
           forward. forward.
           Exists i (Int.add sumv x).
           entailer!.
        -- forward. Exists sumv. entailer!.
      * Intros i sumv.
        assert (Hn: nxt (Znth i vs2) = Znth_or_null s2 (i+1)) by (apply Hnext2; lia).
        rewrite (SglibVST.lib_client1.nodes_focus Ews s2 vs2 0 i (Zlength s2)) by lia.
        destruct (Znth i vs2) as [pi [ni qi]] eqn:Ei.
        unfold nxt in Hn; simpl in Hn. subst ni.
        Intros.
        forward.
        { entailer!. apply (SglibVST.lib_client1.Znth_or_null_pn _ _ _ _ Hp2); lia. }
        Exists (i+1) sumv.
        rewrite (SglibVST.lib_client1.nodes_focus Ews s2 vs2 0 i (Zlength s2)) by lia.
        rewrite Ei.
        entailer!.
      * Intros sumv.
        forward_call (gv, s2, vs2, jh).
        { first [ (right; lia) | (split; [auto | right; lia]) ]. }
        unfold it_rep. Intros cur.
        forward.
        Exists sumv. entailer!.
Qed.

Lemma body_main: semax_body Vprog Gprog f_main main_spec.
Proof.
  start_function.
  sep_apply (create_mem_mgr gv).
  forward_call (gv, Ews, gv _input, 5, input_contents).
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
  semax_func_cons body_client.
  semax_func_cons body_main.
Qed.
