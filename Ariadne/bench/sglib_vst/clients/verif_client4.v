Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import SglibVST.client4 SglibVST.spec_client4.
Require SglibVST.lib_client4.

Local Open Scope logic.

(* This program uses no comparator. *)
Definition Rc_client : globals -> val -> mpred := fun _ _ => emp.

#[export] Existing Instance NullExtension.Espec.

Definition t_holder := Tstruct _holder noattr.

(* the malloc tokens of a sequence of nodes *)
Fixpoint toks (s: list val) : mpred :=
  match s with
  | [] => emp
  | p :: s' => malloc_token Ews t_dl p * toks s'
  end.

Lemma toks_app: forall a b, toks (a ++ b) = toks a * toks b.
Proof.
  induction a; intros; simpl.
  - rewrite emp_sepcon; auto.
  - rewrite IHa, sepcon_assoc; auto.
Qed.

Definition build_spec :=
 DECLARE _build
  WITH gv: globals, lp: val, shi: share, inp: val, il: list int
  PRE [ tptr (tptr t_dl), tptr tint, tint ]
    PROP (readable_share shi; Zlength il <= Int.max_signed)
    PARAMS (lp; inp; Vint (Int.repr (Zlength il))) GLOBALS (gv)
    SEP (mem_mgr gv; data_at Ews (tptr t_dl) nullval lp;
         data_at shi (tarray tint (Zlength il)) (map Vint il) inp)
  POST [ tint ]
    EX s: list val, EX vs: list node_v,
    PROP (whole s vs; int_payloads vs 0 (Zlength s);
          Zlength s <= Zlength il)
    RETURN (Vint (Int.repr (Zlength s)))
    SEP (mem_mgr gv; data_at Ews (tptr t_dl) (Znth_or_null s 0) lp;
         nodes Ews s vs 0 (Zlength s); toks s;
         data_at shi (tarray tint (Zlength il)) (map Vint il) inp).

Definition client_spec :=
 DECLARE _client
  WITH gv: globals, shi: share, inp: val, il: list int
  PRE [ tptr tint, tint ]
    PROP (readable_share shi; Zlength il <= Int.max_signed)
    PARAMS (inp; Vint (Int.repr (Zlength il))) GLOBALS (gv)
    SEP (mem_mgr gv;
         data_at shi (tarray tint (Zlength il)) (map Vint il) inp)
  POST [ tuint ]
    EX r: int,
    PROP ()
    RETURN (Vint r)
    SEP (mem_mgr gv;
         data_at shi (tarray tint (Zlength il)) (map Vint il) inp).

Definition input_vals : list int :=
  map Int.repr [6; 7; 3; 4; 7].

Definition main_spec :=
 DECLARE _main
  WITH gv: globals
  PRE [ ] main_pre prog tt gv
  POST [ tint ]
    PROP ()
    RETURN (Vint (Int.repr 0))
    SEP (mem_mgr gv;
         data_at Ews (tarray tint 5) (map Vint input_vals) (gv _input);
         has_ext tt).

Definition Gprog : funspecs :=
  ltac:(with_library prog [add_spec;get_first_spec;
                           get_last_spec; it_init_on_equal_spec Rc_client;
                           it_init_spec; it_next_spec Rc_client;
                           build_spec; client_spec; main_spec]).

(* ================================================================== *)
(* Library functions, from lib_client4                                *)
(* ================================================================== *)

Lemma sub_Gprog: tycontext_subVG Vprog (SglibVST.spec_client4.Gprog Rc_client)
                                 Vprog Gprog.
Proof.
  split.
  - apply sub_option_get.
    let A1 := fresh "A1" in let A2 := fresh "A2" in
    set (A1 := make_tycontext_g Vprog (SglibVST.spec_client4.Gprog Rc_client));
    set (A2 := make_tycontext_g Vprog Gprog);
    compute in A1; compute in A2; subst A1 A2;
    repeat (apply Forall_cons; [reflexivity | ]); apply Forall_nil.
  - apply subsume_spec_get.
    let A1 := fresh "A1" in let A2 := fresh "A2" in
    set (A1 := make_tycontext_s (SglibVST.spec_client4.Gprog Rc_client));
    set (A2 := make_tycontext_s Gprog);
    let a := make_ground_PTree A1 in change A1 with a; clear A1;
    let a := make_ground_PTree A2 in change A2 with a; clear A2;
    repeat (apply Forall_cons; [apply subsumespec_refl | ]); apply Forall_nil.
Qed.

Lemma body_add: semax_body Vprog Gprog f_sglib_dllist_add add_spec.
Proof.
  eapply semax_body_subsumption;
    [apply (SglibVST.lib_client4.body_add Rc_client)|].
  apply tycontext_sub_i99; apply sub_Gprog.
Qed.

Lemma body_get_first:
  semax_body Vprog Gprog f_sglib_dllist_get_first get_first_spec.
Proof.
  eapply semax_body_subsumption;
    [apply (SglibVST.lib_client4.body_get_first Rc_client)|].
  apply tycontext_sub_i99; apply sub_Gprog.
Qed.

Lemma body_get_last:
  semax_body Vprog Gprog f_sglib_dllist_get_last get_last_spec.
Proof.
  eapply semax_body_subsumption;
    [apply (SglibVST.lib_client4.body_get_last Rc_client)|].
  apply tycontext_sub_i99; apply sub_Gprog.
Qed.

Lemma body_it_init_on_equal:
  semax_body Vprog Gprog f_sglib_dllist_it_init_on_equal
    (it_init_on_equal_spec Rc_client).
Proof.
  eapply semax_body_subsumption;
    [apply SglibVST.lib_client4.body_it_init_on_equal|].
  apply tycontext_sub_i99; apply sub_Gprog.
Qed.

Lemma body_it_init:
  semax_body Vprog Gprog f_sglib_dllist_it_init it_init_spec.
Proof.
  eapply semax_body_subsumption;
    [apply (SglibVST.lib_client4.body_it_init Rc_client)|].
  apply tycontext_sub_i99; apply sub_Gprog.
Qed.

Lemma body_it_next:
  semax_body Vprog Gprog f_sglib_dllist_it_next (it_next_spec Rc_client).
Proof.
  eapply semax_body_subsumption;
    [apply SglibVST.lib_client4.body_it_next|].
  apply tycontext_sub_i99; apply sub_Gprog.
Qed.

Goal forall i, In i [_sglib_dllist_add; _sglib_dllist_get_first;
     _sglib_dllist_get_last; _sglib_dllist_it_init_on_equal;
     _sglib_dllist_it_init; _sglib_dllist_it_next] ->
  initial_world.find_id i Gprog =
  initial_world.find_id i (SglibVST.spec_client4.Gprog Rc_client).
Proof.
  intros i H; simpl in H; repeat destruct H as [<-|H]; [reflexivity..|contradiction].
Qed.

(* ================================================================== *)
(* build                                                              *)
(* ================================================================== *)

Lemma ins0: forall {A} {d: Inhabitant A} (e: A) s, ins 0 e s = e :: s.
Proof. intros. unfold ins. list_solve. Qed.

Lemma whole_nil: whole [] [].
Proof.
  unfold whole, prev_links, next_links. split3; auto; intros; list_solve.
Qed.

Lemma int_payloads_cons: forall vs vs' x k,
  Zlength vs = k -> Zlength vs' = k + 1 ->
  int_payloads vs 0 k ->
  map pay vs' = Vint x :: map pay vs ->
  int_payloads vs' 0 (k + 1).
Proof.
  unfold int_payloads; intros.
  replace (pay (Znth i vs')) with (Znth i (map pay vs'))
    by (rewrite Znth_map by lia; auto).
  rewrite H2. destruct (zeq i 0).
  - subst. rewrite Znth_0_cons. exists x; auto.
  - rewrite Znth_pos_cons by lia. rewrite Znth_map by lia. apply H1. lia.
Qed.

Lemma body_build: semax_body Vprog Gprog f_build build_spec.
Proof.
  start_function.
  forward. (* m = 0 *)
  forward_loop
   (EX k: Z, EX s: list val, EX vs: list node_v,
    PROP (0 <= k <= Zlength il; Zlength s = k; whole s vs;
          int_payloads vs 0 k)
    LOCAL (temp _m (Vint (Int.repr k)); temp _k (Vint (Int.repr k));
           temp _list lp; temp _input__1 inp;
           temp _n (Vint (Int.repr (Zlength il))); gvars gv)
    SEP (mem_mgr gv; data_at Ews (tptr t_dl) (Znth_or_null s 0) lp;
         nodes Ews s vs 0 k; toks s;
         data_at shi (tarray tint (Zlength il)) (map Vint il) inp))
  continue:
   (EX k: Z, EX s: list val, EX vs: list node_v,
    PROP (0 <= k < Zlength il; Zlength s = (k + 1)%Z; whole s vs;
          int_payloads vs 0 (k + 1)%Z)
    LOCAL (temp _m (Vint (Int.repr (k + 1)%Z)); temp _k (Vint (Int.repr k));
           temp _list lp; temp _input__1 inp;
           temp _n (Vint (Int.repr (Zlength il))); gvars gv)
    SEP (mem_mgr gv; data_at Ews (tptr t_dl) (Znth_or_null s 0) lp;
         nodes Ews s vs 0 (k + 1)%Z; toks s;
         data_at shi (tarray tint (Zlength il)) (map Vint il) inp))
  break:
   (EX s: list val, EX vs: list node_v,
    PROP (whole s vs; int_payloads vs 0 (Zlength s);
          Zlength s <= Zlength il)
    LOCAL (temp _m (Vint (Int.repr (Zlength s))))
    SEP (mem_mgr gv; data_at Ews (tptr t_dl) (Znth_or_null s 0) lp;
         nodes Ews s vs 0 (Zlength s); toks s;
         data_at shi (tarray tint (Zlength il)) (map Vint il) inp)).
  - forward.
    Exists 0 (@nil val) (@nil node_v).
    entailer!.
    split; [apply whole_nil|]. unfold int_payloads; intros; lia.
  - Intros k s vs.
    forward_if.
    + forward_call (t_dl, gv).
      Intros l.
      forward_if.
      * if_tac; entailer!.
      * forward. Exists s vs. entailer!.
      * rewrite if_false by auto. Intros.
        forward. (* t'2 = input[k] *)
        forward. (* l->i = t'2 *)
        forward_call (Ews, lp, Ews, l, Vint (Znth k il), (Vundef, Vundef),
                      s, vs, 0).
        { subst k. cancel. }
        { unfold at_node. destruct s; [left; auto | right; list_solve]. }
        Intros vs'.
        rewrite !ins0 in *.
        forward. (* m++ *)
        Exists k (l :: s) vs'.
        assert (HL: Zlength vs' = Zlength s + 1)
          by (destruct H6 as [HL _]; rewrite HL, Zlength_cons; lia).
        assert (HP: int_payloads vs' 0 (k + 1)).
        { apply (int_payloads_cons vs vs' (Znth k il) k); auto;
            [destruct H2; lia | lia]. }
        assert (HZ: Znth_or_null (l :: s) 0 = l).
        { rewrite SglibVST.lib_client4.Znth_or_null_in by list_solve.
          apply Znth_0_cons. }
        rewrite HZ. subst k. simpl toks.
        entailer!.
        rewrite Zlength_cons; auto.
    + forward. Exists s vs. entailer!.
  - Intros k s vs.
    forward.
    Exists (k + 1) s vs. entailer!.
  - Intros s vs.
    forward.
    Exists s vs. entailer!.
Qed.

(* ================================================================== *)
(* client                                                             *)
(* ================================================================== *)

Definition node_opt (l: val) (v: node_v) : mpred :=
  if Val.eq l nullval then emp
  else data_at Ews t_dl v l * malloc_token Ews t_dl l.

Lemma toks_split_last: forall s b, 0 <= b < Zlength s ->
  toks (sublist 0 (b+1) s) =
  toks (sublist 0 b s) * malloc_token Ews t_dl (Znth b s).
Proof.
  intros. rewrite (sublist_split 0 b (b+1)) by lia.
  rewrite toks_app, sublist_len_1 by lia. simpl. rewrite sepcon_emp. auto.
Qed.

Lemma toks_split_first: forall s f, 0 <= f < Zlength s ->
  toks (sublist f (Zlength s) s) =
  malloc_token Ews t_dl (Znth f s) * toks (sublist (f+1) (Zlength s) s).
Proof.
  intros. rewrite (sublist_split f (f+1)) by lia.
  rewrite toks_app, sublist_len_1 by lia. simpl. rewrite sepcon_emp. auto.
Qed.

Lemma toks_focus: forall s c, 0 <= c < Zlength s ->
  toks s = toks (sublist 0 c s) * malloc_token Ews t_dl (Znth c s) *
           toks (sublist (c+1) (Zlength s) s).
Proof.
  intros. rewrite <- (sublist_same 0 (Zlength s) s) at 1 by auto.
  rewrite (sublist_split 0 c (Zlength s)) by lia.
  rewrite toks_app, toks_split_first by lia. rewrite sepcon_assoc. auto.
Qed.

Definition head_at (sp v: val) : mpred :=
  field_at Ews t_holder (DOT _head) v sp.

Lemma holder_back: forall sp v w,
  head_at sp v *
  data_at Ews t_it w (field_address t_holder (DOT _it) sp)
  |-- data_at_ Ews t_holder sp.
Proof.
  intros. unfold head_at.
  unfold_data_at (data_at_ _ _ _).
  rewrite (field_at_data_at Ews t_holder (DOT _it)).
  simpl nested_field_type.
  cancel.
Qed.

Lemma head_pn: forall s vs,
  nodes Ews s vs 0 (Zlength s) |-- !! is_pointer_or_null (Znth_or_null s 0).
Proof.
  intros.
  assert_PROP (forall i, 0 <= i < Zlength s -> isptr (Znth i s)) as Hp
    by apply SglibVST.lib_client4.nodes_isptr.
  entailer!.
  destruct (zlt 0 (Zlength s)).
  - rewrite SglibVST.lib_client4.Znth_or_null_in by lia.
    specialize (Hp 0 ltac:(lia)).
    destruct (Znth 0 s); try contradiction; simpl; auto.
  - rewrite SglibVST.lib_client4.Znth_or_null_out by lia. simpl; auto.
Qed.

Ltac close_props :=
  first
    [ split; [lia | reflexivity]
    | split; intros Hz;
      [ exfalso;
        match goal with Hp: isptr ?p |- _ =>
          rewrite Hz in Hp; simpl in Hp; contradiction end
      | split; [lia | reflexivity] ] ].

Lemma body_client:semax_body Vprog Gprog f_client client_spec.
Proof.
  start_function.
  forward_call (t_holder, gv).
  Intros sp.
  forward. (* sum = 0 *)
  forward_if
    (PROP (sp <> nullval)
     LOCAL (temp _s sp; temp _sum (Vint (Int.repr 0)); temp _input__1 inp;
            temp _n (Vint (Int.repr (Zlength il))); gvars gv)
     SEP (mem_mgr gv; malloc_token Ews t_holder sp; data_at_ Ews t_holder sp;
          data_at shi (tarray tint (Zlength il)) (map Vint il) inp)).
  - if_tac; entailer!.
  - forward. Exists (Int.repr 0). entailer!.
  - rewrite if_false by auto. forward. entailer!.
  - Intros.
    unfold_data_at (data_at_ _ _ _).
    forward. (* s->head = NULL *)
    replace (Vlong (Int64.repr (Int.signed (Int.repr 0)))) with nullval
      by reflexivity.
    assert_PROP (field_compatible t_holder (DOT _head) sp) by entailer!.
    rewrite (field_at_data_at Ews t_holder (DOT _head)).
    forward_call (gv, field_address t_holder (DOT _head) sp, shi, inp, il).
    { entailer!. simpl. f_equal.
      rewrite field_compatible_field_address by auto. reflexivity. }
    Intros vret. destruct vret as [s vs]. cbn [fst snd] in *.
    destruct H2 as [Hlen [Hprev Hnext]].
    change (data_at Ews (tptr t_dl) (Znth_or_null s 0)
              (field_address t_holder (DOT _head) sp))
      with (data_at Ews (nested_field_type t_holder (DOT _head))
              (Znth_or_null s 0) (field_address t_holder (DOT _head) sp)).
    rewrite <- field_at_data_at.
    assert_PROP (is_pointer_or_null (Znth_or_null s 0))
      by (sep_apply (head_pn s vs); entailer!).
    forward. (* t'5 = s->head *)
    assert_PROP (field_compatible t_holder (DOT _it) sp) by entailer!.
    sep_apply (field_at_field_at_ Ews t_holder (DOT _it)).
    rewrite (field_at__data_at_ Ews t_holder (DOT _it)).
    change (nested_field_type t_holder (DOT _it)) with t_it.
    forward_call (Ews, field_address t_holder (DOT _it) sp, Ews, s, vs, 0).
    { split.
      - unfold at_node. destruct s; [left; auto | right; list_solve].
      - apply (SglibVST.lib_client4.prev_links_sub s vs 0 (Zlength s));
          auto; lia. }
    Intros vret. destruct vret as [[b f] r]. cbn [fst snd] in *.
    forward. (* l = t'2 *)
    fold (head_at sp (Znth_or_null s 0)).
    forward_loop
     (EX b: Z, EX f: Z, EX c: Z, EX l: val, EX sm: Int.int,
      PROP (-1 <= b < f; f <= Zlength s;
            (l = nullval -> b = -1 /\ f = Zlength s);
            (l <> nullval -> b < c < f /\ l = Znth c s))
      LOCAL (temp _l l; temp _sum (Vint sm); temp _s sp; gvars gv)
      SEP (mem_mgr gv; malloc_token Ews t_holder sp;
           head_at sp (Znth_or_null s 0);
           it_rep Ews (field_address t_holder (DOT _it) sp) s b f
             nullval nullval;
           nodes Ews s vs 0 (b+1); nodes Ews s vs f (Zlength s);
           toks (sublist 0 (b+1) s); toks (sublist f (Zlength s) s);
           node_opt l (Znth c vs);
           data_at shi (tarray tint (Zlength il)) (map Vint il) inp))
    continue:
     (EX b: Z, EX f: Z, EX sm: Int.int,
      PROP (-1 <= b < f; f <= Zlength s)
      LOCAL (temp _sum (Vint sm); temp _s sp; gvars gv)
      SEP (mem_mgr gv; malloc_token Ews t_holder sp;
           head_at sp (Znth_or_null s 0);
           it_rep Ews (field_address t_holder (DOT _it) sp) s b f
             nullval nullval;
           nodes Ews s vs 0 (b+1); nodes Ews s vs f (Zlength s);
           toks (sublist 0 (b+1) s); toks (sublist f (Zlength s) s);
           data_at shi (tarray tint (Zlength il)) (map Vint il) inp))
    break:
     (EX sm: Int.int,
      PROP ()
      LOCAL (temp _sum (Vint sm); temp _s sp; gvars gv)
      SEP (mem_mgr gv; malloc_token Ews t_holder sp;
           head_at sp (Znth_or_null s 0);
           it_rep Ews (field_address t_holder (DOT _it) sp) s (-1)
             (Zlength s) nullval nullval;
           data_at shi (tarray tint (Zlength il)) (map Vint il) inp)).
    + (* entry *)
      destruct H6 as (Hbf & Hfl & Hr1 & Hr2 & Hex).
      destruct (Hex eq_refl) as [(Hr & Hs & Hb & Hf) | (c & Hc & Hr & Hb & Hf)].
      * subst r s b f.
        Exists (-1) 0 0 nullval (Int.repr 0).
        unfold node_opt. rewrite if_true by auto.
        rewrite !Zlength_nil.
        rewrite !SglibVST.lib_client4.nodes_empty by lia.
        rewrite !sublist_of_nil. cbn [toks].
        entailer!.
      * subst r b f.
        Exists (c-1) (c+1) c (Znth c s) (Int.repr 0).
        replace (c - 1 + 1) with c by lia.
        rewrite (SglibVST.lib_client4.nodes_focus Ews s vs 0 c (Zlength s))
          by lia.
        rewrite (toks_focus s c) by lia.
        assert_PROP (isptr (Znth c s)) by entailer!.
        unfold node_opt. rewrite if_false
          by (intro Hn; rewrite Hn in *; contradiction).
        entailer!.
        split; [lia | reflexivity].
    + (* body *)
      clear H6 b f r.
      Intros b0 f0 c l sum.
      destruct (Val.eq l nullval) as [Hn|Hn].
      * subst l. unfold node_opt. rewrite if_true by auto.
        match goal with Hx: nullval = nullval -> _ |- _ =>
          destruct (Hx eq_refl) as [Hb Hf] end.
        subst b0 f0.
        forward_if.
        { discriminate. }
        forward. (* break *)
        Exists sum.
        rewrite !SglibVST.lib_client4.nodes_empty by lia.
        replace (-1 + 1) with 0 by lia.
        replace (sublist 0 0 s) with (@nil val) by list_solve.
        replace (sublist (Zlength s) (Zlength s) s) with (@nil val)
          by list_solve.
        cbn [toks]. entailer!.
      * unfold node_opt. rewrite if_false by auto.
        match goal with Hx: l <> nullval -> _ |- _ =>
          destruct (Hx Hn) as [Hc Hl] end.
        Intros.
        forward_if.
        2:{ contradiction. }
        assert (Hi: int_val (pay (Znth c vs))) by (apply H3; lia).
        destruct Hi as [i Hi].
        destruct (Znth c vs) as [pv [nv pvv]] eqn:Ev.
        cbn [pay fst] in Hi. subst pv.
        forward. (* t'4 = l->i *)
        forward. (* sum += t'4 *)
        forward_call (t_dl, l, gv).
        { rewrite if_false by auto. cancel. }
        Exists b0 f0 (Int.add sum i).
        entailer!.
    + (* increment *)
      clear H6 b f r.
      Intros b0 f0 sum.
      forward_call (gv, Ews, field_address t_holder (DOT _it) sp, Ews, s, vs,
                    b0, f0, nullval, nullval, Ews,
                    (nullval, (nullval, nullval))).
      { unfold cmp_env, cmp_state. rewrite !if_true by auto. cancel. }
      { repeat match goal with |- _ /\ _ => split end; auto; try lia;
        first
          [ apply (SglibVST.lib_client4.prev_links_sub s vs 0 (Zlength s));
            auto; lia
          | apply (SglibVST.lib_client4.next_links_sub s vs 0 (Zlength s));
            auto; lia
          | left; auto ]. }
      Intros vret. destruct vret as [[b' f'] r]. cbn [fst snd] in *.
      unfold cmp_env, cmp_state. rewrite !if_true by auto.
      forward. (* l = t'3 *)
      match goal with Hx: iter_step _ _ _ _ _ _ _ |- _ =>
        destruct Hx as [_ Hex] end.
      specialize (Hex eq_refl).
      destruct Hex as [(Hr & Hb & Hf & Hb' & Hf')
                      | [(Hb & Hr & Hb' & Hf') | (Hf & Hr & Hb' & Hf')]].
      * subst r b0 f0 b' f'.
        Exists (-1) (Zlength s) 0 nullval sum.
        unfold node_opt. rewrite if_true by auto.
        entailer!.
      * subst r b' f'.
        Exists (b0 - 1) f0 b0 (Znth b0 s) sum.
        replace (b0 - 1 + 1) with b0 by lia.
        rewrite (SglibVST.lib_client4.nodes_split Ews s vs 0 b0 (b0+1))
          by lia.
        rewrite SglibVST.lib_client4.nodes_one.
        rewrite (toks_split_last s b0) by lia.
        assert_PROP (isptr (Znth b0 s)) by entailer!.
        unfold node_opt. rewrite if_false
          by (intro Hn; rewrite Hn in *; contradiction).
        entailer!.
        close_props.
      * subst r b' f'.
        Exists b0 (f0 + 1) f0 (Znth f0 s) sum.
        rewrite (SglibVST.lib_client4.nodes_split Ews s vs f0 (f0+1)
                   (Zlength s)) by lia.
        rewrite SglibVST.lib_client4.nodes_one.
        rewrite (toks_split_first s f0) by lia.
        assert_PROP (isptr (Znth f0 s)) by entailer!.
        unfold node_opt. rewrite if_false
          by (intro Hn; rewrite Hn in *; contradiction).
        entailer!.
        close_props.
    + (* after the loop *)
      Intros sum.
      unfold it_rep. Intros cur.
      sep_apply (holder_back sp (Znth_or_null s 0)).
      forward_call (t_holder, sp, gv).
      { rewrite if_false by auto. cancel. }
      forward.
      Exists sum. entailer!.
Qed.

(* ================================================================== *)
(* main and the whole program                                         *)
(* ================================================================== *)

Lemma body_main: semax_body Vprog Gprog f_main main_spec.
Proof.
  start_function.
  sep_apply (create_mem_mgr gv).
  change 5 with (Zlength input_vals).
  forward_call (gv, Ews, gv _input, input_vals).
  { change (Zlength input_vals) with 5. rep_lia. }
  change (Zlength input_vals) with 5.
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

Print Assumptions prog_correct.
