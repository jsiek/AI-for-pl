(* picolExprExpansion, picolCommandWhile, picolCommandIf *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import Picol.picol_full Picol.spec_picol Picol.picol_defs Picol.verif_util Picol.verif_interp
  Picol.verif_cmd_common Picol.verif_retcodes Picol.verif_vars Picol.verif_cmds.

Lemma len_norm: forall n, 0 <= n <= Ptrofs.max_unsigned ->
  Int64.unsigned (Ptrofs.to_int64 (Ptrofs.repr n)) = n.
Proof.
  intros. rewrite (ptrofs_to_int64_repr (eq_refl _)). rewrite Int64.unsigned_repr by rep_lia. auto.
Qed.

Lemma L8_len: Zlength (litb v___stringlit_9) = 5.
Proof. reflexivity. Qed.

Lemma L8_nz: ~ In Byte.zero (litb v___stringlit_9).
Proof. simpl. intuition; discriminate. Qed.

Lemma split_lit: forall sh L p, Zlength L = 5 -> ~ In Byte.zero L ->
  cstring sh L p =
  (data_at sh (tarray tschar 5) (map Vbyte L) p *
   data_at sh (tarray tschar 1) [Vbyte Byte.zero] (field_address0 (tarray tschar 6) (SUB 5) p))%logic.
Proof.
  intros. unfold cstring. rewrite prop_true_andp by auto. rewrite H.
  rewrite map_app. simpl (map Vbyte [Byte.zero]).
  rewrite (split2_data_at_Tarray_app 5 (5 + 1) sh tschar (map Vbyte L) [Vbyte Byte.zero])
    by list_solve.
  reflexivity.
Qed.

Ltac fa0_tac := apply field_compatible0_cons; simpl; split; [list_solve | auto with field_compatible].

Lemma join_expr: forall L s e, Zlength L = 5 -> ~ In Byte.zero L -> ~ In Byte.zero s ->
  field_compatible (tarray tschar (Zlength s + 6)) [] e ->
  (data_at Ews (tarray tschar 5) (map Vbyte L) e *
   data_at Ews (tarray tschar (Zlength s + 1)) (map Vbyte (s ++ [Byte.zero])) (offset_val 5 e))%logic
  |-- cstring Ews (L ++ s) e.
Proof.
  intros. unfold cstring. rewrite prop_true_andp by (intro X; apply in_app_or in X; tauto).
  rewrite <- app_assoc, (map_app Vbyte L (s ++ [Byte.zero])).
  replace (Zlength (L ++ s) + 1) with (Zlength s + 6) by list_solve.
  rewrite (split2_data_at_Tarray_app 5 (Zlength s + 6) Ews tschar (map Vbyte L)) by list_solve.
  rewrite field_address0_offset by fa0_tac.
  replace (Zlength s + 6 - 5) with (Zlength s + 1) by lia. simpl. cancel.
Qed.

Lemma body_picolExprExpansion: semax_body Vprog Gprog f_picolExprExpansion picolExprExpansion_spec.
Proof.
start_function.
sep_apply (cstring_len sh s sp). Intros.
apply seq_assoc1.
forward_call (sh, s, sp).
forward.
rewrite len_norm by rep_lia.
unfold G. Intros.
forward_call (existT (fun t => list (reptype t)) tschar [], nullval, 0, Zlength s + 6, gv).
all: try solve [rep_lia | cancel].
Intros e. simpl projT1 in *; simpl projT2 in *.
sep_apply (data_at_data_at_ Ews (tarray tschar (Zlength s + 6))).
assert_PROP (field_compatible (tarray tschar (Zlength s + 6)) [] e) by entailer!.
rewrite (split2_data_at__Tarray_app 5 (Zlength s + 6) Ews tschar e) by list_solve.
rewrite field_address0_offset by fa0_tac.
rewrite Gr_GL. Intros.
take_lit gv lits 7 ___stringlit_9 v___stringlit_9.
rewrite (split_lit Ers (litb v___stringlit_9) (gv ___stringlit_9) L8_len L8_nz). Intros.
forward_call (Ews, Ers, e, gv ___stringlit_9, 5, litb v___stringlit_9).
sep_apply (derives_refl' _ _ (eq_sym (split_lit Ers (litb v___stringlit_9) (gv ___stringlit_9) L8_len L8_nz))).
give_lit gv lits 7 ___stringlit_9 v___stringlit_9.
sep_apply (cstring_unfold sh s sp). Intros.
replace (Zlength s + 6 - 5) with (Zlength s + 1) by lia.
replace (nested_field_offset (tarray tschar (Zlength s + 6)) (SUB 5)) with 5 by reflexivity.
forward_call (Ews, sh, offset_val 5 e, sp, Zlength s + 1, s ++ [Byte.zero]).
all: try solve [rep_lia | list_solve | cancel].
sep_apply (cstring_fold sh s sp ltac:(auto)).
sep_apply (join_expr (litb v___stringlit_9) s e L8_len L8_nz ltac:(auto) ltac:(auto)).
sep_apply (derives_refl' _ _ (eq_sym (Gr_GL gv))).
sep_apply (G_fold gv).
forward_call (gv, i, st, Ews, litb v___stringlit_9 ++ s, e).
{ rewrite Zlength_app, L8_len. rep_lia. }
Intros vret. destruct vret as [st' r]. simpl fst in *; simpl snd in *.
unfold cstring at 1. Intros.
sep_apply (data_at_data_at_ Ews (tarray tschar (Zlength (litb v___stringlit_9 ++ s) + 1))).
replace (Zlength (litb v___stringlit_9 ++ s) + 1) with (Zlength s + 6)
  by (rewrite Zlength_app, L8_len; lia).
assert_PROP (isptr e) by entailer!.
forward_call (tarray tschar (Zlength s + 6), e, gv).
{ rewrite if_false by (destruct e; simpl in *; try contradiction; discriminate). cancel. }
forward.
Exists st' r. entailer!.
Qed.

Lemma interp_fold: forall i st, 0 <= i_level st <= 128 -> i_frames st <> [] ->
  (malloc_token Ews (tarray t_interp 1) i *
   data_at Ews t_interp (Vint (Int.repr (i_level st)), (hdp f_ptr (i_frames st) nullval,
      (hdp c_ptr (i_cmds st) nullval, i_resultp st))) i *
   frames_rep (i_frames st) * cmds_rep (i_cmds st) *
   malloc_token Ews (tarray tschar (Zlength (i_result st) + 1)) (i_resultp st) *
   cstring Ews (i_result st) (i_resultp st))%logic |-- interp_rep i st.
Proof. intros. unfold interp_rep, mstr. entailer!. Qed.

(* reads i->result and calls strtod on it *)
Ltac strtod_result i st2 :=
  unfold interp_rep at 1; rewrite (mstr_eq (i_result st2)); Intros;
  forward;
  forward_call (Ews, i_resultp st2, i_result st2, nullval);
  [ rewrite if_true by auto; cancel | ];
  let sres := fresh "sres" in Intros sres;
  rewrite if_true by auto;
  sep_apply (interp_fold i st2 ltac:(auto) ltac:(auto)).

Lemma args3_bound: forall a0 a1 a2, args_size [a0; a1; a2] <= Int.max_signed - 10 ->
  Zlength a1 + 6 <= Int.max_signed /\ Zlength a2 < Int.max_signed.
Proof.
  intros. unfold args_size in H. simpl in H.
  pose proof (Zlength_nonneg a0). pose proof (Zlength_nonneg a1). pose proof (Zlength_nonneg a2).
  rep_lia.
Qed.

Lemma body_picolCommandWhile: semax_body Vprog Gprog f_picolCommandWhile picolCommandWhile_spec.
Proof.
start_function.
pose proof (args_size_ge args).
destruct (Z.eq_dec argc 3) as [Hc|Hc].
2:{ forward_if (PROP (False) LOCAL () SEP ()).
    { arity_tail gv i st args ptrs. Exists (set_res st s q) (Int.repr 1). entailer!. }
    { absurd_hyp. } }
subst argc. three_args args ptrs. cbn [args_pred] in *. Intros.
match goal with H: args_size _ <= _ |- _ => destruct (args3_bound _ _ _ H) as [Hb1 Hb2] end.
same_pre_if.
{ absurd_hyp. }
{ forward. entailer!. }
forward_loop (EX st1: istate,
  PROP (cmds_ok gv (i_cmds st1); i_level st1 = i_level st;
        Zlength (i_frames st1) = Zlength (i_frames st))
  LOCAL (temp _i i; temp _argc (Vint (Int.repr 3)); temp _argv argv; gvars gv)
  SEP (mem_mgr gv; G gv; interp_rep i st1;
       data_at Ews (tarray (tptr tschar) 3) [p0; p1; p2] argv;
       cstring Ews a0 p0; cstring Ews a1 p1; cstring Ews a2 p2))%assert.
- Exists st. entailer!.
- Intros st1.
  forward. forward.
  forward_call (gv, i, st1, Ews, a1, p1).
  Intros vret. destruct vret as [st2 r]. simpl fst in *; simpl snd in *.
  forward.
  same_pre_if.
  { forward. Exists st2 r. cbn [args_pred]. entailer!. }
  { forward. entailer!. }
  strtod_result i st2.
  same_pre_if.
  { forward. Exists st2 (Int.repr 0). cbn [args_pred]. entailer!. }
  { forward. entailer!. }
  forward.
  forward_call (gv, i, st2, Ews, a2, p2).
  Intros vret. destruct vret as [st3 r3]. simpl fst in *; simpl snd in *.
  forward.
  destruct (Int.eq_dec r3 (Int.repr 4)) as [E4|E4].
  { subst r3.
    forward_if (temp _t'5 (Vint Int.one)).
    { forward. entailer!. }
    { absurd_hyp. }
    forward_if.
    { forward. Exists st3. entailer!. }
    { absurd_hyp. } }
  destruct (Int.eq_dec r3 Int.zero) as [E0|E0].
  { subst r3.
    forward_if (temp _t'5 (Vint Int.one)).
    { absurd_hyp. }
    { forward. entailer!. }
    forward_if.
    { forward. Exists st3. entailer!. }
    { absurd_hyp. } }
  forward_if (temp _t'5 (Vint Int.zero)).
  { absurd_hyp. }
  { forward. entailer!. rewrite Int.eq_false by auto. reflexivity. }
  forward_if.
  { absurd_hyp. }
  forward_if.
  { forward. Exists st3 (Int.repr 0). cbn [args_pred]. entailer!. }
  { forward. Exists st3 r3. cbn [args_pred]. entailer!. }
Qed.

Lemma args_elem: forall args j, 0 <= j < Zlength args ->
  Zlength (Znth j args) + 1 <= args_size args.
Proof.
  induction args as [|a args IH]; intros.
  - rewrite Zlength_nil in H. lia.
  - rewrite Zlength_cons in H. unfold args_size; simpl; fold (args_size args).
    pose proof (args_size_ge args). pose proof (Zlength_nonneg args).
    destruct (zeq j 0).
    + subst. rewrite Znth_0_cons. lia.
    + rewrite Znth_pos_cons by lia. specialize (IH (j-1) ltac:(lia)).
      pose proof (Zlength_nonneg a). lia.
Qed.

Ltac fin_eqs :=
  repeat match goal with |- _ /\ _ => split end;
  cbn [set_res i_level i_frames i_cmds] in *; try congruence; auto.

Ltac arity_ret gv i st1 args ptrs :=
  sep_apply (args_isptr 0 args ptrs ltac:(lia) ltac:(lia)); Intros;
  forward;
  rewrite (args_focus 0 args ptrs) by lia; Intros;
  forward_call (gv, i, st1, Ews, Znth 0 args, Znth 0 ptrs);
  let vr := fresh "vr" in let s := fresh "s" in let q := fresh "q" in
  Intros vr; destruct vr as [s q]; simpl fst in *; simpl snd in *;
  sep_apply (derives_refl' _ _ (eq_sym (args_focus 0 args ptrs ltac:(lia) ltac:(lia))));
  forward;
  Exists (set_res st1 s q) (Int.repr 1); entailer!; fin_eqs.

Ltac pre_if_with P :=
  match goal with |- semax _ (PROPx ?A ?B) _ _ => forward_if (PROPx (P :: A) B) end.

Ltac take_G gv := unfold G; Intros; rewrite Gr_GL; Intros.
Ltac give_G gv := sep_apply (derives_refl' _ _ (eq_sym (Gr_GL gv))); sep_apply (G_fold gv).

Lemma body_picolCommandIf: semax_body Vprog Gprog f_picolCommandIf picolCommandIf_spec.
Proof.
start_function.
pose proof (args_size_ge args).
forward.
forward_loop (EX j: Z, EX st1: istate,
  PROP (1 <= j <= argc; cmds_ok gv (i_cmds st1); i_level st1 = i_level st;
        Zlength (i_frames st1) = Zlength (i_frames st))
  LOCAL (temp _j (Vint (Int.repr j)); temp _i i; temp _argc (Vint (Int.repr argc));
         temp _argv argv; gvars gv)
  SEP (mem_mgr gv; G gv; interp_rep i st1;
       data_at Ews (tarray (tptr tschar) argc) ptrs argv; args_pred args ptrs))%assert.
{ Exists 1 st. entailer!. }
Intros j st1.
pre_if_with (j < argc).
{ arity_ret gv i st1 args ptrs. }
{ forward. entailer!. }
Intros.
sep_apply (args_isptr j args ptrs ltac:(lia) ltac:(lia)). Intros.
forward.
rewrite (args_focus j args ptrs) by lia. Intros.
forward_call (gv, i, st1, Ews, Znth j args, Znth j ptrs).
{ pose proof (args_elem args j ltac:(lia)). rep_lia. }
Intros vret. destruct vret as [st2 r]. simpl fst in *; simpl snd in *.
sep_apply (derives_refl' _ _ (eq_sym (args_focus j args ptrs ltac:(lia) ltac:(lia)))).
forward.
same_pre_if.
{ forward. Exists st2 r. entailer!; fin_eqs. }
{ forward. entailer!. }
pre_if_with (j + 1 < argc).
{ arity_ret gv i st2 args ptrs. }
{ forward. entailer!. }
Intros.
strtod_result i st2.
same_pre_if.
{ sep_apply (args_isptr (j+1) args ptrs ltac:(lia) ltac:(lia)). Intros.
  forward.
  rewrite (args_focus (j+1) args ptrs) by lia. Intros.
  forward_call (gv, i, st2, Ews, Znth (j+1) args, Znth (j+1) ptrs).
  { pose proof (args_elem args (j+1) ltac:(lia)). rep_lia. }
  Intros vret. destruct vret as [st3 r3]. simpl fst in *; simpl snd in *.
  sep_apply (derives_refl' _ _ (eq_sym (args_focus (j+1) args ptrs ltac:(lia) ltac:(lia)))).
  forward.
  Exists st3 r3. entailer!; fin_eqs. }
{ forward. entailer!. }
forward.
pre_if_with (j + 2 < argc).
{ forward. Exists st2 (Int.repr 0). entailer!; fin_eqs. }
{ forward. entailer!. }
Intros.
sep_apply (args_isptr (j+2) args ptrs ltac:(lia) ltac:(lia)). Intros.
forward.
take_G gv.
take_lit gv lits 14 ___stringlit_16 v___stringlit_16.
rewrite (args_focus (j+2) args ptrs) by lia. Intros.
forward_call (Ews, Ers, Znth (j+2) ptrs, Znth (j+2) args, gv ___stringlit_16, litb v___stringlit_16).
Intros r2.
give_lit gv lits 14 ___stringlit_16 v___stringlit_16.
sep_apply (derives_refl' _ _ (eq_sym (args_focus (j+2) args ptrs ltac:(lia) ltac:(lia)))).
give_G gv.
same_pre_if.
{ forward_if (EX st3: istate, EX r3: int,
    PROP (cmds_ok gv (i_cmds st3); i_level st3 = i_level st;
          Zlength (i_frames st3) = Zlength (i_frames st))
    LOCAL (temp _t'6 (Vint r3); temp _i i; temp _argc (Vint (Int.repr argc));
           temp _argv argv; gvars gv)
    SEP (mem_mgr gv; G gv; interp_rep i st3;
         data_at Ews (tarray (tptr tschar) argc) ptrs argv; args_pred args ptrs))%assert.
  { sep_apply (args_isptr (j+3) args ptrs ltac:(lia) ltac:(lia)). Intros.
    forward.
    rewrite (args_focus (j+3) args ptrs) by lia. Intros.
    forward_call (gv, i, st2, Ews, Znth (j+3) args, Znth (j+3) ptrs).
    { pose proof (args_elem args (j+3) ltac:(lia)). rep_lia. }
    Intros vret. destruct vret as [st3 r3]. simpl fst in *; simpl snd in *.
    sep_apply (derives_refl' _ _ (eq_sym (args_focus (j+3) args ptrs ltac:(lia) ltac:(lia)))).
    forward.
    Exists st3 r3. entailer!; fin_eqs. }
  { sep_apply (args_isptr 0 args ptrs ltac:(lia) ltac:(lia)). Intros.
    forward.
    rewrite (args_focus 0 args ptrs) by lia. Intros.
    forward_call (gv, i, st2, Ews, Znth 0 args, Znth 0 ptrs).
    Intros vr. destruct vr as [s q]. simpl fst in *; simpl snd in *.
    sep_apply (derives_refl' _ _ (eq_sym (args_focus 0 args ptrs ltac:(lia) ltac:(lia)))).
    forward.
    Exists (set_res st2 s q) (Int.repr 1). entailer!; fin_eqs. }
  Intros st3 r3.
  forward.
  Exists st3 r3. entailer!; fin_eqs. }
{ forward. entailer!. }
forward.
take_G gv.
take_lit gv lits 15 ___stringlit_17 v___stringlit_17.
rewrite (args_focus (j+2) args ptrs) by lia. Intros.
forward_call (Ews, Ers, Znth (j+2) ptrs, Znth (j+2) args, gv ___stringlit_17, litb v___stringlit_17).
Intros r4.
give_lit gv lits 15 ___stringlit_17 v___stringlit_17.
sep_apply (derives_refl' _ _ (eq_sym (args_focus (j+2) args ptrs ltac:(lia) ltac:(lia)))).
give_G gv.
same_pre_if.
{ arity_ret gv i st2 args ptrs. }
{ forward. entailer!. }
forward.
Exists (j+3) st2. entailer!; fin_eqs.
do 2 f_equal; lia.
Qed.
