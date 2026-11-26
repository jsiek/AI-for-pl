(* picolCommandReturn and picolCommandRetCodes *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import Picol.picol_full Picol.spec_picol Picol.picol_defs Picol.verif_cmd_common.

Lemma args_isptr: forall j args ptrs, 0 <= j < Zlength args -> Zlength ptrs = Zlength args ->
  args_pred args ptrs |-- !! isptr (Znth j ptrs).
Proof.
  intros. rewrite (args_focus j args ptrs) by auto. unfold cstring.
  Intros. entailer!.
Qed.

Lemma args_size_ge: forall args, Zlength args <= args_size args.
Proof.
  unfold args_size. induction args; simpl; [rewrite Zlength_nil; lia|]. rewrite Zlength_cons.
  pose proof (Zlength_nonneg a). lia.
Qed.

Ltac fin_cmd st' r :=
  Exists st' r; unfold interp_rep, set_res, G; entailer!;
  cbn [i_level i_frames i_cmds i_result i_resultp]; try cancel.

Ltac absurd_hyp :=
  first [ match goal with Hx: typed_true _ _ |- _ => solve [inv Hx] end
        | match goal with Hx: typed_false _ _ |- _ => solve [inv Hx] end
        | match goal with Hx: ?a <> ?a |- _ => solve [contradiction Hx; reflexivity] end
        | match goal with Hx: _ <> _ |- _ => solve [exfalso; apply Hx; reflexivity] end
        | match goal with Hx: Int.repr _ = Int.repr _ |- _ =>
            solve [apply repr_inj_signed in Hx; [lia | rep_lia | rep_lia]] end
        | match goal with Hx: @eq int _ _ |- _ => solve [vm_compute in Hx; discriminate Hx] end
        | match goal with Hx: @eq val _ _ |- _ => solve [vm_compute in Hx; discriminate Hx] end
        | solve [contradiction] | solve [lia] ].

Lemma body_picolCommandReturn: semax_body Vprog Gprog f_picolCommandReturn picolCommandReturn_spec.
Proof.
start_function.
assert (Hc: argc = 1 \/ argc = 2 \/ (argc <> 1 /\ argc <> 2)) by lia.
destruct Hc as [Hc|[Hc|[Hc1 Hc2]]].
- (* argc = 1 *)
  subst argc.
  forward_if (temp _t'2 (Vint Int.zero)).
  { absurd_hyp. }
  { forward. entailer!. }
  forward_if. { absurd_hyp. }
  forward_if (temp _t'3 (gv ___stringlit_2)).
  { absurd_hyp. }
  { forward. entailer!. }
  unfold G. Intros. rewrite Gr_GL. Intros.
  take_lit gv lits 0 ___stringlit_2 v___stringlit_2.
  unfold interp_rep. Intros.
  forward_call (gv, i, Vint (Int.repr (i_level st)), hdp f_ptr (i_frames st) nullval,
                hdp c_ptr (i_cmds st) nullval, i_result st, i_resultp st,
                Ers, litb v___stringlit_2, gv ___stringlit_2).
  Intros q.
  give_lit gv lits 0 ___stringlit_2 v___stringlit_2.
  forward.
  fin_cmd (set_res st (litb v___stringlit_2) q) (Int.repr 2).
  rewrite Gr_GL. cancel.
- (* argc = 2 *)
  subst argc.
  forward_if (temp _t'2 (Vint Int.zero)).
  { forward. entailer!. }
  { absurd_hyp. }
  forward_if. { absurd_hyp. }
  forward_if (temp _t'3 (Znth 1 ptrs)).
  { sep_apply (args_isptr 1 args ptrs ltac:(lia) ltac:(lia)). Intros.
    forward. forward. entailer!. }
  { absurd_hyp. }
  rewrite (args_focus 1 args ptrs) by lia. Intros.
  unfold G, interp_rep. Intros.
  forward_call (gv, i, Vint (Int.repr (i_level st)), hdp f_ptr (i_frames st) nullval,
                hdp c_ptr (i_cmds st) nullval, i_result st, i_resultp st,
                Ews, Znth 1 args, Znth 1 ptrs).
  Intros q.
  sep_apply (derives_refl' _ _ (eq_sym (args_focus 1 args ptrs ltac:(lia) ltac:(lia)))).
  forward.
  fin_cmd (set_res st (Znth 1 args) q) (Int.repr 2).
- pose proof (args_size_ge args).
  forward_if (temp _t'2 (Vint Int.one)).
  { forward. entailer!; try
    match goal with |- context [Int.eq ?a ?b] => destruct (Int.eq a b) eqn:E;
      [apply Int.same_if_eq in E; apply repr_inj_signed in E; rep_lia | reflexivity] end. }
  { absurd_hyp. }
  forward_if.
  2:{ absurd_hyp. }
  sep_apply (args_isptr 0 args ptrs ltac:(lia) ltac:(lia)). Intros.
  forward.
  rewrite (args_focus 0 args ptrs) by lia. Intros.
  forward_call (gv, i, st, Ews, Znth 0 args, Znth 0 ptrs).
  Intros vret. destruct vret as [s q]. simpl fst in *; simpl snd in *.
  sep_apply (derives_refl' _ _ (eq_sym (args_focus 0 args ptrs ltac:(lia) ltac:(lia)))).
  forward.
  Exists (set_res st s q) (Int.repr 1). entailer!.
Qed.

Lemma body_picolCommandRetCodes: semax_body Vprog Gprog f_picolCommandRetCodes picolCommandRetCodes_spec.
Proof.
start_function.
sep_apply (args_isptr 0 args ptrs ltac:(lia) ltac:(lia)). Intros.
pose proof (args_size_ge args).
forward_if (PROP (argc = 1) LOCAL (temp _i i; temp _argc (Vint (Int.repr argc)); temp _argv argv; gvars gv)
  SEP (mem_mgr gv; G gv; interp_rep i st; data_at Ews (tarray (tptr tschar) argc) ptrs argv;
       args_pred args ptrs)).
{ forward. rewrite (args_focus 0 args ptrs) by lia. Intros.
  forward_call (gv, i, st, Ews, Znth 0 args, Znth 0 ptrs).
  Intros vret. destruct vret as [s q]. simpl fst in *; simpl snd in *.
  sep_apply (derives_refl' _ _ (eq_sym (args_focus 0 args ptrs ltac:(lia) ltac:(lia)))).
  forward. Exists (set_res st s q) (Int.repr 1). entailer!. }
{ forward. entailer!; apply repr_inj_signed; auto; rep_lia. }
Intros. subst argc.
forward.
rewrite (args_focus 0 args ptrs) by lia. Intros.
unfold G. Intros. rewrite Gr_GL. Intros.
take_lit gv lits 16 ___stringlit_18 v___stringlit_18.
forward_call (Ews, Ers, Znth 0 ptrs, Znth 0 args, gv ___stringlit_18, litb v___stringlit_18).
Intros r1.
give_lit gv lits 16 ___stringlit_18 v___stringlit_18.
sep_apply (derives_refl' _ _ (eq_sym (args_focus 0 args ptrs ltac:(lia) ltac:(lia)))).
match goal with |- semax _ ?Pre _ _ => forward_if Pre end.
{ forward. Exists st (Int.repr 3). unfold G. rewrite Gr_GL. entailer!. }
{ forward. rewrite (args_focus 0 args ptrs) by lia. Intros.
  take_lit gv lits 17 ___stringlit_19 v___stringlit_19.
  forward_call (Ews, Ers, Znth 0 ptrs, Znth 0 args, gv ___stringlit_19, litb v___stringlit_19).
  Intros r2.
  give_lit gv lits 17 ___stringlit_19 v___stringlit_19.
  sep_apply (derives_refl' _ _ (eq_sym (args_focus 0 args ptrs ltac:(lia) ltac:(lia)))).
  forward_if.
  { forward. Exists st (Int.repr 4). unfold G. rewrite Gr_GL. entailer!. }
  { forward. entailer!. } }
forward. Exists st (Int.repr 0). unfold G. rewrite Gr_GL. entailer!.
Qed.
