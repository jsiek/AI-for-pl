(* picolCommandProc *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import Picol.picol_full Picol.spec_picol Picol.picol_defs Picol.verif_util Picol.verif_interp
  Picol.verif_cmd_common Picol.verif_retcodes Picol.verif_vars Picol.verif_cmds Picol.verif_control.

Lemma find_cmd_mid: forall nm C1 r C2,
  Forall (fun c => c_name c <> nm) C1 -> c_name r = nm -> find_cmd nm (C1 ++ r :: C2) = c_ptr r.
Proof.
  intros. rewrite find_cmd_app by auto. simpl.
  destruct (list_eq_dec Byte.eq_dec (c_name r) nm); [auto | contradiction].
Qed.

Lemma ok_insert_proc: forall gv C1 r C2,
  cmds_ok gv (C1 ++ C2) -> cmd_ok gv r -> cmds_ok gv (C1 ++ r :: C2).
Proof.
  intros. unfold cmds_ok in *. apply Forall_app in H. destruct H.
  apply Forall_app. split; auto.
Qed.

Lemma args4_bound: forall a0 a1 a2 a3, args_size [a0; a1; a2; a3] <= Int.max_signed - 10 ->
  Zlength a3 < Int.max_signed.
Proof.
  intros. unfold args_size in H. simpl in H.
  pose proof (Zlength_nonneg a0). pose proof (Zlength_nonneg a1).
  pose proof (Zlength_nonneg a2). pose proof (Zlength_nonneg a3). rep_lia.
Qed.

Lemma body_picolCommandProc: semax_body Vprog Gprog f_picolCommandProc picolCommandProc_spec.
Proof.
start_function.
pose proof (args_size_ge args).
destruct (Z.eq_dec argc 4) as [Hc|Hc].
2:{ forward_if (PROP (False) LOCAL () SEP ()).
    { arity_ret gv i st args ptrs. }
    { absurd_hyp. } }
subst argc.
destruct args as [|a0 [|a1 [|a2 [|a3 [|? ?]]]]]; try solve [exfalso; list_solve].
destruct ptrs as [|p0 [|p1 [|p2 [|p3 [|? ?]]]]]; try solve [exfalso; list_solve].
cbn [args_pred] in *. Intros.
match goal with H: args_size _ <= _ |- _ => pose proof (args4_bound _ _ _ _ H) as Hb end.
same_pre_if.
{ absurd_hyp. }
{ forward. entailer!. }
forward.
unfold G. Intros.
forward_call (gv, i, st, Ews, a1, p1, gv _picolCommandCallProc).
Intros vret. destruct vret as [[[st1 C1] r] C2]. simpl fst in *; simpl snd in *.
forward.
forward_call (i, st1, Ews, a1, p1).
match goal with H: i_cmds st1 = _ |- _ => rename H into HC end.
rewrite HC, find_cmd_mid by auto.
forward.
forward.
forward_call (Ews, a2, p2, gv). Intros q2.
unfold interp_rep at 1. Intros.
rewrite HC, cmds_split, cmd_node_eq. Intros.
match goal with H: c_arg r = None |- _ => rewrite H end.
match goal with H: c_body r = None |- _ => rewrite H end.
cbn [ostr]. Intros.
forward.
forward.
forward_call (Ews, a3, p3, gv). Intros q3.
forward.
forward.
set (r' := mkcmd (c_ptr r) (c_name r) (c_namep r) (c_func r) (Some a2) q2 (Some a3) q3).
Exists (mkist (i_level st1) (i_frames st1) (C1 ++ r' :: C2) (i_result st1) (i_resultp st1))
       (Int.repr 0).
unfold interp_rep, G. cbn [i_level i_frames i_cmds i_result i_resultp args_pred].
rewrite (hdp_mid c_ptr C1 r' r C2) by reflexivity.
rewrite cmds_split, cmd_node_eq. subst r'.
cbn [c_ptr c_name c_namep c_func c_arg c_argp c_body c_bodyp ostr].
entailer!.
apply ok_insert_proc; auto.
right. split; auto. exists a2, a3. auto.
Qed.
