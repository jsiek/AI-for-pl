(* picolRegisterCoreCommands *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import Picol.picol_full Picol.spec_picol Picol.picol_defs Picol.verif_cmd_common.

Lemma ok_insert: forall gv C1 r C2,
  cmds_ok gv (C1 ++ C2) -> In (c_func r) (builtin_addrs gv) -> cmds_ok gv (C1 ++ r :: C2).
Proof.
  intros. unfold cmds_ok in *. apply Forall_app in H. destruct H.
  apply Forall_app. split; auto. constructor; auto. left; auto.
Qed.

Ltac reg gv k id v f :=
  take_lit gv lits k id v;
  match goal with |- context [interp_rep ?i ?s] =>
    forward_call (gv, i, s, Ers, litb v, gv id, gv f);
    [ try (split; [ | auto]); left; simpl; tauto | ] end;
  let vret := fresh "vret" in
  Intros vret; destruct vret as [[[?st ?C1] ?r] ?C2]; simpl fst in *; simpl snd in *;
  give_lit gv lits k id v.

Ltac fix_ok gv :=
  match goal with H: i_cmds ?s = ?C1 ++ ?r :: ?C2, Hf: c_func ?r = ?f |- _ =>
    assert (cmds_ok gv (i_cmds s)) by (rewrite H; apply ok_insert; [auto | rewrite Hf; simpl; tauto]);
    clear H end.

Lemma body_picolRegisterCoreCommands: semax_body Vprog Gprog f_picolRegisterCoreCommands picolRegisterCoreCommands_spec.
Proof.
start_function.
unfold G. Intros. rewrite Gr_GL. Intros.
reg gv 22 ___stringlit_24 v___stringlit_24 _picolCommandExpr. fix_ok gv.
reg gv 23 ___stringlit_25 v___stringlit_25 _picolCommandSet. fix_ok gv.
reg gv 24 ___stringlit_26 v___stringlit_26 _picolCommandPuts. fix_ok gv.
reg gv 25 ___stringlit_27 v___stringlit_27 _picolCommandIf. fix_ok gv.
reg gv 26 ___stringlit_28 v___stringlit_28 _picolCommandWhile. fix_ok gv.
reg gv 16 ___stringlit_18 v___stringlit_18 _picolCommandRetCodes. fix_ok gv.
reg gv 17 ___stringlit_19 v___stringlit_19 _picolCommandRetCodes. fix_ok gv.
reg gv 27 ___stringlit_29 v___stringlit_29 _picolCommandProc. fix_ok gv.
reg gv 28 ___stringlit_30 v___stringlit_30 _picolCommandReturn. fix_ok gv.
match goal with |- context [interp_rep i ?s] => Exists s end.
unfold G. rewrite Gr_GL. entailer!.
Qed.
