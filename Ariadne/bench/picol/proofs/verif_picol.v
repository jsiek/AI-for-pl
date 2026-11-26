Require Import VST.floyd.proofauto. Require Import VST.floyd.library.
Require Import Picol.picol_full Picol.spec_picol.
#[export] Existing Instance NullExtension.Espec.
Require Import Picol.picol_defs Picol.verif_libc Picol.verif_util Picol.verif_parse
  Picol.verif_parse2 Picol.verif_parse3 Picol.verif_gettoken Picol.verif_interp Picol.verif_frames Picol.verif_vars Picol.verif_cmd_common
  Picol.verif_retcodes Picol.verif_core_cmds Picol.verif_cmds Picol.verif_control
  Picol.verif_proc Picol.verif_main Picol.verif_pstring Picol.verif_strutil Picol.verif_cmdexpr
  Picol.verif_evalutil Picol.verif_callproc Picol.verif_globs Picol.verif_pmain Picol.verif_expr Picol.verif_evalutil2 Picol.verif_eval.

(* Gprog is defined in picol_defs.v (frozen specs of spec_picol.v + ours). *)


Ltac ext_ret :=
  repeat (rewrite exp_unfold; let x := fresh "x" in Intros x);
  rewrite <- insert_local; rewrite lower_andp;
  apply derives_extract_prop;
  let H1 := fresh "Hr" in let H2 := fresh "Hr" in
  intros [H1 H2]; unfold_lift in H1; unfold_lift in H2;
  match goal with r: option val |- _ => destruct r end; try contradiction;
  unfold eval_id in H1; simpl in H1; subst.

(* VST's semax_func_cons, without the (here very slow) attempts to close
   the body goal by unification; uses the tycontext_subVG fact instead. *)
Ltac my_sfc L :=
  repeat (eapply semax_func_cons_ext_vacuous; [reflexivity | reflexivity | LookupID | LookupB |]);
  try_prove_tycontext_subVG L;
  eapply semax_func_cons;
    [ reflexivity
    | repeat apply Forall_cons; try apply Forall_nil; try computable; reflexivity
    | unfold var_sizes_ok; repeat constructor; try (simpl; rep_lia)
    | reflexivity | LookupID | LookupB
    | eapply (@semax_body_subsumption' _ _ _ _ _ _ _ _ L);
        [ first [ apply cspecs_sub_refl
                | split3; red; apply @sub_option_get;
                  repeat (apply Forall_cons; [reflexivity | ]); apply Forall_nil ]
        | repeat (apply Forall_cons; [ reflexivity | ]); apply Forall_nil
        | apply tycontext_sub_i99; assumption ]
    | ];
  repeat (eapply semax_func_cons_ext_vacuous; [reflexivity | reflexivity | LookupID | LookupB |]);
  try apply semax_func_nil.

Transparent peq.
Lemma prog_correct: semax_prog prog tt Vprog Gprog.
Proof.
  prove_semax_prog.
  semax_func_cons body_fopen.
  { rewrite exp_unfold. Intros pp.
  rewrite <- insert_local. rewrite lower_andp.
  apply derives_extract_prop. intros [Hret Hret2]. unfold_lift in Hret. unfold_lift in Hret2.
  match goal with r: option val |- _ => destruct r end; try contradiction.
  unfold eval_id in Hret; simpl in Hret. subst pp. destruct (eq_dec _ nullval) as [Hn|Hn].
    rewrite Hn; entailer!. renormalize. sep_apply (FILE_handle_ptr v1). entailer!. }
  semax_func_cons body_fclose. { ext_ret. entailer!. }
  semax_func_cons body_fflush. { ext_ret. entailer!. }
  semax_func_cons body_fread. { ext_ret. entailer!. }
  semax_func_cons body_fgets.
  { ext_ret. destruct (eq_dec _ nullval) as [Hn|Hn]. rewrite Hn; entailer!.
    unfold PROPx, LOCALx, SEPx; simpl. normalize. unfold cstringn. entailer!. }
  semax_func_cons body_fputs. { ext_ret. entailer!. }
  semax_func_cons body_perror.
  semax_func_cons body_strtod. { ext_ret. entailer!. }
  semax_func_cons body_realloc.
  { ext_ret. destruct (eq_dec _ nullval) as [Hn|Hn]. rewrite Hn; entailer!.
    unfold PROPx, LOCALx, SEPx; simpl. normalize. entailer!. }
  Opaque peq.
  semax_func_cons body_free.
  semax_func_cons body_exit.
  my_sfc body_xrealloc.
  my_sfc body_xstrdup.
  my_sfc body_fmt_append.
  my_sfc body_fmt_str3.
  my_sfc body_fmt_int.
  semax_func_cons body_fmt_double.
  my_sfc body_picolInitParser.
  my_sfc body_picolParseSep.
  my_sfc body_picolParseEol.
  my_sfc body_picolParseCommand.
  my_sfc body_picolParseVar.
  my_sfc body_picolParseBrace.
  my_sfc body_picolParseString.
  my_sfc body_picolParseComment.
  my_sfc body_picolGetToken.
  my_sfc body_picolInitInterp.
  my_sfc body_picolSetResult.
  my_sfc body_picolGetVar.
  my_sfc body_picolSetVar.
  my_sfc body_picolGetCommand.
  my_sfc body_picolRegisterCommand.
  my_sfc body_picolEval.
  my_sfc body_picolExpr.
  my_sfc body_picolExprExpansion.
  my_sfc body_picolArityErr.
  my_sfc body_picolCommandExpr.
  my_sfc body_picolCommandSet.
  my_sfc body_picolCommandPuts.
  my_sfc body_picolCommandIf.
  my_sfc body_picolCommandWhile.
  my_sfc body_picolCommandRetCodes.
  my_sfc body_picolDropCallFrame.
  my_sfc body_picolFreeInterp.
  my_sfc body_picolCallProcFail.
  my_sfc body_picolCommandCallProc.
  my_sfc body_picolCommandProc.
  my_sfc body_picolCommandReturn.
  my_sfc body_picolRegisterCoreCommands.
  my_sfc body_picol_main.
  my_sfc body_strlen.
  my_sfc body___strchrnul.
  my_sfc body_strchr.
  my_sfc body_strcmp.
  my_sfc body_memcpy.
  my_sfc body_isupper.
  my_sfc body___isupper_l.
  my_sfc body_main.
Qed.
