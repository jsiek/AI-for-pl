(* picol_main *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import Picol.picol_full Picol.spec_picol Picol.picol_defs Picol.verif_util Picol.verif_parse
  Picol.verif_interp Picol.verif_cmd_common Picol.verif_retcodes Picol.verif_vars Picol.verif_cmds
  Picol.verif_control Picol.verif_strutil Picol.verif_globs.

#[local] Hint Resolve FILE_handle_valid : valid_pointer.

Ltac hps gv l :=
  lazymatch l with
  | nil => idtac
  | ?id :: ?l' =>
      assert_PROP (headptr (gv id)) by (eapply gvars_denote_HP'; [simpl; auto | reflexivity]);
      hps gv l'
  end.

Lemma body_picol_main: semax_body Vprog Gprog f_picol_main picol_main_spec.
Proof.
start_function.
let l := eval unfold gids in gids in hps gv l.
assert (HP: forall id, In id gids -> headptr (gv id)).
{ intros id Hid. unfold gids in Hid. simpl in Hid.
  repeat (destruct Hid as [<-|Hid]; [assumption|]). contradiction. }
rewrite (globs_eq gv HP). Intros.
forward_call (gv).
Intros vret. destruct vret as [i st]. simpl fst in *; simpl snd in *.
forward_call (gv, i, st).
{ match goal with H: i_cmds st = [] |- _ => rewrite H end. constructor. }
Intros st1.
forward_if (EX st2: istate,
  PROP (cmds_ok gv (i_cmds st2))
  LOCAL (temp _interp i; lvar _buf (tarray tschar 16384) v_buf;
         lvar _num (tarray tschar 12) v_num; lvar _clibuf (tarray tschar 1024) v_clibuf; gvars gv)
  SEP (mem_mgr gv; G gv; interp_rep i st2;
       data_at_ Tsh (tarray tschar 16384) v_buf; data_at_ Tsh (tarray tschar 12) v_num;
       data_at_ Tsh (tarray tschar 1024) v_clibuf; lit gv ___stringlit_35 v___stringlit_35;
       data_at Ews (tarray (tptr tschar) (argc + 1)) (ptrs ++ [nullval]) argv;
       args_pred args ptrs))%assert.
{ forward_loop (EX st2: istate,
    PROP (cmds_ok gv (i_cmds st2))
    LOCAL (temp _interp i; lvar _buf (tarray tschar 16384) v_buf;
           lvar _num (tarray tschar 12) v_num; lvar _clibuf (tarray tschar 1024) v_clibuf; gvars gv)
    SEP (mem_mgr gv; G gv; interp_rep i st2;
         data_at_ Tsh (tarray tschar 16384) v_buf; data_at_ Tsh (tarray tschar 12) v_num;
         data_at_ Tsh (tarray tschar 1024) v_clibuf; lit gv ___stringlit_35 v___stringlit_35;
         data_at Ews (tarray (tptr tschar) (argc + 1)) (ptrs ++ [nullval]) argv;
         args_pred args ptrs))%assert
   break: (EX st2: istate,
    PROP (cmds_ok gv (i_cmds st2))
    LOCAL (temp _interp i; lvar _buf (tarray tschar 16384) v_buf;
           lvar _num (tarray tschar 12) v_num; lvar _clibuf (tarray tschar 1024) v_clibuf; gvars gv)
    SEP (mem_mgr gv; G gv; interp_rep i st2;
         data_at_ Tsh (tarray tschar 16384) v_buf; data_at_ Tsh (tarray tschar 12) v_num;
         data_at_ Tsh (tarray tschar 1024) v_clibuf; lit gv ___stringlit_35 v___stringlit_35;
         data_at Ews (tarray (tptr tschar) (argc + 1)) (ptrs ++ [nullval]) argv;
         args_pred args ptrs))%assert.
  { Exists st1. entailer!. }
  Intros st2.
  unfold G. Intros. rewrite Gr_GL, Gs_eq. Intros.
  forward.
  take_lit gv lits 31 ___stringlit_33 v___stringlit_33.
  forward_call (Ers, gv ___stringlit_33, litb v___stringlit_33, gv ___stdout_FILE, false, gv).
  { entailer!. unfold std_stream; auto. }
  give_lit gv lits 31 ___stringlit_33 v___stringlit_33.
  forward.
  forward_call (gv ___stdout_FILE, false, gv).
  { entailer!. unfold std_stream; auto. }
  forward.
  rewrite (buf_split_tsh (tarray tschar 1024) v_clibuf). Intros.
  forward_call (v_clibuf, 1024, gv ___stdin_FILE, false, gv).
  { entailer!. unfold std_stream; auto. }
  Intros r.
  if_tac.
  { subst r.
    forward_if.
    { forward.
      sep_apply (derives_refl' _ _ (eq_sym (buf_split_tsh (tarray tschar 1024) v_clibuf))).
      Exists st2. unfold G. rewrite Gr_GL, Gs_eq. entailer!. }
    { exfalso. absurd_hyp. } }
  Intros s. subst r.
  forward_if.
  { entailer!. apply denote_tc_test_eq_split;
      [ repeat apply sepcon_valid_pointer1; apply cstringn_valid_pointer;
        apply readable_nonidentity; auto
      | apply valid_pointer_null ]. }
  { forward. unfold cstringn. Intros.
    sep_apply (data_at_data_at_ Ews (tarray tschar 1024)).
    sep_apply (derives_refl' _ _ (eq_sym (buf_split_tsh (tarray tschar 1024) v_clibuf))).
    Exists st2. unfold G. rewrite Gr_GL, Gs_eq. entailer!. }
  assert_PROP (Zlength s + 1 <= 1024) by entailer!.
  unfold cstringn. Intros.
  rewrite (strbuf_split Ews s 1024 (Zrepeat Vundef (1024 - (Zlength s + 1))) v_clibuf)
    by (auto; try lia; list_solve).
  Intros.
  sep_apply (derives_refl' _ _ (eq_sym (Gs_eq gv))).
  sep_apply (derives_refl' _ _ (eq_sym (Gr_GL gv))).
  sep_apply (G_fold gv).
  forward_call (gv, i, st2, Ews, s, v_clibuf).
  Intros vret. destruct vret as [st3 rc]. simpl fst in *; simpl snd in *.
  sep_apply (derives_refl' _ _ (eq_sym (strbuf_split Ews s 1024 (Zrepeat Vundef (1024 - (Zlength s + 1)))
     v_clibuf ltac:(auto) ltac:(lia) ltac:(list_solve)))).
  sep_apply (data_at_data_at_ Ews (tarray tschar 1024)).
  sep_apply (derives_refl' _ _ (eq_sym (buf_split_tsh (tarray tschar 1024) v_clibuf))).
  unfold interp_rep at 1. Intros. rewrite (mstr_eq (i_result st3)). unfold cstring. Intros.
  forward.
  assert_PROP (field_compatible (tarray tschar (Zlength (i_result st3) + 1)) [] (i_resultp st3))
    by entailer!.
  assert_PROP (isptr (i_resultp st3)) by entailer!.
  assert (force_val (sem_add_ptr_int tschar Signed (i_resultp st3) (Vint (Int.repr 0))) =
          field_address (tarray tschar (Zlength (i_result st3) + 1)) (SUB 0) (i_resultp st3))
    by (rewrite add0_ptr by auto; transitivity (offset_val 0 (i_resultp st3));
        [rewrite isptr_offset_val_zero; auto | apply arr_field_address; auto; list_solve]).
  forward.
  sep_apply (cstring_fold Ews (i_result st3) (i_resultp st3) ltac:(auto)).
  sep_apply (derives_refl' _ _ (eq_sym (mstr_eq (i_result st3) (i_resultp st3)))).
  sep_apply (interp_refold i st3 ltac:(auto) ltac:(auto)).
  forward_if (PROP ()
    LOCAL (temp _interp i; lvar _buf (tarray tschar 16384) v_buf;
           lvar _num (tarray tschar 12) v_num; lvar _clibuf (tarray tschar 1024) v_clibuf; gvars gv)
    SEP (mem_mgr gv; G gv; interp_rep i st3;
         data_at_ Tsh (tarray tschar 16384) v_buf; data_at_ Tsh (tarray tschar 12) v_num;
         data_at_ Tsh (tarray tschar 1024) v_clibuf; lit gv ___stringlit_35 v___stringlit_35;
         data_at Ews (tarray (tptr tschar) (argc + 1)) (ptrs ++ [nullval]) argv;
         args_pred args ptrs))%assert.
  { replace rc with (Int.repr (Int.signed rc)) by apply Int.repr_signed.
    forward_call (Tsh, v_num, 12, Int.signed rc).
    all: try (pose proof (Int.signed_range rc); repeat split; auto; rep_lia).
    Intros s1. unfold strbuf. Intros rest1. rewrite strbuf_split by auto. Intros.
    unfold G. Intros. rewrite Gr_GL, Gs_eq. Intros.
    forward.
    take_lit gv lits 32 ___stringlit_34 v___stringlit_34.
    forward_call (Ers, gv ___stringlit_34, litb v___stringlit_34, gv ___stdout_FILE, false, gv).
    { entailer!. unfold std_stream; auto. }
    give_lit gv lits 32 ___stringlit_34 v___stringlit_34.
    forward.
    forward_call (Tsh, v_num, s1, gv ___stdout_FILE, false, gv).
    { entailer!. unfold std_stream; auto. }
    forward.
    unfold lit at 1.
    forward_call (Ers, gv ___stringlit_35, litb v___stringlit_35, gv ___stdout_FILE, false, gv).
    { entailer!. unfold std_stream; auto. }
    change (cstring Ers (litb v___stringlit_35) (gv ___stringlit_35))
      with (lit gv ___stringlit_35 v___stringlit_35).
    unfold interp_rep at 1. Intros. rewrite (mstr_eq (i_result st3)). Intros.
    forward. forward.
    forward_call (Ews, i_resultp st3, i_result st3, gv ___stdout_FILE, false, gv).
    { entailer!. unfold std_stream; auto. }
    forward.
    take_lit gv lits 13 ___stringlit_15 v___stringlit_15.
    forward_call (Ers, gv ___stringlit_15, litb v___stringlit_15, gv ___stdout_FILE, false, gv).
    { entailer!. unfold std_stream; auto. }
    give_lit gv lits 13 ___stringlit_15 v___stringlit_15.
    sep_apply (derives_refl' _ _ (eq_sym (strbuf_split Tsh s1 12 rest1 v_num ltac:(auto) ltac:(auto) ltac:(auto)))).
    sep_apply (data_at_data_at_ Tsh (tarray tschar 12)).
    sep_apply (derives_refl' _ _ (eq_sym (mstr_eq (i_result st3) (i_resultp st3)))).
    sep_apply (interp_refold i st3 ltac:(auto) ltac:(auto)).
    unfold G. rewrite Gr_GL, Gs_eq. entailer!. }
  { forward. entailer!. }
  Exists st3. entailer!. }
forward_if (EX st2: istate,
  PROP (cmds_ok gv (i_cmds st2))
  LOCAL (temp _interp i; lvar _buf (tarray tschar 16384) v_buf;
         lvar _num (tarray tschar 12) v_num; lvar _clibuf (tarray tschar 1024) v_clibuf; gvars gv)
  SEP (mem_mgr gv; G gv; interp_rep i st2;
       data_at_ Tsh (tarray tschar 16384) v_buf; data_at_ Tsh (tarray tschar 12) v_num;
       data_at_ Tsh (tarray tschar 1024) v_clibuf; lit gv ___stringlit_35 v___stringlit_35;
       data_at Ews (tarray (tptr tschar) (argc + 1)) (ptrs ++ [nullval]) argv;
       args_pred args ptrs))%assert.
2:{ forward. Exists st1. entailer!. }
subst argc. two_args args ptrs. cbn [args_pred] in *. Intros.
forward.
unfold G. Intros. rewrite Gr_GL, Gs_eq. Intros.
take_lit gv lits 29 ___stringlit_31 v___stringlit_31.
forward_call (Ews, Ers, p1, gv ___stringlit_31, a1, litb v___stringlit_31).
Intros fp.
give_lit gv lits 29 ___stringlit_31 v___stringlit_31.
forward.
if_tac.
{ forward_if (PROP (False) LOCAL () SEP ()).
  { take_lit gv lits 30 ___stringlit_32 v___stringlit_32.
    forward_call (Ers, gv ___stringlit_32, litb v___stringlit_32).
    forward_call 1. Intros. contradiction. }
  { first [contradiction | absurd_hyp | (exfalso; congruence)]. } }
same_pre_if.
{ take_lit gv lits 30 ___stringlit_32 v___stringlit_32.
  forward_call (Ers, gv ___stringlit_32, litb v___stringlit_32).
  forward_call 1. Intros. contradiction. }
{ forward. entailer!. }
rewrite (buf_split_tsh (tarray tschar 16384) v_buf). Intros.
rewrite <- (data_at_undef Ews 16384 v_buf).
assert_PROP (field_compatible (tarray tschar 16384) [] v_buf) by entailer!.
replace (Zrepeat Vundef 16384) with (Zrepeat Vundef 16383 ++ Zrepeat Vundef 1) by list_solve.
rewrite (arr_split2 Ews 16384 16383 1 (Zrepeat Vundef 16383) (Zrepeat Vundef 1) v_buf)
  by (auto; list_solve).
Intros.
rewrite (data_at_undef Ews 16383 v_buf).
change (tarray tschar 16383) with (tarray tschar (1 * 16383)).
forward_call (v_buf, 1, 16383, fp, true, gv).
Intros vret. destruct vret as [k bytes]. simpl fst in *; simpl snd in *.
change (1 * 16383) with 16383.
replace (1 * (16383 - k)) with (16383 - k) by lia.
sep_apply (derives_refl' _ _ (eq_sym (arr_split2 Ews 16384 16383 1
   (map Vbyte bytes ++ Zrepeat Vundef (16383 - k)) (Zrepeat Vundef 1) v_buf
   ltac:(lia) ltac:(list_solve) ltac:(list_solve) ltac:(lia) ltac:(lia) ltac:(auto)))).
pose proof (arr_field_address 16384 k v_buf ltac:(lia) ltac:(auto)).
forward.
forward_call fp.
destruct (first_zero bytes) as (z & Hz & Hnz & Hend).
set (C := upd_Znth k ((map Vbyte bytes ++ Zrepeat Vundef (16383 - k)) ++ Zrepeat Vundef 1)
                   (Vint (Int.repr 0))).
assert (HC: C = map Vbyte (sublist 0 z bytes ++ [Byte.zero]) ++ sublist (z + 1) 16384 C).
{ subst C. change (Vint (Int.repr 0)) with (Vbyte Byte.zero).
  assert (Hkb: Zlength bytes = k) by lia.
  destruct Hend as [Hzk | [Hlt Hz0]].
  - subst z. list_solve.
  - replace (sublist 0 z bytes ++ [Byte.zero]) with (sublist 0 (z + 1) bytes)
      by (rewrite (sublist_split 0 z (z + 1)) by lia; rewrite sublist_len_1 by lia;
          rewrite Hz0; auto).
    list_solve. }
assert (Hkb: Zlength bytes = k) by lia.
assert (HCl: Zlength C = 16384) by (unfold C; list_solve).
rewrite HC.
rewrite (strbuf_split Ews (sublist 0 z bytes) 16384 (sublist (z + 1) 16384 C) v_buf)
  by (auto; list_solve).
Intros.
sep_apply (derives_refl' _ _ (eq_sym (Gs_eq gv))).
sep_apply (derives_refl' _ _ (eq_sym (Gr_GL gv))).
sep_apply (G_fold gv).
forward_call (gv, i, st1, Ews, sublist 0 z bytes, v_buf).
all: try (rewrite Zlength_sublist by lia; rep_lia).
Intros vret. destruct vret as [st2 rc]. simpl fst in *; simpl snd in *.
forward_if (PROP ()
  LOCAL (temp _interp i; lvar _buf (tarray tschar 16384) v_buf;
         lvar _num (tarray tschar 12) v_num; lvar _clibuf (tarray tschar 1024) v_clibuf; gvars gv)
  SEP (mem_mgr gv; G gv; interp_rep i st2;
       cstring Ews (sublist 0 z bytes) v_buf;
       data_at Ews (tarray tschar (16384 - (Zlength (sublist 0 z bytes) + 1))) (sublist (z + 1) 16384 C)
         (field_address0 (tarray tschar 16384) (SUB (Zlength (sublist 0 z bytes) + 1)) v_buf);
       data_at_ (Share.comp Ews) (tarray tschar 16384) v_buf;
       data_at_ Tsh (tarray tschar 12) v_num;
       data_at_ Tsh (tarray tschar 1024) v_clibuf; lit gv ___stringlit_35 v___stringlit_35;
       data_at Ews (tarray (tptr tschar) (Zlength [a0; a1] + 1)) ([p0; p1] ++ [nullval]) argv;
       cstring Ews a0 p0; cstring Ews a1 p1))%assert.
{ unfold G. Intros. rewrite Gr_GL, Gs_eq. Intros.
  unfold interp_rep at 1. Intros. rewrite (mstr_eq (i_result st2)). Intros.
  forward. forward.
  forward_call (Ews, i_resultp st2, i_result st2, gv ___stdout_FILE, false, gv).
  { entailer!. unfold std_stream; auto. }
  forward.
  take_lit gv lits 13 ___stringlit_15 v___stringlit_15.
  forward_call (Ers, gv ___stringlit_15, litb v___stringlit_15, gv ___stdout_FILE, false, gv).
  { entailer!. unfold std_stream; auto. }
  give_lit gv lits 13 ___stringlit_15 v___stringlit_15.
  sep_apply (derives_refl' _ _ (eq_sym (mstr_eq (i_result st2) (i_resultp st2)))).
  sep_apply (interp_refold i st2 ltac:(auto) ltac:(auto)).
  unfold G. rewrite Gr_GL, Gs_eq. entailer!. }
{ forward. entailer!. }
sep_apply (derives_refl' _ _ (eq_sym (strbuf_split Ews (sublist 0 z bytes) 16384 (sublist (z + 1) 16384 C) v_buf
   ltac:(auto) ltac:(list_solve) ltac:(list_solve)))).
sep_apply (data_at_data_at_ Ews (tarray tschar 16384)).
sep_apply (derives_refl' _ _ (eq_sym (buf_split_tsh (tarray tschar 16384) v_buf))).
Exists st2. cbn [args_pred]. entailer!.
Intros st2.
forward_call (gv, i, st2).
sep_apply (derives_refl' _ _ (eq_sym (globs_eq gv HP))).
forward.
Exists (Int.repr 0). entailer!.
Qed.
