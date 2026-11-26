(* From the string literals back to globvars2pred (the converse of VST's
   globvar2pred_cstring), for picol_main's postcondition. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import Picol.picol_full Picol.spec_picol Picol.picol_defs.

Lemma init_data_tarray_tuchar_rev:
  forall sh (gv : globals) (b : block) (xs : list int) (i : ptrofs),
  Ptrofs.unsigned i + Zlength xs < Ptrofs.modulus ->
  Forall (fun a => Int.unsigned a <= Byte.max_unsigned) xs ->
  data_at sh (tarray tuchar (Zlength xs)) (map Vint xs) (Vptr b i)
  |-- init_data_list2pred gv (map Init_int8 xs) sh (Vptr b i).
Proof.
  intros.
  replace xs with (map (Int.zero_ext 8) xs).
  2:{
    clear - H0.
    induction H0; simpl; auto. f_equal; auto.
    apply zero_ext_inrange. simpl. rep_lia.
  }
  clear H0; revert i H;
  induction xs; intros; simpl.
  - rewrite data_at_zero_array_eq; auto; reflexivity.
  - rewrite Zlength_cons in H.
    specialize (Zlength_nonneg xs); intros L.
    unfold Ptrofs.add. rewrite ! Ptrofs.unsigned_repr; try rep_lia.
    rewrite (split2_data_at_Tarray sh tuchar (Zlength (Int.zero_ext 8 a :: (map (Int.zero_ext 8) xs))) 1
            (Vint (Int.zero_ext 8 a) :: map Vint (map (Int.zero_ext 8) xs)) (Vint (Int.zero_ext 8 a) :: map Vint (map (Int.zero_ext 8) xs))
            (sublist 0 1 (Vint (Int.zero_ext 8 a) :: map Vint (map (Int.zero_ext 8) xs)))
            (sublist 1 (Zlength (Int.zero_ext 8 a :: xs)) (Vint (Int.zero_ext 8 a) :: map Vint (map (Int.zero_ext 8) xs))) (Vptr b i)); try list_solve.
   apply sepcon_derives.
   + fold tuchar.
     rewrite (data_at_singleton_array_eq sh tuchar (Vint (Int.zero_ext 8 a)))
       by trivial.
     erewrite mapsto_data_at'; auto; trivial.
     rewrite Int.zero_ext_idem by lia. auto.
     red; simpl; intuition auto with *.
     econstructor. reflexivity. simpl; trivial. apply Z.divide_1_l.
   + eapply derives_trans; [ | apply IHxs ].
     * rewrite Zlength_cons.
       unfold Z.succ. rewrite Z.add_simpl_r. autorewrite with sublist.
       rewrite sublist_1_cons by lia.
       rewrite sublist_same by list_solve.
       apply derives_refl'. f_equal.
       unfold field_address0. rewrite if_true; simpl; trivial.
       red; intuition auto with *.
       -- reflexivity.
       -- red. rewrite sizeof_Tarray, Z.max_r. simpl sizeof; rep_lia. list_solve.
       -- eapply align_compatible_rec_Tarray; intros.
          econstructor. reflexivity.
          simpl. apply Z.divide_1_l.
     * rewrite ! Ptrofs.unsigned_repr; try rep_lia.
Qed.

Lemma globvar2pred_cstring_rev:
 forall gv i v,
  headptr (gv i) ->
  0 < Zlength (gvar_init v) < Ptrofs.modulus ->
  Znth (Zlength (gvar_init v)-1) (gvar_init v) = Init_int8 Int.zero ->
  gvar_volatile v = false ->
  forallb ok_initbyte (sublist 0 (Zlength (gvar_init v)-1) (gvar_init v)) = true ->
  gvar_info v = tarray tschar (Zlength (gvar_init v)) ->
  cstring (readonly2share (gvar_readonly v)) (map init_data2byte (sublist 0 (Zlength (gvar_init v)-1) (gvar_init v))) (gv i)
  |-- globvar2pred gv (i, v).
Proof.
intros gv i v HEAD BOUND ZERO; intros.
destruct HEAD as [b ?].
destruct v;
unfold globvar2pred; simpl in *.
rewrite H; clear gvar_volatile H.
rename gvar_init into bl0.
set (bl := sublist 0 (Zlength bl0 - 1) bl0) in *.
assert (exists al, map Init_int8 al = bl
         /\ ~In Byte.zero (map (Basics.compose Byte.repr Int.intval) al)). {
  clear - H0. clearbody bl.
  induction bl. exists nil; auto.
  simpl in H0.
  destruct a; try discriminate H0.
  rewrite andb_true_iff in H0. destruct H0.
  destruct (IHbl H0) as [j [H3 H4]].
  exists (i::j); simpl.
  split.
  f_equal. auto.
  contradict H4. destruct H4; auto.
  simpl in H.
  exfalso; clear - H1 H.
  rewrite !andb_true_iff in H; destruct H as [? [? ?]].
  forget (Int.intval i) as j. clear i.
  apply negb_true_iff, Z.eqb_neq in H.
  apply Z.leb_le in H0. apply Z.ltb_lt in H2.
  assert (Byte.signed (Byte.repr j) = Byte.signed (Byte.zero)) by congruence.
  rewrite Byte.signed_repr in H3 by rep_lia. contradiction.
}
rewrite H2.
destruct H as [al [H3 H3']].
subst bl.
replace bl0 with (map Init_int8 (al ++ [Int.zero])).
 2:{ rewrite map_app. rewrite H3.
      simpl map. rewrite <- ZERO. list_solve.
}
eapply derives_trans; [ | apply init_data_tarray_tuchar_rev ].
2: list_solve.
2:{ rewrite <- H3 in H0. clear - H0.
  apply List.Forall_app.
  split;[ | repeat constructor; rewrite Int.unsigned_zero; rep_lia].
  induction al; simpl in *.
  constructor.
  rewrite !andb_true_iff in H0; destruct H0 as [[ ? [??]] ?].
  constructor; auto.
  apply Z.leb_le in H0. apply Z.ltb_lt in H1.
  change Int.intval with Int.unsigned in *. rep_lia.
}
unfold cstring. Intros.
rewrite data_at_tarray_tschar_tuchar.
rewrite !Zlength_map.
assert (map Vubyte (map init_data2byte (map Init_int8 al)) = map Vint al). {
  rewrite <- H3 in H0.
  clear - H0.
  induction al; simpl in *; auto.
  rewrite !andb_true_iff in H0.
  destruct H0 as [[? [? ?]] ?].
  f_equal; auto.
  apply Z.leb_le in H0. apply Z.ltb_lt in H1.
  unfold Vubyte. f_equal.
  rewrite Byte.unsigned_repr by rep_lia.
  change (Int.intval a) with (Int.unsigned a).
  rewrite Int.repr_unsigned. auto.
}
autorewrite with sublist.
apply derives_refl'.
f_equal.
rewrite sublist_map.
autorewrite with sublist.
rewrite !map_app.
f_equal.
auto.
Qed.

Definition lit_ok (v: globvar type) : bool :=
  (0 <? Zlength (gvar_init v)) && (Zlength (gvar_init v) <? Ptrofs.modulus) &&
  (match Znth (Zlength (gvar_init v) - 1) (gvar_init v) with
   | Init_int8 i => Int.eq i Int.zero | _ => false end) &&
  negb (gvar_volatile v) &&
  forallb ok_initbyte (sublist 0 (Zlength (gvar_init v)-1) (gvar_init v)) &&
  eqb_type (gvar_info v) (tarray tschar (Zlength (gvar_init v))) &&
  gvar_readonly v.

Lemma lit_ok_spec: forall v, lit_ok v = true ->
  0 < Zlength (gvar_init v) < Ptrofs.modulus /\
  Znth (Zlength (gvar_init v)-1) (gvar_init v) = Init_int8 Int.zero /\
  gvar_volatile v = false /\
  forallb ok_initbyte (sublist 0 (Zlength (gvar_init v)-1) (gvar_init v)) = true /\
  gvar_info v = tarray tschar (Zlength (gvar_init v)) /\
  gvar_readonly v = true.
Proof.
  intros. unfold lit_ok in H. rewrite !andb_true_iff in H.
  destruct H as [[[[[[H1 H2] H3] H4] H5] H6] H7].
  apply Z.ltb_lt in H1. apply Z.ltb_lt in H2.
  repeat split; auto.
  - destruct (Znth _ _); try discriminate. apply Int.same_if_eq in H3. subst; auto.
  - destruct (gvar_volatile v); auto; discriminate.
  - apply eqb_type_true; auto.
Qed.

Lemma lit_fwd: forall gv i v, headptr (gv i) -> lit_ok v = true ->
  globvar2pred gv (i, v) |-- lit gv i v.
Proof.
  intros. destruct (lit_ok_spec v H0) as (A & B & C & D & E & F).
  eapply derives_trans; [apply globvar2pred_cstring; auto|].
  unfold lit, litb. rewrite F. apply derives_refl.
Qed.

Lemma lit_bwd: forall gv i v, headptr (gv i) -> lit_ok v = true ->
  lit gv i v |-- globvar2pred gv (i, v).
Proof.
  intros. destruct (lit_ok_spec v H0) as (A & B & C & D & E & F).
  eapply derives_trans; [|apply globvar2pred_cstring_rev; auto].
  unfold lit, litb. rewrite F. apply derives_refl.
Qed.

Lemma std_eq: forall gv id fid, headptr (gv fid) -> headptr (gv id) ->
  globvar2pred gv (id, {| gvar_info := tptr (Tstruct __IO_FILE noattr);
                          gvar_init := [Init_addrof fid (Ptrofs.repr 0)];
                          gvar_readonly := true; gvar_volatile := false |}) =
  data_at Ers (tptr t_FILE) (gv fid) (gv id).
Proof.
  intros gv id fid [b Hb] Hid. unfold globvar2pred. simpl. rewrite Hb. rewrite sepcon_emp.
  replace (Ptrofs.add Ptrofs.zero (Ptrofs.repr 0)) with Ptrofs.zero by reflexivity.
  rewrite <- (mapsto_data_at'' Ers (tptr t_FILE) (Vptr b Ptrofs.zero) (Vptr b Ptrofs.zero) (gv id))
    by (auto; reflexivity).
  reflexivity.
Qed.

Lemma lit_eq: forall gv i v, headptr (gv i) -> lit_ok v = true ->
  globvar2pred gv (i, v) = lit gv i v.
Proof. intros. apply pred_ext; [apply lit_fwd | apply lit_bwd]; auto. Qed.

Definition gids : list ident :=
  [___stringlit_1; ___stringlit_2; ___stringlit_3; ___stringlit_4; ___stringlit_5;
   ___stringlit_6; ___stringlit_7; ___stringlit_8; ___stringlit_9; ___stringlit_10;
   ___stringlit_11; ___stringlit_12; ___stringlit_13; ___stringlit_14; ___stringlit_15;
   ___stringlit_16; ___stringlit_17; ___stringlit_18; ___stringlit_19; ___stringlit_20;
   ___stringlit_21; ___stringlit_22; ___stringlit_23; ___stringlit_24; ___stringlit_25;
   ___stringlit_26; ___stringlit_27; ___stringlit_28; ___stringlit_29; ___stringlit_30;
   ___stringlit_31; ___stringlit_32; ___stringlit_33; ___stringlit_34; ___stringlit_35;
   ___stdin_FILE; ___stdout_FILE; ___stderr_FILE; _stdin; _stdout; _stderr].

Lemma globs_eq: forall gv, (forall id, In id gids -> headptr (gv id)) ->
  globvars2pred gv (prog_vars prog) = (G gv * lit gv ___stringlit_35 v___stringlit_35)%logic.
Proof.
  intros gv HP.
  unfold prog_vars, prog. rewrite prog_defs_Clight_mkprogram. simpl globvars2pred.
  unfold globvars2pred. cbn [map fold_right].
  rewrite (std_eq gv _stdin ___stdin_FILE (HP ___stdin_FILE ltac:(simpl; tauto))
             (HP _stdin ltac:(simpl; tauto)) : globvar2pred gv (_stdin, v_stdin) = _).
  rewrite (std_eq gv _stdout ___stdout_FILE (HP ___stdout_FILE ltac:(simpl; tauto))
             (HP _stdout ltac:(simpl; tauto)) : globvar2pred gv (_stdout, v_stdout) = _).
  rewrite (std_eq gv _stderr ___stderr_FILE (HP ___stderr_FILE ltac:(simpl; tauto))
             (HP _stderr ltac:(simpl; tauto)) : globvar2pred gv (_stderr, v_stderr) = _).
  change (globvar2pred gv (___stdin_FILE, v___stdin_FILE)) with emp.
  change (globvar2pred gv (___stdout_FILE, v___stdout_FILE)) with emp.
  change (globvar2pred gv (___stderr_FILE, v___stderr_FILE)) with emp.
  repeat match goal with |- context [globvar2pred gv (?id, ?v)] =>
    rewrite (lit_eq gv id v (HP id ltac:(simpl; tauto)) ltac:(reflexivity)) end.
  unfold G, Gx, Gr. apply pred_ext; cancel.
Qed.
