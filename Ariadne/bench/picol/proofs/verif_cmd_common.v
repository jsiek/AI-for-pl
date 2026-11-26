(* Helpers shared by the command proofs: buffers, argv, string literals;
   and picolArityErr. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import Picol.picol_full Picol.spec_picol Picol.picol_defs.

Lemma strbuf_split: forall sh s n rest p,
  ~ In Byte.zero s -> Zlength s < n -> Zlength rest = n - Zlength s - 1 ->
  data_at sh (tarray tschar n) (map Vbyte (s ++ [Byte.zero]) ++ rest) p =
  (cstring sh s p *
   data_at sh (tarray tschar (n - (Zlength s + 1))) rest
     (field_address0 (tarray tschar n) (SUB (Zlength s + 1)) p))%logic.
Proof.
  intros.
  rewrite (split2_data_at_Tarray_app (Zlength s + 1) n sh tschar (map Vbyte (s ++ [Byte.zero]))) by list_solve.
  unfold cstring. rewrite prop_true_andp by auto. reflexivity.
Qed.

Lemma args_pred_app: forall a1 a2 p1 p2, Zlength a1 = Zlength p1 ->
  args_pred (a1 ++ a2) (p1 ++ p2) = (args_pred a1 p1 * args_pred a2 p2)%logic.
Proof.
  induction a1; destruct p1; intros; simpl; try (rewrite emp_sepcon; auto);
  try (rewrite Zlength_nil, Zlength_cons in H; rep_lia);
  try (rewrite Zlength_nil in H; rewrite Zlength_cons in H; rep_lia).
  rewrite !Zlength_cons in H. rewrite IHa1 by lia. rewrite sepcon_assoc. auto.
Qed.

Lemma args_focus: forall j args ptrs, 0 <= j < Zlength args -> Zlength ptrs = Zlength args ->
  args_pred args ptrs =
  (cstring Ews (Znth j args) (Znth j ptrs) *
   (args_pred (sublist 0 j args) (sublist 0 j ptrs) *
    args_pred (sublist (j+1) (Zlength args) args) (sublist (j+1) (Zlength ptrs) ptrs)))%logic.
Proof.
  intros.
  rewrite <- (sublist_same 0 (Zlength args) args) at 1 by auto.
  rewrite <- (sublist_same 0 (Zlength ptrs) ptrs) at 1 by auto.
  rewrite (sublist_split 0 j (Zlength args) args) by lia.
  rewrite (sublist_split 0 j (Zlength ptrs) ptrs) by lia.
  rewrite args_pred_app by list_solve.
  rewrite (sublist_split j (j+1) (Zlength args) args) by lia.
  rewrite (sublist_split j (j+1) (Zlength ptrs) ptrs) by lia.
  rewrite !sublist_len_1 by lia. simpl.
  rewrite <- !sepcon_assoc. rewrite (sepcon_comm (args_pred _ _) (cstring _ _ _)). auto.
Qed.

Definition litp (gv: globals) (x: ident * globvar type) : mpred :=
  cstring Ers (litb (snd x)) (gv (fst x)).
Definition GL (gv: globals) (L: list (ident * globvar type)) : mpred :=
  fold_right_sepcon (map (litp gv) L).
Definition lits : list (ident * globvar type) :=
  [(___stringlit_2, v___stringlit_2); (___stringlit_3, v___stringlit_3);
   (___stringlit_4, v___stringlit_4); (___stringlit_5, v___stringlit_5);
   (___stringlit_6, v___stringlit_6); (___stringlit_7, v___stringlit_7);
   (___stringlit_8, v___stringlit_8); (___stringlit_9, v___stringlit_9);
   (___stringlit_10, v___stringlit_10); (___stringlit_11, v___stringlit_11);
   (___stringlit_12, v___stringlit_12); (___stringlit_13, v___stringlit_13);
   (___stringlit_14, v___stringlit_14); (___stringlit_15, v___stringlit_15);
   (___stringlit_16, v___stringlit_16); (___stringlit_17, v___stringlit_17);
   (___stringlit_18, v___stringlit_18); (___stringlit_19, v___stringlit_19);
   (___stringlit_20, v___stringlit_20); (___stringlit_21, v___stringlit_21);
   (___stringlit_22, v___stringlit_22); (___stringlit_23, v___stringlit_23);
   (___stringlit_24, v___stringlit_24); (___stringlit_25, v___stringlit_25);
   (___stringlit_26, v___stringlit_26); (___stringlit_27, v___stringlit_27);
   (___stringlit_28, v___stringlit_28); (___stringlit_29, v___stringlit_29);
   (___stringlit_30, v___stringlit_30); (___stringlit_31, v___stringlit_31);
   (___stringlit_32, v___stringlit_32); (___stringlit_33, v___stringlit_33);
   (___stringlit_34, v___stringlit_34)].
Definition Gs (gv: globals) : mpred :=
  (data_at Ers (tptr t_FILE) (gv ___stdin_FILE) (gv _stdin) *
   data_at Ers (tptr t_FILE) (gv ___stdout_FILE) (gv _stdout))%logic.

#[export] Instance Inh_lit: Inhabitant (ident * globvar type) := (___stringlit_2, v___stringlit_2).

Lemma Zlength_lits: Zlength lits = 33.
Proof. reflexivity. Qed.

Lemma Gr_GL: forall gv, Gr gv = (GL gv lits * Gs gv)%logic.
Proof. intros. unfold Gr, GL, Gs, lits, litp, lit. simpl. apply pred_ext; cancel. Qed.

Lemma GL_take: forall gv L k, 0 <= k < Zlength L ->
  GL gv L = (litp gv (Znth k L) * GL gv (sublist 0 k L ++ sublist (k+1) (Zlength L) L))%logic.
Proof.
  intros. unfold GL.
  rewrite <- (sublist_same 0 (Zlength L) L) at 1 by auto.
  rewrite (sublist_split 0 k (Zlength L) L) by lia.
  rewrite (sublist_split k (k+1) (Zlength L) L) by lia.
  rewrite sublist_len_1 by lia.
  rewrite !map_app, !fold_right_sepcon_app. simpl.
  apply pred_ext; cancel.
Qed.

#[global] Opaque GL Gs.

Ltac take_lit gv L k i v :=
  rewrite (GL_take gv L k) by (pose proof Zlength_lits; list_solve);
  Intros; change (litp gv (Znth k L)) with (cstring Ers (litb v) (gv i)).

Ltac give_lit gv L k i v :=
  change (cstring Ers (litb v) (gv i)) with (litp gv (Znth k L));
  sep_apply (derives_refl' _ _ (eq_sym (GL_take gv L k
      ltac:(pose proof Zlength_lits; list_solve)))).

Lemma body_picolArityErr: semax_body Vprog Gprog f_picolArityErr picolArityErr_spec.
Proof.
start_function.
unfold G. Intros. rewrite Gr_GL. Intros.
take_lit gv lits 8 ___stringlit_10 v___stringlit_10.
take_lit gv (sublist 0 8 lits ++ sublist (8+1) (Zlength lits) lits) 0 ___stringlit_2 v___stringlit_2.
forward_call (Tsh, v_buf, 1024, Ers, litb v___stringlit_10, gv ___stringlit_10, sh, nm, np,
              Ers, litb v___stringlit_2, gv ___stringlit_2).
Intros s. unfold strbuf. Intros rest.
rewrite strbuf_split by auto.
unfold interp_rep. Intros.
forward_call (gv, i, Vint (Int.repr (i_level st)), hdp f_ptr (i_frames st) nullval,
              hdp c_ptr (i_cmds st) nullval, i_result st, i_resultp st, Tsh, s, v_buf).
Intros q.
sep_apply (derives_refl' _ _ (eq_sym (strbuf_split Tsh s 1024 rest v_buf ltac:(auto) ltac:(auto) ltac:(auto)))).
give_lit gv (sublist 0 8 lits ++ sublist (8+1) (Zlength lits) lits) 0 ___stringlit_2 v___stringlit_2.
give_lit gv lits 8 ___stringlit_10 v___stringlit_10.
sep_apply (data_at_data_at_ Tsh (tarray tschar 1024)).
forward.
Exists s q. unfold interp_rep, set_res, G. rewrite Gr_GL. entailer!.
cbn [i_level i_frames i_cmds i_result i_resultp]. cancel.
Qed.
