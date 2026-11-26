(* Lemmas on char arrays and argument sizes, shared by the remaining proofs. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import Picol.picol_full Picol.spec_picol Picol.picol_defs.

Lemma arr_split: forall sh n k (l1 l2: list val) p,
  0 <= k <= n -> Zlength l1 = k -> Zlength l2 = n - k ->
  field_compatible (tarray tschar n) [] p ->
  data_at sh (tarray tschar n) (l1 ++ l2) p =
  (data_at sh (tarray tschar k) l1 p * data_at sh (tarray tschar (n - k)) l2 (offset_val k p))%logic.
Proof.
  intros. rewrite (split2_data_at_Tarray_app k n sh tschar l1 l2) by auto.
  rewrite field_address0_offset
    by (apply field_compatible0_cons; simpl; split; [lia | auto with field_compatible]).
  simpl. replace (0 + 1 * k) with k by lia. reflexivity.
Qed.

Lemma arr_split2: forall sh n k m (l1 l2: list val) p,
  n = k + m -> Zlength l1 = k -> Zlength l2 = m -> 0 <= k -> 0 <= m ->
  field_compatible (tarray tschar n) [] p ->
  data_at sh (tarray tschar n) (l1 ++ l2) p =
  (data_at sh (tarray tschar k) l1 p * data_at sh (tarray tschar m) l2 (offset_val k p))%logic.
Proof.
  intros. subst n. rewrite (arr_split sh (k + m) k l1 l2 p) by (auto; lia).
  replace (k + m - k) with m by lia. reflexivity.
Qed.

Lemma arr_field_address: forall n k p, 0 <= k < n -> field_compatible (tarray tschar n) [] p ->
  offset_val k p = field_address (tarray tschar n) (SUB k) p.
Proof.
  intros. unfold field_address. rewrite if_true. simpl. f_equal. lia.
  apply field_compatible_cons. simpl. split; auto.
Qed.

Lemma upd_app_byte: forall (cat: list byte) b n, Zlength cat < n ->
  upd_Znth (Zlength cat) (map Vbyte cat ++ Zrepeat Vundef (n - Zlength cat)) (Vbyte b) =
  map Vbyte (cat ++ [b]) ++ Zrepeat Vundef (n - Zlength (cat ++ [b])).
Proof. intros. list_solve. Qed.

Lemma not_in_snoc: forall (cat: list byte) b, ~ In Byte.zero cat -> b <> Byte.zero ->
  ~ In Byte.zero (cat ++ [b]).
Proof.
  intros. intro X. apply in_app_or in X. destruct X as [X|[X|X]]; auto.
Qed.

Lemma not_in_app: forall (a b: list byte), ~ In Byte.zero a -> ~ In Byte.zero b ->
  ~ In Byte.zero (a ++ b).
Proof. intros. intro X. apply in_app_or in X. destruct X; auto. Qed.

Lemma arr3: forall sh (l1 l2 l3: list val) n p,
  n = Zlength l1 + Zlength l2 + Zlength l3 -> field_compatible (tarray tschar n) [] p ->
  data_at sh (tarray tschar n) (l1 ++ l2 ++ l3) p =
  (data_at sh (tarray tschar (Zlength l1)) l1 p *
   data_at sh (tarray tschar (Zlength l2)) l2 (offset_val (Zlength l1) p) *
   data_at sh (tarray tschar (Zlength l3)) l3 (offset_val (Zlength l1 + Zlength l2) p))%logic.
Proof.
  intros. rewrite app_assoc.
  pose proof (Zlength_nonneg l1). pose proof (Zlength_nonneg l2). pose proof (Zlength_nonneg l3).
  rewrite (arr_split2 sh n (Zlength l1 + Zlength l2) (Zlength l3) (l1 ++ l2) l3 p)
    by (auto; try lia; list_solve).
  rewrite (arr_split2 sh (Zlength l1 + Zlength l2) (Zlength l1) (Zlength l2) l1 l2 p);
    auto; try lia.
  eapply field_compatible_array_smaller0; [eassumption | lia].
Qed.

Lemma buf3: forall (pre w rest: list byte) n p,
  n = Zlength pre + Zlength w + 1 + Zlength rest -> ~ In Byte.zero w ->
  field_compatible (tarray tschar n) [] p ->
  data_at Ews (tarray tschar n) (map Vbyte (pre ++ w ++ [Byte.zero] ++ rest)) p =
  (data_at Ews (tarray tschar (Zlength pre)) (map Vbyte pre) p *
   cstring Ews w (offset_val (Zlength pre) p) *
   data_at Ews (tarray tschar (Zlength rest)) (map Vbyte rest) (offset_val (Zlength pre + Zlength w + 1) p))%logic.
Proof.
  intros.
  replace (map Vbyte (pre ++ w ++ [Byte.zero] ++ rest))
    with (map Vbyte pre ++ map Vbyte (w ++ [Byte.zero]) ++ map Vbyte rest) by list_solve.
  rewrite (arr3 Ews _ _ _ n p) by (auto; list_solve).
  unfold cstring. rewrite prop_true_andp by auto. rewrite !Zlength_map.
  replace (Zlength (w ++ [Byte.zero])) with (Zlength w + 1) by list_solve.
  replace (Zlength pre + (Zlength w + 1)) with (Zlength pre + Zlength w + 1) by lia.
  reflexivity.
Qed.

Lemma char_cases: forall (a: list byte) j2, 0 <= j2 <= Zlength a -> ~ In Byte.zero a ->
  (j2 < Zlength a /\ Znth j2 (a ++ [Byte.zero]) = Znth j2 a /\ Znth j2 a <> Byte.zero) \/
  (j2 = Zlength a /\ Znth j2 (a ++ [Byte.zero]) = Byte.zero).
Proof.
  intros. destruct (zlt j2 (Zlength a)).
  - left. split; auto. rewrite app_Znth1 by lia. split; auto.
    intro X. apply H0. rewrite <- X. apply Znth_In. lia.
  - right. split. lia. rewrite app_Znth2 by lia. replace (j2 - Zlength a) with 0 by lia. reflexivity.
Qed.

Lemma int_eq_byte: forall c, c <> Byte.zero ->
  Int.eq (Int.repr (Byte.signed c)) (Int.repr 0) = false.
Proof.
  intros. apply Int.eq_false. intro X. apply repr_inj_signed in X.
  - apply H. rewrite <- (Byte.repr_signed c), X. reflexivity.
  - pose proof (Byte.signed_range c). rep_lia.
  - rep_lia.
Qed.

Lemma byte_of_signed: forall c z, Byte.signed c = z -> c = Byte.repr z.
Proof. intros. subst. rewrite Byte.repr_signed. auto. Qed.

Lemma ptr_cmp_eq: forall p j k n,
  field_compatible (tarray tschar n) [] p -> 0 <= j <= n -> 0 <= k <= n ->
  force_val (sem_cast tint tbool
    (eval_binop Oeq (tptr tschar) (tptr tschar) (offset_val j p) (offset_val k p))) =
  bool2val (Z.eqb j k).
Proof.
  intros. destruct H as (Hp & _ & Hsz & _).
  destruct p; try contradiction. simpl in Hsz. rewrite Z.max_r in Hsz by lia.
  pose proof (Ptrofs.unsigned_range i).
  unfold offset_val, eval_binop, force_val, sem_binary_operation'. simpl.
  unfold sem_cmp_pp. simpl. rewrite peq_true. simpl.
  unfold Ptrofs.eq, Ptrofs.add.
  rewrite !(Ptrofs.unsigned_repr j) by rep_lia. rewrite !(Ptrofs.unsigned_repr k) by rep_lia.
  rewrite !Ptrofs.unsigned_repr by rep_lia.
  destruct (Z.eqb_spec j k).
  - subst. rewrite zeq_true. reflexivity.
  - rewrite zeq_false by lia. reflexivity.
Qed.

Lemma to_obuf: forall n p v, isptr p ->
  (malloc_token Ews (tarray tschar n) p * data_at Ews (tarray tschar n) v p)%logic |-- obuf n p.
Proof.
  intros. unfold obuf. rewrite if_false by (intro; subst; contradiction).
  cancel.
Qed.

Lemma obuf_null: forall n, emp |-- obuf n nullval.
Proof. intros. unfold obuf. rewrite if_true by auto. auto. Qed.

Lemma obuf_null': forall n P, P |-- (P * obuf n nullval)%logic.
Proof. intros. unfold obuf. rewrite if_true by auto. rewrite sepcon_emp. auto. Qed.

Lemma add0_ptr: forall p, isptr p ->
  force_val (sem_add_ptr_int tschar Signed p (Vint (Int.repr 0))) = p.
Proof.
  intros. destruct p; try contradiction. simpl.
  first [ rewrite Ptrofs.add_zero; reflexivity
        | f_equal; rewrite <- (Ptrofs.add_zero i) at 2; f_equal
        | normalize ].
Qed.

Lemma first_zero: forall (L: list byte), exists z, 0 <= z <= Zlength L /\
  ~ In Byte.zero (sublist 0 z L) /\ (z = Zlength L \/ (z < Zlength L /\ Znth z L = Byte.zero)).
Proof.
  induction L as [|a L IH].
  - exists 0. simpl. split; [rewrite Zlength_nil; lia|]. split; auto.
  - destruct (Byte.eq_dec a Byte.zero) as [E|E].
    + exists 0. rewrite Zlength_cons. pose proof (Zlength_nonneg L).
      split; [lia|]. split; [simpl; auto|]. right. split; [lia|]. rewrite Znth_0_cons. auto.
    + destruct IH as (z & Hz & Hnz & Hend). exists (z + 1). rewrite Zlength_cons.
      split; [lia|]. split.
      * rewrite sublist_0_cons by lia. replace (z + 1 - 1) with z by lia.
        intros [X|X]; auto.
      * destruct Hend as [->|[Hlt HZ]]; [left; lia|].
        right. split; [lia|]. rewrite Znth_pos_cons by lia. replace (z + 1 - 1) with z by lia. auto.
Qed.

Lemma dat_off0: forall sh e p, isptr e ->
  data_at sh (tptr tschar) e p |-- data_at sh (tptr tschar) (offset_val 0 e) p.
Proof. intros. rewrite isptr_offset_val_zero by auto. apply derives_refl. Qed.

Lemma buf_split_tsh: forall t p,
  data_at_ Tsh t p = (data_at_ Ews t p * data_at_ (Share.comp Ews) t p)%logic.
Proof. intros. symmetry. apply data_at__share_join. apply join_comp_Tsh. Qed.

Lemma interp_refold: forall i st,
  0 <= i_level st <= 128 -> i_frames st <> [] ->
  (malloc_token Ews (tarray t_interp 1) i *
   data_at Ews t_interp (Vint (Int.repr (i_level st)),
     (hdp f_ptr (i_frames st) nullval, (hdp c_ptr (i_cmds st) nullval, i_resultp st))) i *
   frames_rep (i_frames st) * cmds_rep (i_cmds st) * mstr (i_result st) (i_resultp st))%logic
  |-- interp_rep i st.
Proof. intros. unfold interp_rep. entailer!. Qed.

Lemma data_at_undef: forall sh n p,
  data_at sh (tarray tschar n) (Zrepeat Vundef n) p = data_at_ sh (tarray tschar n) p.
Proof. intros. unfold data_at_, field_at_, data_at. reflexivity. Qed.

Lemma Zrepeat_split: forall {A} (x: A) a b, 0 <= a -> 0 <= b ->
  Zrepeat x (a + b) = Zrepeat x a ++ Zrepeat x b.
Proof. intros. symmetry. apply Zrepeat_app; auto. Qed.

Lemma args_size_cons: forall a l, args_size (a :: l) = Zlength a + 1 + args_size l.
Proof. reflexivity. Qed.

Lemma args_size_app:forall a b, args_size (a ++ b) = args_size a + args_size b.
Proof.
  induction a as [|x a IH]; intros; [reflexivity|].
  simpl app. rewrite !args_size_cons, IH. lia.
Qed.

Lemma args_size_nonneg: forall a, 0 <= args_size a.
Proof.
  induction a as [|x a IH]; [unfold args_size; simpl; lia|].
  rewrite args_size_cons. pose proof (Zlength_nonneg x). lia.
Qed.

Lemma args_size_snoc: forall args i j, 0 <= i <= j -> j < Zlength args ->
  args_size (sublist i (j + 1) args) = args_size (sublist i j args) + Zlength (Znth j args) + 1.
Proof.
  intros. rewrite (sublist_split i j (j+1)) by lia. rewrite args_size_app.
  rewrite sublist_len_1 by lia. unfold args_size at 2. simpl. lia.
Qed.

Lemma args_size_mono: forall args i j k, 0 <= i <= j -> j <= k -> k <= Zlength args ->
  args_size (sublist i j args) <= args_size (sublist i k args).
Proof.
  intros. rewrite (sublist_split i j k) by lia. rewrite args_size_app.
  pose proof (args_size_nonneg (sublist j k args)). lia.
Qed.

Lemma args_size_sub: forall args i j, 0 <= i <= j -> j <= Zlength args ->
  args_size (sublist i j args) <= args_size args.
Proof.
  intros. rewrite <- (sublist_same 0 (Zlength args) args) at 2 by auto.
  rewrite (sublist_split 0 i (Zlength args)) by lia.
  rewrite (sublist_split i j (Zlength args)) by lia.
  rewrite !args_size_app.
  pose proof (args_size_nonneg (sublist 0 i args)).
  pose proof (args_size_nonneg (sublist j (Zlength args) args)). lia.
Qed.
