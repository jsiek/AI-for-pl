Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import Picol.picol_full Picol.spec_picol Picol.picol_defs.

Lemma Vbyte_eq_zero: forall b,
  Int.repr (Byte.signed b) = Int.zero -> b = Byte.zero.
Proof.
intros b E.
assert (Byte.signed b = 0).
{ apply (f_equal Int.signed) in E.
  rewrite Int.signed_repr in E. exact E.
  pose proof (Byte.signed_range b).
  assert (Int.min_signed <= Byte.min_signed) by (compute; congruence).
  assert (Byte.max_signed <= Int.max_signed) by (compute; congruence).
  lia. }
rewrite <- (Byte.repr_signed b), H. reflexivity.
Qed.

Lemma typed_true_byte: forall b,
  typed_true tschar (Vint (Int.repr (Byte.signed b))) -> b <> Byte.zero.
Proof.
intros b H E; subst b. unfold typed_true in H. simpl in H. discriminate.
Qed.

Lemma typed_false_byte: forall b,
  typed_false tschar (Vint (Int.repr (Byte.signed b))) -> b = Byte.zero.
Proof.
intros b H. unfold typed_false, strict_bool_val in H. simpl in H.
destruct (Int.eq (Int.repr (Byte.signed b)) Int.zero) eqn:E; simpl in H; inv H.
apply Vbyte_eq_zero. apply Int.same_if_eq in E. exact E.
Qed.

Ltac tt_byte := match goal with H: typed_true tschar _ |- _ => apply typed_true_byte in H end.
Ltac tf_byte := match goal with H: typed_false tschar _ |- _ => apply typed_false_byte in H end.

Lemma body_strlen: semax_body Vprog Gprog f_strlen strlen_spec.
Proof.
start_function.
unfold cstring in *.
rename s into ls.
forward.
forward_loop (EX i : Z,
  PROP (0 <= i < Zlength ls + 1)
  LOCAL (temp _a str; temp _s (offset_val i str))
  SEP (data_at sh (tarray tschar (Zlength ls + 1))
          (map Vbyte (ls ++ [Byte.zero])) str))
 break: (PROP ()
  LOCAL (temp _a str; temp _s (offset_val (Zlength ls) str))
  SEP (data_at sh (tarray tschar (Zlength ls + 1))
          (map Vbyte (ls ++ [Byte.zero])) str)).
*
Exists 0. entailer!.
*
Intros i.
assert_PROP (offset_val i str = field_address (tarray tschar (Zlength ls + 1)) (SUB i) str).
{ entailer!. unfold field_address; rewrite if_true. simpl; f_equal; lia. auto with field_compatible. }
forward.
forward_if.
+ apply typed_true_byte in H2. forward. Exists (i+1). entailer!. cstring.
+ apply typed_false_byte in H2. forward. entailer!. assert (i = Zlength ls) by cstring. subst; auto.
* forward.
  - entailer!. destruct str; try contradiction. simpl. unfold sameblock. destruct (peq b b); simpl; auto.
  - entailer!. destruct str; try contradiction. unfold sem_sub_pp. simpl.
    destruct (eq_block b b); [|congruence]. simpl.
    rewrite Ptrofs.sub_add_l, Ptrofs.sub_idem, Ptrofs.add_zero_l.
    change (Ptrofs.repr 1) with Ptrofs.one. rewrite Ptrofs.divs_one by reflexivity.
    rewrite (Vptrofs_unfold_true (eq_refl _)).
    rewrite (ptrofs_to_int64_repr (eq_refl _)). reflexivity.
Qed.

Lemma zext_byte: forall c,
  Int.zero_ext 8 (Int.repr (Byte.signed c)) = Int.repr (Byte.unsigned c).
Proof.
intros.
rewrite <- (Int.repr_unsigned (Int.zero_ext 8 _)).
rewrite Int.zero_ext_mod by (compute; split; congruence).
f_equal.
rewrite Int.unsigned_repr_eq.
change (two_p 8) with 256.
rewrite <- Znumtheory.Zmod_div_mod; [| lia | reflexivity | exists 16777216; reflexivity].
pose proof (Byte.unsigned_range c).
unfold Byte.signed.
change Byte.half_modulus with 128. change Byte.modulus with 256 in *.
destruct (zlt (Byte.unsigned c) 128).
- apply Z.mod_small; lia.
- replace (Byte.unsigned c - 256) with (Byte.unsigned c + (-1)*256) by lia.
  rewrite Z_mod_plus_full. apply Z.mod_small; lia.
Qed.

Lemma ubyte_inj: forall b c,
  Int.repr (Byte.unsigned b) = Int.repr (Byte.unsigned c) -> b = c.
Proof.
intros.
apply (f_equal Int.unsigned) in H.
pose proof (Byte.unsigned_range b). pose proof (Byte.unsigned_range c).
change Byte.modulus with 256 in *.
rewrite !Int.unsigned_repr in H by rep_lia.
rewrite <- (Byte.repr_unsigned b), <- (Byte.repr_unsigned c), H. reflexivity.
Qed.

Lemma ubyte_nonzero: forall c, c <> Byte.zero ->
  Int.repr (Byte.unsigned c) <> Int.zero.
Proof.
intros c Hc E. apply Hc.
apply ubyte_inj. rewrite E. reflexivity.
Qed.

Lemma break_case: forall ls (c: byte) i,
  ~ In Byte.zero ls -> c <> Byte.zero -> 0 <= i < Zlength ls + 1 ->
  (Znth i (ls ++ [Byte.zero]) = Byte.zero \/ Znth i (ls ++ [Byte.zero]) = c) ->
  0 <= i <= Zlength ls /\ (i = Zlength ls \/ Znth i ls = c).
Proof.
intros.
destruct (zeq i (Zlength ls)).
- subst; split; [lia | auto].
- rewrite app_Znth1 in H2 by lia. split; [lia |].
  destruct H2; [| auto].
  exfalso; apply H; rewrite <- H2; apply Znth_In; lia.
Qed.

Lemma cont_case: forall ls (c: byte) i,
  0 <= i < Zlength ls + 1 -> Forall (fun d => d <> c) (sublist 0 i ls) ->
  Znth i (ls ++ [Byte.zero]) <> Byte.zero -> Znth i (ls ++ [Byte.zero]) <> c ->
  0 <= i + 1 < Zlength ls + 1 /\ Forall (fun d => d <> c) (sublist 0 (i + 1) ls).
Proof.
intros.
assert (i < Zlength ls).
{ destruct (zeq i (Zlength ls)); [| lia]. subst.
  rewrite app_Znth2, Z.sub_diag in H1 by lia. contradiction. }
rewrite app_Znth1 in H2 by lia. split; [lia |].
rewrite (sublist_split 0 i (i + 1)) by lia.
rewrite sublist_len_1 by lia.
apply Forall_app; split; auto.
Qed.

Lemma body___strchrnul: semax_body Vprog Gprog f___strchrnul __strchrnul_spec.
Proof.
start_function.
unfold cstring in *.
rename s into ls.
Intros.
forward.
rewrite zext_byte.
forward_if (PROP ()
  LOCAL (temp _s str; temp _c (Vint (Int.repr (Byte.unsigned c))))
  SEP (data_at sh (tarray tschar (Zlength ls + 1))
          (map Vbyte (ls ++ [Byte.zero])) str)).
{ exfalso. apply (ubyte_nonzero c H). assumption. }
{ forward. entailer!. }
forward_loop (EX i : Z,
  PROP (0 <= i < Zlength ls + 1; Forall (fun d => d <> c) (sublist 0 i ls))
  LOCAL (temp _s (offset_val i str); temp _c (Vint (Int.repr (Byte.unsigned c))))
  SEP (data_at sh (tarray tschar (Zlength ls + 1))
          (map Vbyte (ls ++ [Byte.zero])) str))
 break: (EX i : Z,
  PROP (0 <= i <= Zlength ls; Forall (fun d => d <> c) (sublist 0 i ls);
        i = Zlength ls \/ Znth i ls = c)
  LOCAL (temp _s (offset_val i str))
  SEP (data_at sh (tarray tschar (Zlength ls + 1))
          (map Vbyte (ls ++ [Byte.zero])) str)).
* Exists 0. rewrite sublist_nil. entailer!.
* Intros i.
  assert_PROP (offset_val i str = field_address (tarray tschar (Zlength ls + 1)) (SUB i) str).
  { entailer!. unfold field_address; rewrite if_true. simpl; f_equal; lia. auto with field_compatible. }
  forward.
  forward_if (EX b : bool,
    PROP (if b then Znth i (ls ++ [Byte.zero]) <> Byte.zero /\ Znth i (ls ++ [Byte.zero]) <> c
          else Znth i (ls ++ [Byte.zero]) = Byte.zero \/ Znth i (ls ++ [Byte.zero]) = c)
    LOCAL (temp _t'2 (bool2val b); temp _s (offset_val i str);
           temp _c (Vint (Int.repr (Byte.unsigned c))))
    SEP (data_at sh (tarray tschar (Zlength ls + 1))
          (map Vbyte (ls ++ [Byte.zero])) str)).
  + tt_byte.
    rewrite data_at_tarray_tschar_tuchar.
    assert_PROP (offset_val i str = field_address (tarray tuchar (Zlength ls + 1)) (SUB i) str).
    { entailer!. unfold field_address; rewrite if_true. simpl; f_equal; lia. auto with field_compatible. }
    assert (Zlength (ls ++ [Byte.zero]) = Zlength ls + 1) by (autorewrite with sublist; lia).
    forward.
    { entailer!. unfold Vubyte; simpl.
      pose proof (Byte.unsigned_range_2 (Znth i (ls ++ [Byte.zero]))).
      rewrite Int.unsigned_repr by rep_lia. rep_lia. }
    rewrite Znth_map by lia.
    forward.
    rewrite <- data_at_tarray_tschar_tuchar.
    destruct (zeq (Byte.unsigned (Znth i (ls ++ [Byte.zero]))) (Byte.unsigned c)) as [E|E].
    { Exists false. entailer!. right.
      rewrite <- (Byte.repr_unsigned (Znth i _)), <- (Byte.repr_unsigned c), E. reflexivity. }
    { Exists true. entailer!. all: try (split; auto; intro X; apply E; rewrite X; reflexivity). }
  + tf_byte.
    forward. Exists false. entailer!.
  + Intros b.
    forward_if.
    - destruct b; [| unfold typed_true in *; simpl in *; discriminate].
      forward. Exists (i+1). entailer!.
      match goal with Hb: _ /\ _ |- _ => destruct Hb end.
      apply cont_case; auto.
    - destruct b; [unfold typed_false in *; simpl in *; discriminate |].
      forward. Exists i. entailer!.
      { destruct (break_case ls c i); auto. }
* Intros i. forward. Exists i. entailer!.
Qed.

Lemma body_strchr: semax_body Vprog Gprog f_strchr strchr_spec.
Proof.
start_function.
forward_call (sh, str, s, c).
Intros i.
unfold cstring in *.
rename s into ls.
Intros.
assert (Zlength (ls ++ [Byte.zero]) = Zlength ls + 1) by (autorewrite with sublist; lia).
rewrite data_at_tarray_tschar_tuchar.
assert_PROP (offset_val i str = field_address (tarray tuchar (Zlength ls + 1)) (SUB i) str).
{ entailer!. unfold field_address; rewrite if_true. simpl; f_equal; lia. auto with field_compatible. }
forward.
{ entailer!. unfold Vubyte; simpl.
  pose proof (Byte.unsigned_range_2 (Znth i (ls ++ [Byte.zero]))).
  rewrite Int.unsigned_repr by rep_lia. rep_lia. }
rewrite Znth_map by lia.
rewrite <- data_at_tarray_tschar_tuchar.
destruct (zeq i (Zlength ls)).
- subst i.
  rewrite app_Znth2, Z.sub_diag by lia. rewrite Znth_0_cons.
  forward_if (PROP ()
     LOCAL (temp _t'2 nullval)
     SEP (data_at sh (tarray tschar (Zlength ls + 1))
            (map Vbyte (ls ++ [Byte.zero])) str)).
  + rewrite zext_byte in H6. apply ubyte_inj in H6. congruence.
  + forward. entailer!.
  + forward. Exists nullval. entailer!.
    right. rewrite sublist_same in H1 by lia. split; auto.
- assert (Znth i ls = c) by (destruct H2; [lia | auto]).
  rewrite app_Znth1, H6 by lia.
  forward_if (PROP ()
     LOCAL (temp _t'2 (offset_val i str))
     SEP (data_at sh (tarray tschar (Zlength ls + 1))
            (map Vbyte (ls ++ [Byte.zero])) str)).
  + forward. entailer!.
  + rewrite zext_byte in H7. contradiction.
  + forward. Exists (offset_val i str). entailer!.
    left. exists i. auto.
Qed.

Lemma is_int_Vubyte (b : byte) : is_int I8 Unsigned (Vubyte b).
Proof.
  unfold Vubyte; simpl. pose proof (Byte.unsigned_range_2 b).
  rewrite Int.unsigned_repr by rep_lia. rep_lia.
Qed.

Lemma znth_app_zero (ls : list byte) (i : Z) :
  ~ In Byte.zero ls -> 0 <= i <= Zlength ls ->
  (Znth i (ls ++ [Byte.zero]) = Byte.zero <-> i = Zlength ls).
Proof.
  intros H H1.
  split; [|intro; subst; rewrite app_Znth2, Zminus_diag by lia; auto].
  destruct (zlt i (Zlength ls)); [|lia].
  intro X; lapply (Znth_In i ls); [|lia]. cstring.
Qed.

Lemma int_repr_byte_eq_zero (c : byte) :
  Int.eq (Int.repr (Byte.signed c)) Int.zero =
  (if Byte.eq_dec c Byte.zero then true else false).
Proof.
  destruct (Byte.eq_dec c Byte.zero).
  - subst. reflexivity.
  - apply Int.eq_false. intro X. apply n.
    apply (f_equal Int.signed) in X.
    rewrite Int.signed_repr in X by (pose proof (Byte.signed_range c); rep_lia).
    rewrite <- (Byte.repr_signed c), X. reflexivity.
Qed.

Lemma body_strcmp : semax_body Vprog Gprog f_strcmp strcmp_spec.
Proof.
start_function.
unfold cstring in *.
rename s1 into ls1. rename s2 into ls2.
Intros.
forward_loop (EX i : Z,
  PROP (0 <= i <= Zlength ls1; 0 <= i <= Zlength ls2;
        sublist 0 i ls1 = sublist 0 i ls2)
  LOCAL (temp _l (offset_val i str1); temp _r (offset_val i str2))
  SEP (data_at sh1 (tarray tschar (Zlength ls1 + 1))
          (map Vbyte (ls1 ++ [Byte.zero])) str1;
       data_at sh2 (tarray tschar (Zlength ls2 + 1))
          (map Vbyte (ls2 ++ [Byte.zero])) str2))
 continue: (EX i : Z,
  PROP (0 <= i < Zlength ls1; 0 <= i < Zlength ls2;
        sublist 0 (i+1) ls1 = sublist 0 (i+1) ls2)
  LOCAL (temp _l (offset_val i str1); temp _r (offset_val i str2))
  SEP (data_at sh1 (tarray tschar (Zlength ls1 + 1))
          (map Vbyte (ls1 ++ [Byte.zero])) str1;
       data_at sh2 (tarray tschar (Zlength ls2 + 1))
          (map Vbyte (ls2 ++ [Byte.zero])) str2))
 break: (EX i : Z,
  PROP (0 <= i <= Zlength ls1; 0 <= i <= Zlength ls2;
        sublist 0 i ls1 = sublist 0 i ls2;
        Znth i (ls1 ++ [Byte.zero]) <> Znth i (ls2 ++ [Byte.zero]) \/ i = Zlength ls1)
  LOCAL (temp _l (offset_val i str1); temp _r (offset_val i str2))
  SEP (data_at sh1 (tarray tschar (Zlength ls1 + 1))
          (map Vbyte (ls1 ++ [Byte.zero])) str1;
       data_at sh2 (tarray tschar (Zlength ls2 + 1))
          (map Vbyte (ls2 ++ [Byte.zero])) str2)).
- Exists 0. entailer!.
- Intros i.
  assert_PROP (offset_val i str1 = field_address (tarray tschar (Zlength ls1 + 1)) [ArraySubsc i] str1).
  { entailer!. rewrite field_address_offset.
    - simpl. f_equal. lia.
    - apply field_compatible_cons; simpl; split; [lia | auto]. }
  assert_PROP (offset_val i str2 = field_address (tarray tschar (Zlength ls2 + 1)) [ArraySubsc i] str2).
  { entailer!. rewrite field_address_offset.
    - simpl. f_equal. lia.
    - apply field_compatible_cons; simpl; split; [lia | auto]. }
  assert (Zlength (ls1 ++ [Byte.zero]) = Zlength ls1 + 1) by (autorewrite with sublist; auto).
  assert (Zlength (ls2 ++ [Byte.zero]) = Zlength ls2 + 1) by (autorewrite with sublist; auto).
  forward.
  forward.
  pose proof (znth_app_zero ls1 i H H1) as Hs1.
  pose proof (znth_app_zero ls2 i H0 H2) as Hs2.
  set (c1 := Znth i (ls1 ++ [Byte.zero])) in *.
  set (c2 := Znth i (ls2 ++ [Byte.zero])) in *.
  forward_if (temp _t'1 (Val.of_bool (if Byte.eq_dec c1 c2 then negb (if Byte.eq_dec c1 Byte.zero then true else false) else false))).
  { forward. forward. entailer!!. rewrite int_repr_byte_eq_zero.
    remember (Znth i (ls1 ++ [Byte.zero])) as d1.
    remember (Znth i (ls2 ++ [Byte.zero])) as d2.
    destruct (Byte.eq_dec d1 d2); [|contradiction].
    destruct (Byte.eq_dec d1 Byte.zero); reflexivity. }
  { forward. entailer!!. destruct (Byte.eq_dec c1 c2); [contradiction|reflexivity]. }
  forward_if.
  { forward.
    destruct (Byte.eq_dec c1 c2) as [E|E]; [|inv H8].
    destruct (Byte.eq_dec c1 Byte.zero) as [Hz|Hz]; [inv H8|].
    assert (i <> Zlength ls1) by (intro; apply Hz, Hs1; auto).
    assert (i <> Zlength ls2) by (intro; apply Hz; rewrite E; apply Hs2; auto).
    assert (Hc1 : c1 = Znth i ls1) by (subst c1; rewrite app_Znth1 by lia; auto).
    assert (Hc2 : c2 = Znth i ls2) by (subst c2; rewrite app_Znth1 by lia; auto).
    Exists i. entailer!!.
    rewrite !sublist_last_1 by lia. rewrite H3, <- Hc1, <- Hc2, E. auto. }
  { forward.
    destruct (Byte.eq_dec c1 c2) as [E|E].
    - destruct (Byte.eq_dec c1 Byte.zero) as [Hz|Hz]; [|inv H8].
      Exists i. entailer!!. right. apply Hs1; auto.
    - Exists i. entailer!!. }
- Intros i. forward. forward. Exists (i+1). entailer!.
- Intros i.
  rewrite !data_at_tarray_tschar_tuchar.
  assert_PROP (offset_val i str1 = field_address (tarray tuchar (Zlength ls1 + 1)) [ArraySubsc i] str1).
  { entailer!. rewrite field_address_offset.
    - simpl. f_equal. lia.
    - apply field_compatible_cons; simpl; split; [lia | auto]. }
  assert_PROP (offset_val i str2 = field_address (tarray tuchar (Zlength ls2 + 1)) [ArraySubsc i] str2).
  { entailer!. rewrite field_address_offset.
    - simpl. f_equal. lia.
    - apply field_compatible_cons; simpl; split; [lia | auto]. }
  assert (Zlength (ls1 ++ [Byte.zero]) = Zlength ls1 + 1) by (autorewrite with sublist; auto).
  assert (Zlength (ls2 ++ [Byte.zero]) = Zlength ls2 + 1) by (autorewrite with sublist; auto).
  forward.
  { entailer!!. apply is_int_Vubyte. }
  forward.
  { entailer!!. apply is_int_Vubyte. }
  rewrite !Znth_map by lia.
  rewrite <- !data_at_tarray_tschar_tuchar.
  forward.
  Exists (Int.repr (Byte.unsigned (Znth i (ls1 ++ [Byte.zero])) - Byte.unsigned (Znth i (ls2 ++ [Byte.zero])))).
  entailer!!.
  pose proof (znth_app_zero ls1 i H H1) as Hs1.
  pose proof (znth_app_zero ls2 i H0 H2) as Hs2.
  remember (Znth i (ls1 ++ [Byte.zero])) as c1.
  remember (Znth i (ls2 ++ [Byte.zero])) as c2.
  split.
  2:{ unfold Vubyte. simpl. rewrite sub_repr. reflexivity. }
  { destruct (Byte.eq_dec c1 c2) as [E|E].
    + rewrite E in *. rewrite Z.sub_diag.
      destruct (Int.eq_dec (Int.repr 0) Int.zero) as [_|n]; [|contradiction n; reflexivity].
      destruct H4 as [X|X]; [contradiction|].
      assert (c2 = Byte.zero) by (apply Hs1; auto).
      assert (Y : i = Zlength ls2) by (apply Hs2; auto).
      rewrite <- (sublist_same 0 (Zlength ls1) ls1) by auto.
      rewrite <- (sublist_same 0 (Zlength ls2) ls2) by auto.
      rewrite <- X, <- Y. exact H3.
    + destruct (Int.eq_dec _ Int.zero) as [Q|Q].
      * exfalso. apply E. apply (f_equal Int.signed) in Q.
        pose proof (Byte.unsigned_range_2 c1). pose proof (Byte.unsigned_range_2 c2).
        rewrite Int.signed_repr in Q by rep_lia.
        change (Int.signed Int.zero) with 0 in Q.
        rewrite <- (Byte.repr_unsigned c1), <- (Byte.repr_unsigned c2). f_equal; lia.
      * intro X; subst ls2. apply E. subst c1 c2. reflexivity. }
Qed.

Lemma body_memcpy : semax_body Vprog Gprog f_memcpy memcpy_spec.
Proof.
  start_function.
  rewrite data_at_tarray_tschar_tuchar.
  assert_PROP (field_compatible (tarray tschar n) [] dest) by entailer!.
  rewrite <- memory_block_data_at__tarray_tschar_eq by (rep_lia).
  rewrite memory_block_data_at__tarray_tuchar_eq by (rep_lia).
  forward.
  forward.
  forward_loop
    (EX i : Z,
     PROP (0 <= i <= n)
     LOCAL (temp _d (offset_val i dest); temp _s (offset_val i src);
            temp _dest dest; temp _n (Vlong (Int64.repr (n - i))))
     SEP (data_at shd (tarray tuchar n)
            (map Vubyte (sublist 0 i bytes) ++ Zrepeat Vundef (n - i)) dest;
          data_at shs (tarray tuchar n) (map Vubyte bytes) src))
  continue:
    (EX i : Z,
     PROP (0 <= i < n)
     LOCAL (temp _d (offset_val (i+1) dest); temp _s (offset_val (i+1) src);
            temp _dest dest; temp _n (Vlong (Int64.repr (n - i))))
     SEP (data_at shd (tarray tuchar n)
            (map Vubyte (sublist 0 (i+1) bytes) ++ Zrepeat Vundef (n - (i+1))) dest;
          data_at shs (tarray tuchar n) (map Vubyte bytes) src))
  break:
    (PROP ()
     LOCAL (temp _dest dest)
     SEP (data_at shd (tarray tuchar n) (map Vubyte bytes) dest;
          data_at shs (tarray tuchar n) (map Vubyte bytes) src)).
  - Exists 0. entailer!. rewrite app_nil_l. unfold data_at_, field_at_, data_at. apply derives_refl.
  - Intros i.
    forward_if.
    + assert_PROP (isptr dest /\ isptr src) as Pds by entailer!.
      destruct Pds as [Pd Ps].
      assert (i < n) by lia.
      assert_PROP (offset_val i src = field_address (tarray tuchar n) [ArraySubsc i] src) as Hs.
      { entailer!. rewrite field_address_offset by auto with field_compatible. simpl. f_equal; lia. }
      assert_PROP (offset_val i dest = field_address (tarray tuchar n) [ArraySubsc i] dest) as Hd.
      { entailer!. rewrite field_address_offset by auto with field_compatible. simpl. f_equal; lia. }
      forward. forward. forward. forward.
      forward.
      { entailer!. exact (tc_val_Vubyte _). }
      forward.
      Exists i. entailer!.
      unfold data_at. apply derives_refl'. f_equal.
      rewrite (sublist_split 0 i (i+1)) by lia.
      rewrite sublist_len_1 by lia.
      list_solve.
    + forward. entailer!.
      apply (f_equal Int64.unsigned) in H3.
      rewrite Int64.unsigned_repr in H3 by rep_lia.
      rewrite Int64.unsigned_zero in H3.
      assert (i = Zlength bytes) by lia. subst i.
      rewrite sublist_same by lia. rewrite Z.sub_diag, Zrepeat_0, app_nil_r.
      apply derives_refl.
  - Intros i. forward. Exists (i+1). entailer!. f_equal. f_equal. lia.
  - forward. rewrite !data_at_tarray_tschar_tuchar. cancel.
Qed.

Lemma body_isupper : semax_body Vprog Gprog f_isupper isupper_spec.
Proof.
  start_function.
  forward.
  Exists (Int.repr (if Int.ltu (Int.sub (Int.repr c) (Int.repr 65)) (Int.repr 26) then 1 else 0)).
  entailer!.
Qed.

Lemma body___isupper_l : semax_body Vprog Gprog f___isupper_l __isupper_l_spec.
Proof.
  start_function.
  forward_call c.
  Intros r.
  forward.
  Exists r. entailer!.
Qed.
