Require Import VST.floyd.proofauto. Require Import VST.floyd.library.
Require Import Libc.strcmp Libc.spec_strcmp.

Definition Gprog : funspecs := [strcmp_spec].

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
  (* musl reads the final bytes through (unsigned char * ) casts *)
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
