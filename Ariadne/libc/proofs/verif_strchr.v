Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import Libc.strchr Libc.spec_strchr.

Definition __strchrnul_spec :=
 DECLARE ___strchrnul
  WITH sh: share, str : val, s : list byte, c : byte
  PRE  [ tptr tschar, tint ]
    PROP (readable_share sh; c <> Byte.zero)
    PARAMS (str; Vbyte c)
    SEP (cstring sh s str)
  POST [ tptr tschar ]
   EX i : Z,
    PROP (0 <= i <= Zlength s;
          Forall (fun d => d<>c) (sublist 0 i s);
          i = Zlength s \/ Znth i s = c)
    RETURN (offset_val i str)
    SEP (cstring sh s str).

Definition Gprog : funspecs :=
  ltac:(with_library prog [strlen_spec; __strchrnul_spec; strchr_spec]).

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
