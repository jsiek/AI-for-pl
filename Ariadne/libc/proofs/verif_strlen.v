Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import Libc.strlen Libc.spec_strlen.

Definition Gprog : funspecs := [strlen_spec].

Lemma byte_signed_zero : forall b,
  typed_false tschar (Vint (Int.repr (Byte.signed b))) -> b = Byte.zero.
Proof.
  intros b H. hnf in H. simpl in H.
  destruct (Int.eq (Int.repr (Byte.signed b)) Int.zero) eqn:E; inv H.
  apply Int.same_if_eq in E.
  assert (Byte.signed b = 0).
  { pose proof (Byte.signed_range b).
    apply (f_equal Int.signed) in E.
    rewrite Int.signed_repr in E by (unfold Byte.min_signed, Byte.max_signed in *; simpl in *; rep_lia).
    rewrite E. reflexivity. }
  rewrite <- (Byte.repr_signed b), H. reflexivity.
Qed.

Lemma body_strlen: semax_body Vprog Gprog f_strlen strlen_spec.
Proof.
start_function.
unfold cstring in *.
rename s into ls.
Intros.
forward.
assert_PROP (isptr str) by entailer!.
forward_loop (EX i : Z,
  PROP (0 <= i < Zlength ls + 1)
  LOCAL (temp _a str; temp _s (offset_val i str))
  SEP (data_at sh (tarray tschar (Zlength ls + 1))
          (map Vbyte (ls ++ [Byte.zero])) str))
  break: (PROP ()
  LOCAL (temp _a str; temp _s (offset_val (Zlength ls) str))
  SEP (data_at sh (tarray tschar (Zlength ls + 1))
          (map Vbyte (ls ++ [Byte.zero])) str)).
- Exists 0. entailer!!.
- Intros i.
  assert_PROP (offset_val i str =
     field_address (tarray tschar (Zlength ls + 1)) [ArraySubsc i] str).
  { entailer!. rewrite field_address_offset by auto with field_compatible.
    simpl. f_equal. lia. }
  forward.
  forward_if.
  + forward.
    assert (Znth i (ls ++ [Byte.zero]) <> Byte.zero).
    { match goal with T : typed_true _ _ |- _ =>
        intro E; rewrite E in T; inv T end. }
    assert (Hi : i < Zlength ls) by cstring.
    Exists (i+1). entailer!!.
  + forward. entailer!!.
    assert (Znth i (ls ++ [Byte.zero]) = Byte.zero).
    { apply byte_signed_zero; auto. }
    assert (i = Zlength ls) by cstring. subst. auto.
- forward.
  entailer!!.
  + destruct str; try contradiction. simpl. unfold sameblock.
    destruct (peq b b); auto. contradiction.
  + apply prop_right. destruct str; try contradiction.
    unfold sem_sub_pp. simpl. rewrite peq_true. simpl.
    rewrite Ptrofs.sub_add_l, Ptrofs.sub_idem, Ptrofs.add_zero_l.
    replace (Ptrofs.divs (Ptrofs.repr (Zlength ls)) (Ptrofs.repr 1))
      with (Ptrofs.repr (Zlength ls)).
    2:{ unfold Ptrofs.divs. rewrite (Ptrofs.signed_repr 1) by rep_lia.
        rewrite Z.quot_1_r, Ptrofs.repr_signed. auto. }
    destruct H2 as (_ & _ & Hsz & _). simpl in Hsz.
    pose proof (Ptrofs.unsigned_range i).
    unfold Vptrofs; simpl. f_equal.
    unfold Ptrofs.to_int64. rewrite Ptrofs.unsigned_repr by rep_lia. auto.
Qed.
