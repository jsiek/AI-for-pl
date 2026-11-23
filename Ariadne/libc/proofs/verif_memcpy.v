Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import Libc.memcpy Libc.spec_memcpy.

Definition Gprog : funspecs := [memcpy_spec].

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
