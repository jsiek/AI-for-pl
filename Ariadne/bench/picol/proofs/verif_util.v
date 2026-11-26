Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import Picol.picol_full Picol.spec_picol Picol.picol_defs Picol.verif_libc.

Ltac show_goal := match goal with |- ?g => idtac g end.

Lemma cstring_len: forall sh s p,
  cstring sh s p |-- !! (Zlength s + 1 <= Ptrofs.max_unsigned).
Proof.
  intros. unfold cstring. entailer!.
  destruct H0 as (? & ? & Hsz & _). destruct p; try contradiction.
  simpl in Hsz. pose proof (Ptrofs.unsigned_range i).
  rewrite Z.max_r in Hsz by rep_lia. rep_lia.
Qed.

Lemma Vptrofs_repr: forall x, Vptrofs (Ptrofs.repr x) = Vlong (Int64.repr x).
Proof.
  intros. rewrite (Vptrofs_unfold_true (eq_refl _)).
  rewrite (ptrofs_to_int64_repr (eq_refl _)). auto.
Qed.

Lemma not_in_app_sub: forall (pre s: list byte) j,
  ~ In Byte.zero pre -> ~ In Byte.zero s -> ~ In Byte.zero (pre ++ sublist 0 j s).
Proof.
  intros. intro X. apply in_app_or in X. destruct X; auto.
  apply sublist_In in H1. auto.
Qed.

Lemma ltu64_repr: forall a b, 0 <= a <= Int64.max_unsigned -> 0 <= b <= Int64.max_unsigned ->
  Int64.ltu (Int64.repr a) (Int64.repr b) = (a <? b).
Proof.
  intros. unfold Int64.ltu. rewrite !Int64.unsigned_repr by auto.
  destruct (zlt a b); symmetry; [apply Z.ltb_lt | apply Z.ltb_ge]; lia.
Qed.

Lemma body_fmt_append: semax_body Vprog Gprog f_fmt_append fmt_append_spec.
Proof.
start_function.
unfold cstring. Intros.
rewrite !Vptrofs_repr.
forward_loop (EX j: Z,
  PROP (0 <= j <= Zlength s; Zlength pre + j < n)
  LOCAL (temp _buf buf; temp _n (Vlong (Int64.repr n));
         temp _k (Vlong (Int64.repr (Zlength pre + j))); temp _s (offset_val j sp))
  SEP (data_at sh (tarray tschar n) (map Vbyte (pre ++ sublist 0 j s) ++ sublist j (Zlength rest) rest) buf;
       data_at shs (tarray tschar (Zlength s + 1)) (map Vbyte (s ++ [Byte.zero])) sp))
 break: (EX j: Z,
  PROP (0 <= j <= Zlength s; Zlength pre + j < n)
  LOCAL (temp _buf buf; temp _n (Vlong (Int64.repr n));
         temp _k (Vlong (Int64.repr (Zlength pre + j))); temp _s (offset_val j sp))
  SEP (data_at sh (tarray tschar n) (map Vbyte (pre ++ sublist 0 j s) ++ sublist j (Zlength rest) rest) buf;
       data_at shs (tarray tschar (Zlength s + 1)) (map Vbyte (s ++ [Byte.zero])) sp)).
- Exists 0. entailer!. autorewrite with sublist. auto.
- Intros j.
  assert_PROP (offset_val j sp = field_address (tarray tschar (Zlength s + 1)) (SUB j) sp).
  { entailer!. unfold field_address; rewrite if_true. simpl; f_equal; lia. auto with field_compatible. }
  forward.
  forward_if (EX b: bool,
    PROP (if b then j < Zlength s /\ Zlength pre + j + 1 < n else (j = Zlength s \/ n <= Zlength pre + j + 1))
    LOCAL (temp _t'1 (Val.of_bool b); temp _buf buf; temp _n (Vlong (Int64.repr n));
         temp _k (Vlong (Int64.repr (Zlength pre + j))); temp _s (offset_val j sp))
    SEP (data_at sh (tarray tschar n) (map Vbyte (pre ++ sublist 0 j s) ++ sublist j (Zlength rest) rest) buf;
       data_at shs (tarray tschar (Zlength s + 1)) (map Vbyte (s ++ [Byte.zero])) sp)).
  + match goal with H: typed_true tschar _ |- _ => apply typed_true_byte in H; rename H into Hc end.
    assert (j < Zlength s).
    { destruct (zeq j (Zlength s)); [|lia]. subst. rewrite app_Znth2, Z.sub_diag in Hc by list_solve.
      contradiction. }
    forward. Exists (Zlength pre + j + 1 <? n). entailer!.
    split.
    { match goal with |- context [if ?c then _ else _] => destruct c eqn:E end;
      [apply Z.ltb_lt in E | apply Z.ltb_ge in E]; lia. }
    unfold Int64.cmpu. rewrite ltu64_repr by rep_lia. destruct (_ <? _); reflexivity.
  + match goal with H: typed_false tschar _ |- _ => apply typed_false_byte in H; rename H into Hc end.
    forward. Exists false. entailer!.
    left. destruct (zeq j (Zlength s)); auto.
    rewrite app_Znth1 in Hc by list_solve. exfalso.
    assert (In Byte.zero s) by (rewrite <- Hc; apply Znth_In; lia). contradiction.
  + Intros b. forward_if.
    * destruct b; [|match goal with H: typed_true _ _ |- _ => inv H end].
      match goal with H: _ /\ _ |- _ => destruct H end.
      forward. forward. forward. forward. forward. forward.
      Exists (j+1). entailer!.
      { do 2 f_equal; lia. }
      apply derives_refl'. f_equal.
      rewrite app_Znth1 by lia.
      rewrite (sublist_split 0 j (j+1)) by lia. rewrite sublist_len_1 by lia.
      change (Vint (Int.repr (Byte.signed (Znth j s)))) with (Vbyte (Znth j s)).
      list_solve.
    * destruct b; [match goal with H: typed_false _ _ |- _ => inv H end|].
      forward. Exists j. entailer!.
- Intros j. forward. forward.
  Exists (pre ++ sublist 0 j s) (sublist (j+1) (Zlength rest) rest).
  entailer!.
  { split3. apply not_in_app_sub; auto. list_solve. list_solve. }
  unfold cstring. entailer!.
  apply derives_refl'. f_equal.
  change (Vint (Int.repr 0)) with (Vbyte Byte.zero).
  list_solve.
Qed.

Lemma buf_reshape: forall sh n p (pre: list byte) rest,
  data_at sh (tarray tschar n) (map Vbyte (pre ++ [Byte.zero]) ++ rest) p =
  data_at sh (tarray tschar n) (map Vbyte pre ++ (Vbyte Byte.zero :: rest)) p.
Proof. intros. f_equal. list_solve. Qed.

Lemma make_strbuf: forall sh s n rest p,
  ~ In Byte.zero s /\ Zlength s < n /\ Zlength rest = n - Zlength s - 1 ->
  data_at sh (tarray tschar n) (map Vbyte (s ++ [Byte.zero]) ++ rest) p |-- strbuf sh s n p.
Proof. intros. unfold strbuf. Exists rest. destruct H as [? [? ?]]. entailer!. Qed.

Lemma data_at__buf: forall sh n p,
  data_at_ sh (tarray tschar n) p |-- data_at sh (tarray tschar n) (map Vbyte [] ++ Zrepeat Vundef n) p.
Proof. intros. simpl. unfold data_at_, field_at_, data_at. apply derives_refl. Qed.

Lemma body_fmt_str3: semax_body Vprog Gprog f_fmt_str3 fmt_str3_spec.
Proof.
start_function.
replace_SEP 0 (data_at sh (tarray tschar n) (map Vbyte [] ++ Zrepeat Vundef n) buf).
{ entailer!; simpl; unfold data_at_, field_at_, data_at; apply derives_refl. }
forward_call (sh, buf, n, @nil byte, Zrepeat Vundef n, sha, a, ap).
all: try solve [repeat match goal with |- _ /\ _ => split end; auto; try list_solve; try rep_lia].
Intros vret. destruct vret as [pre1 rest1]. simpl fst in *; simpl snd in *.
rewrite buf_reshape.
forward_call (sh, buf, n, pre1, Vbyte Byte.zero :: rest1, shb, b, bp).
all: try solve [repeat match goal with |- _ /\ _ => split end; auto; try list_solve; try rep_lia].
Intros vret. destruct vret as [pre2 rest2]. simpl fst in *; simpl snd in *.
rewrite buf_reshape.
forward_call (sh, buf, n, pre2, Vbyte Byte.zero :: rest2, shc, c, cp).
all: try solve [repeat match goal with |- _ /\ _ => split end; auto; try list_solve; try rep_lia].
Intros vret. destruct vret as [pre3 rest3]. simpl fst in *; simpl snd in *.
sep_apply (make_strbuf sh pre3 n rest3 buf ltac:(split3; auto; lia)).
Exists pre3. forward. cancel.
Qed.

Lemma split_cstring_tail: forall sh n k (digs: list byte) p,
  0 <= k <= n -> Zlength digs + 1 = n - k -> ~ In Byte.zero digs ->
  field_compatible (tarray tschar n) [] p ->
  data_at sh (tarray tschar n) (Zrepeat Vundef k ++ map Vbyte (digs ++ [Byte.zero])) p =
  (data_at sh (tarray tschar k) (Zrepeat Vundef k) p * cstring sh digs (offset_val k p))%logic.
Proof.
  intros.
  rewrite (split2_data_at_Tarray_app k n sh tschar (Zrepeat Vundef k)) by list_solve.
  rewrite field_address0_offset by auto with field_compatible.
  unfold cstring. rewrite prop_true_andp by auto. simpl. f_equal.
  replace (n - k) with (Zlength digs + 1) by lia. f_equal. f_equal. lia.
Qed.

Lemma digit_val: forall u: int,
  Vint (Int.sign_ext 8 (Int.add (Int.repr 48) (Int.modu u (Int.repr 10)))) =
  Vbyte (Byte.repr (48 + Int.unsigned u mod 10)).
Proof.
  intros. unfold Int.modu. rewrite add_repr.
  rewrite Int.unsigned_repr with (z := 10) by rep_lia.
  assert (0 <= Int.unsigned u mod 10 < 10) by (apply Z.mod_pos_bound; lia).
  forget (Int.unsigned u mod 10) as x.
  unfold Vbyte. f_equal.
  assert (x = 0 \/ x = 1 \/ x = 2 \/ x = 3 \/ x = 4 \/ x = 5 \/ x = 6 \/ x = 7 \/ x = 8 \/ x = 9) by lia.
  repeat destruct H0 as [?|H0]; subst; reflexivity.
Qed.

Lemma digit_nz: forall u: int, Byte.repr (48 + Int.unsigned u mod 10) <> Byte.zero.
Proof.
  intros. assert (0 <= Int.unsigned u mod 10 < 10) by (apply Z.mod_pos_bound; lia).
  intro X. apply (f_equal Byte.unsigned) in X.
  rewrite Byte.unsigned_repr in X by rep_lia. rewrite Byte.unsigned_zero in X. lia.
Qed.

Lemma pow_bound: forall j x, 0 <= j -> 1 <= x -> x * 10 ^ j <= Int.max_unsigned -> j <= 9.
Proof.
  intros. destruct (zle j 9); auto. exfalso.
  assert (10 ^ 10 <= 10 ^ j) by (apply Z.pow_le_mono_r; lia).
  change (10 ^ 10) with 10000000000 in H2.
  assert (10 ^ j <= x * 10 ^ j) by nia.
  rep_lia.
Qed.

Lemma div_bound: forall j (u: int), 0 <= j ->
  Int.unsigned u * 10 ^ j <= Int.max_unsigned ->
  Int.unsigned (Int.divu u (Int.repr 10)) * 10 ^ (j + 1) <= Int.max_unsigned.
Proof.
  intros. unfold Int.divu. rewrite Int.unsigned_repr with (z := 10) by rep_lia.
  pose proof (Int.unsigned_range u).
  rewrite Int.unsigned_repr.
  2:{ split. apply Z.div_pos; lia. apply Z.le_trans with (Int.unsigned u). apply Z.div_le_upper_bound; lia. rep_lia. }
  rewrite Z.pow_add_r by lia. change (10 ^ 1) with 10.
  assert (Int.unsigned u / 10 * 10 <= Int.unsigned u) by (pose proof (Z.mul_div_le (Int.unsigned u) 10); lia).
  assert (0 <= 10 ^ j) by (apply Z.pow_nonneg; lia).
  nia.
Qed.

Lemma body_fmt_int: semax_body Vprog Gprog f_fmt_int fmt_int_spec.
Proof.
start_function.
forward.
forward_if (EX u: int, PROP () LOCAL (temp _t'1 (Vint u); temp _k (Vint (Int.repr 11));
   temp _buf buf; temp _n (Vptrofs (Ptrofs.repr n)); temp _v (Vint (Int.repr v));
   lvar _d (tarray tschar 12) v_d)
  SEP (data_at_ Tsh (tarray tschar 12) v_d; data_at_ sh (tarray tschar n) buf)).
{ forward. Exists (Int.sub (Int.repr 0) (Int.repr v)). entailer!. }
{ forward. Exists (Int.repr v). entailer!. }
Intros u.
forward. forward.
forward_loop (EX u: int, EX digs: list byte,
  PROP (Zlength digs <= 10; ~ In Byte.zero digs; digs = [] \/ u <> Int.zero;
        Int.unsigned u * 10 ^ (Zlength digs) <= Int.max_unsigned)
  LOCAL (temp _k (Vint (Int.repr (11 - Zlength digs))); temp _u (Vint u);
   temp _buf buf; temp _n (Vptrofs (Ptrofs.repr n)); temp _v (Vint (Int.repr v));
   lvar _d (tarray tschar 12) v_d)
  SEP (data_at Tsh (tarray tschar 12) (Zrepeat Vundef (11 - Zlength digs) ++ map Vbyte (digs ++ [Byte.zero])) v_d;
       data_at_ sh (tarray tschar n) buf))
 continue: (EX u: int, EX digs: list byte,
  PROP (1 <= Zlength digs <= 10; ~ In Byte.zero digs;
        Int.unsigned u * 10 ^ (Zlength digs) <= Int.max_unsigned)
  LOCAL (temp _k (Vint (Int.repr (11 - Zlength digs))); temp _u (Vint u);
   temp _buf buf; temp _n (Vptrofs (Ptrofs.repr n)); temp _v (Vint (Int.repr v));
   lvar _d (tarray tschar 12) v_d)
  SEP (data_at Tsh (tarray tschar 12) (Zrepeat Vundef (11 - Zlength digs) ++ map Vbyte (digs ++ [Byte.zero])) v_d;
       data_at_ sh (tarray tschar n) buf))
 break: (EX digs: list byte,
  PROP (1 <= Zlength digs <= 10; ~ In Byte.zero digs)
  LOCAL (temp _k (Vint (Int.repr (11 - Zlength digs)));
   temp _buf buf; temp _n (Vptrofs (Ptrofs.repr n)); temp _v (Vint (Int.repr v));
   lvar _d (tarray tschar 12) v_d)
  SEP (data_at Tsh (tarray tschar 12) (Zrepeat Vundef (11 - Zlength digs) ++ map Vbyte (digs ++ [Byte.zero])) v_d;
       data_at_ sh (tarray tschar n) buf)).
- Exists u (@nil byte). entailer!.
  split. list_solve. pose proof (Int.unsigned_range_2 u). lia.
- Intros u0 digs.
  assert (Hk: Zlength digs <= 9).
  { match goal with H: digs = [] \/ u0 <> Int.zero |- _ => destruct H as [Hn|Hnz] end.
    subst digs. list_solve.
    assert (Hu1: 1 <= Int.unsigned u0).
    { pose proof (Int.unsigned_range u0). destruct (zeq (Int.unsigned u0) 0) as [e|]; [|lia].
      exfalso. apply Hnz. rewrite <- (Int.repr_unsigned u0), e. reflexivity. }
    eapply pow_bound; [list_solve | exact Hu1 | eassumption]. }
  forward. forward. rewrite sub_repr. forward.
  { entailer!; pose proof (Zlength_nonneg digs); lia. }
  forward.
  Exists (Int.divu u0 (Int.repr 10)) (Byte.repr (48 + Int.unsigned u0 mod 10) :: digs).
  entailer!.
  { split3; [list_solve | intros [X|X]; [apply (digit_nz u0); auto | contradiction] |].
    split. rewrite Zlength_cons; unfold Z.succ. apply div_bound; auto. list_solve.
    do 2 f_equal; list_solve. }
  apply derives_refl'. f_equal. rewrite digit_val.
  list_solve.
- Intros u0 digs.
  forward_if.
  + forward. Exists u0 digs. entailer!.
  + forward. Exists digs. entailer!.
- Intros digs.
  forward_if (EX digs: list byte,
  PROP (1 <= Zlength digs <= 11; ~ In Byte.zero digs)
  LOCAL (temp _k (Vint (Int.repr (11 - Zlength digs)));
   temp _buf buf; temp _n (Vptrofs (Ptrofs.repr n)); temp _v (Vint (Int.repr v));
   lvar _d (tarray tschar 12) v_d)
  SEP (data_at Tsh (tarray tschar 12) (Zrepeat Vundef (11 - Zlength digs) ++ map Vbyte (digs ++ [Byte.zero])) v_d;
       data_at_ sh (tarray tschar n) buf)).
  + forward. forward. rewrite sub_repr. forward.
    Exists (Byte.repr 45 :: digs). entailer!.
    { split3. list_solve. intros [X|X]; [discriminate | contradiction]. do 2 f_equal. list_solve. }
    apply derives_refl'. f_equal. list_solve.
  + forward. Exists digs. entailer!.
  + Intros digs1.
    set (k1 := 11 - Zlength digs1).
    assert_PROP (field_compatible (tarray tschar 12) [] v_d) by entailer!.
    rewrite (split_cstring_tail Tsh 12 k1 digs1 v_d) by (auto; subst k1; lia).
    sep_apply (data_at__buf sh n buf).
    forward_call (sh, buf, n, @nil byte, Zrepeat Vundef n, Tsh, digs1, offset_val k1 v_d).
    all: try solve [repeat match goal with |- _ /\ _ => split end; auto; try list_solve; try rep_lia].
    Intros vret. destruct vret as [pre rest]. simpl fst in *; simpl snd in *.
    sep_apply (derives_refl' _ _ (eq_sym (split_cstring_tail Tsh 12 k1 digs1 v_d ltac:(subst k1; lia) ltac:(subst k1; lia) H4 H5))).
    sep_apply (make_strbuf sh pre n rest buf ltac:(split3; auto; lia)).
    Exists pre. forward.
    sep_apply data_at_data_at_. cancel.
Qed.

Lemma body_xrealloc: semax_body Vprog Gprog f_xrealloc xrealloc_spec.
Proof.
start_function.
forward_call (told, p, n, m, gv).
Intros q.
if_tac.
- subst q.
  forward_if (PROP (False) LOCAL () SEP ()).
  + unfold Gx, lit. Intros.
    forward.
    forward_call (Ers, gv ___stringlit_1, litb v___stringlit_1, gv ___stderr_FILE, false, gv).
    { simpl. entailer!. unfold std_stream; auto. }
    forward_call 1.
    Intros. contradiction.
  + contradiction.
- forward_if (PROP () LOCAL (temp _mem q) SEP (mem_mgr gv; Gx gv;
        malloc_token Ews (tarray (projT1 told) m) q *
        data_at Ews (tarray (projT1 told) m)
               (sublist 0 (Z.min n m) (projT2 told) ++
                Zrepeat (default_val (projT1 told)) (m - Z.min n m)) q)).
  + subst q. contradiction.
  + forward. entailer!.
  + forward. Exists q. entailer!.
Qed.

Lemma body_xstrdup: semax_body Vprog Gprog f_xstrdup xstrdup_spec.
Proof.
start_function.
sep_apply (cstring_len sh s str). Intros.
forward_call (sh, s, str).
forward_call (existT (fun t => list (reptype t)) tschar [], nullval, 0, Zlength s + 1, gv).
{ cancel. }
Intros q. simpl projT1 in *. simpl projT2 in *.
sep_apply (data_at_data_at_ Ews (tarray tschar (Zlength s + 1))).
unfold cstring. Intros.
forward_call (Ews, sh, q, str, Zlength s + 1, s ++ [Byte.zero]).
all: try solve [repeat match goal with |- _ /\ _ => split end; auto; try list_solve; try rep_lia].
forward.
Exists q. unfold mstr, cstring. entailer!.
Qed.
