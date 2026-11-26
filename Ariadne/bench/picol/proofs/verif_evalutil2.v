(* More lemmas for picolEval: argv array, token copy, unescape, append. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import Picol.picol_full Picol.spec_picol Picol.picol_defs Picol.verif_util
  Picol.verif_cmd_common Picol.verif_strutil Picol.verif_evalutil.

Definition argv_rep (argv: val) (L: list tok) : mpred :=
  if eq_dec argv nullval then emp
  else (malloc_token Ews (tarray (tptr tschar) (Zlength L)) argv *
        data_at Ews (tarray (tptr tschar) (Zlength L)) (map tk_p L) argv)%logic.

Lemma argv_rep_free: forall argv L,
  argv_rep argv L |-- (if eq_dec argv nullval then emp else
     malloc_token Ews (tarray (tptr tschar) (Zlength L)) argv *
     data_at_ Ews (tarray (tptr tschar) (Zlength L)) argv)%logic.
Proof. intros. unfold argv_rep. if_tac; auto. cancel. Qed.

Lemma argv_rep_nn: forall argv L, argv <> nullval ->
  argv_rep argv L = (malloc_token Ews (tarray (tptr tschar) (Zlength L)) argv *
        data_at Ews (tarray (tptr tschar) (Zlength L)) (map tk_p L) argv)%logic.
Proof. intros. unfold argv_rep. rewrite if_false by auto. auto. Qed.

Lemma argv_rep_null: forall L, argv_rep nullval L = emp.
Proof. intros. unfold argv_rep. rewrite if_true by auto. auto. Qed.

Lemma s_split3: forall (s: list byte) a b, 0 <= a <= b -> b <= Zlength s ->
  map Vbyte (s ++ [Byte.zero]) =
  map Vbyte (sublist 0 a s) ++ map Vbyte (sublist a b s) ++ map Vbyte (sublist b (Zlength s) s ++ [Byte.zero]).
Proof. intros. list_solve. Qed.

Lemma src3: forall sh (s: list byte) a b t, 0 <= a <= b -> b <= Zlength s ->
  field_compatible (tarray tschar (Zlength s + 1)) [] t ->
  data_at sh (tarray tschar (Zlength s + 1)) (map Vbyte (s ++ [Byte.zero])) t =
  (data_at sh (tarray tschar a) (map Vbyte (sublist 0 a s)) t *
   data_at sh (tarray tschar (b - a)) (map Vbyte (sublist a b s)) (offset_val a t) *
   data_at sh (tarray tschar (Zlength s + 1 - b)) (map Vbyte (sublist b (Zlength s) s ++ [Byte.zero]))
     (offset_val b t))%logic.
Proof.
  intros. rewrite (s_split3 s a b) by auto.
  rewrite arr3 by (auto; list_solve).
  rewrite !Zlength_map. rewrite !Zlength_sublist by lia.
  replace (a - 0) with a by lia. replace (a + (b - a)) with b by lia.
  rewrite Zlength_app, Zlength_sublist by lia.
  replace (Zlength s - b + Zlength [Byte.zero]) with (Zlength s + 1 - b) by list_solve.
  reflexivity.
Qed.

Lemma newbuf_split: forall m q, 0 <= m ->
  field_compatible (tarray tschar (m + 1)) [] q ->
  data_at Ews (tarray tschar (m + 1))
    (sublist 0 (Z.min 0 (m + 1)) [] ++ Zrepeat (default_val tschar) (m + 1 - Z.min 0 (m + 1))) q =
  (data_at_ Ews (tarray tschar m) q * data_at Ews (tarray tschar 1) [Vundef] (offset_val m q))%logic.
Proof.
  intros. rewrite Z.min_l by lia. rewrite sublist_nil, app_nil_l. replace (m + 1 - 0) with (m + 1) by lia.
  rewrite Zrepeat_split by lia.
  rewrite (arr_split Ews (m + 1) m) by (auto; try lia; list_solve).
  rewrite data_at_undef. replace (m + 1 - m) with 1 by lia. reflexivity.
Qed.

Lemma newbuf_join: forall (w: list byte) q, field_compatible (tarray tschar (Zlength w + 1)) [] q ->
  (data_at Ews (tarray tschar (Zlength w)) (map Vbyte w) q *
   data_at Ews (tarray tschar 1) [Vundef] (offset_val (Zlength w) q))%logic =
  data_at Ews (tarray tschar (Zlength w + 1)) (map Vbyte w ++ [Vundef]) q.
Proof.
  intros. rewrite (arr_split Ews (Zlength w + 1) (Zlength w)) by (auto; try lia; list_solve).
  replace (Zlength w + 1 - Zlength w) with 1 by lia. reflexivity.
Qed.

Lemma newbuf_join': forall (w: list byte) m q, Zlength w = m ->
  field_compatible (tarray tschar (m + 1)) [] q ->
  (data_at Ews (tarray tschar m) (map Vbyte w) q *
   data_at Ews (tarray tschar 1) [Vundef] (offset_val m q))%logic
  |-- data_at Ews (tarray tschar (m + 1)) (map Vbyte w ++ [Vundef]) q.
Proof. intros. subst m. rewrite newbuf_join by auto. auto. Qed.

Lemma last0_upd: forall (w: list byte) m, Zlength w = m ->
  upd_Znth m (map Vbyte w ++ [Vundef]) (Vint (Int.repr 0)) = map Vbyte (w ++ [Byte.zero]).
Proof. intros. subst. list_solve. Qed.

Lemma upd_last0: forall (w: list byte),
  upd_Znth (Zlength w) (map Vbyte w ++ [Vundef]) (Vint (Int.repr 0)) = map Vbyte (w ++ [Byte.zero]).
Proof. intros. list_solve. Qed.

Lemma not_in_sub: forall (s: list byte) a b, ~ In Byte.zero s -> ~ In Byte.zero (sublist a b s).
Proof. intros. intro X. apply sublist_In in X. auto. Qed.

Lemma tbuf_of_buf: forall w q, ~ In Byte.zero w ->
  (malloc_token Ews (tarray tschar (Zlength w + 1)) q *
   data_at Ews (tarray tschar (Zlength w + 1)) (map Vbyte (w ++ [Byte.zero])) q)%logic
  |-- tbuf (mktok w (Zlength w + 1) q).
Proof.
  intros. unfold tbuf, strbuf. simpl. Exists (@nil val). rewrite app_nil_r. entailer!. list_solve.
Qed.

Lemma tbuf_mstr: forall w q, ~ In Byte.zero w ->
  (malloc_token Ews (tarray tschar (Zlength w + 1)) q *
   data_at Ews (tarray tschar (Zlength w + 1)) (map Vbyte (w ++ [Byte.zero])) q)%logic
  |-- mstr w q.
Proof. intros. unfold mstr, cstring. entailer!. Qed.

Lemma tbuf_unfold: forall x, tbuf x =
  (EX rest: list val,
    !! (~ In Byte.zero (tk_s x) /\ Zlength (tk_s x) < tk_n x /\ Zlength rest = tk_n x - Zlength (tk_s x) - 1) &&
    (malloc_token Ews (tarray tschar (tk_n x)) (tk_p x) *
     data_at Ews (tarray tschar (tk_n x)) (map Vbyte (tk_s x ++ [Byte.zero]) ++ rest) (tk_p x)))%logic.
Proof.
  intros. unfold tbuf, strbuf. apply pred_ext.
  - Intros rest. Exists rest. entailer!.
  - Intros rest. Exists rest. entailer!.
Qed.

Lemma buf_split3: forall sh n k1 k2 (C: list val) p, 0 <= k1 <= k2 -> k2 <= n -> Zlength C = n ->
  field_compatible (tarray tschar n) [] p ->
  data_at sh (tarray tschar n) C p =
  (data_at sh (tarray tschar k1) (sublist 0 k1 C) p *
   data_at sh (tarray tschar (k2 - k1)) (sublist k1 k2 C) (offset_val k1 p) *
   data_at sh (tarray tschar (n - k2)) (sublist k2 n C) (offset_val k2 p))%logic.
Proof.
  intros.
  rewrite <- (sublist_same 0 n C) at 1 by auto.
  rewrite (sublist_split 0 k1 n) by lia. rewrite (sublist_split k1 k2 n) by lia.
  rewrite arr3 by (auto; list_solve).
  rewrite !Zlength_sublist by lia.
  replace (k1 - 0) with k1 by lia. replace (k1 + (k2 - k1)) with k2 by lia. reflexivity.
Qed.

(* ---------- pointer arithmetic ---------- *)

Lemma add_ptr_n: forall p j n, isptr p -> Int.min_signed <= n <= Int.max_signed ->
  force_val (sem_add_ptr_int tschar Signed (offset_val j p) (Vint (Int.repr n))) = offset_val (j + n) p.
Proof.
  intros. destruct p; try contradiction. unfold offset_val, sem_add_ptr_int. simpl.
  f_equal. rewrite Ptrofs.add_assoc. f_equal.
  unfold Ptrofs.of_ints. rewrite Int.signed_repr by lia.
  rewrite ptrofs_mul_repr, ptrofs_add_repr. f_equal. lia.
Qed.

Lemma add_ptr_0n: forall p n, isptr p -> Int.min_signed <= n <= Int.max_signed ->
  force_val (sem_add_ptr_int tschar Signed p (Vint (Int.repr n))) = offset_val n p.
Proof.
  intros. pose proof (add_ptr_n p 0 n H H0). rewrite isptr_offset_val_zero in H1 by auto.
  rewrite Z.add_0_l in H1. auto.
Qed.

Lemma sub_pp_off: forall t x y, isptr t ->
  force_val (sem_sub_pp tschar (offset_val x t) (offset_val y t)) = Vlong (Int64.repr (x - y)).
Proof.
  intros. destruct t; try contradiction. simpl. unfold sem_sub_pp. simpl.
  rewrite peq_true. simpl.
  change (Ptrofs.repr 1) with Ptrofs.one. rewrite Ptrofs.divs_one by (compute; congruence).
  rewrite (Ptrofs.add_commut i (Ptrofs.repr x)), (Ptrofs.add_commut i (Ptrofs.repr y)).
  rewrite Ptrofs.sub_shifted.
  rewrite <- (Vptrofs_repr (x - y)). f_equal.
  unfold Ptrofs.sub. apply Ptrofs.eqm_samerepr.
  apply Ptrofs.eqm_sub; apply Ptrofs.eqm_sym; apply Ptrofs.eqm_unsigned_repr.
Qed.

Lemma tlen_val: forall t a b, isptr t -> 0 <= a <= b -> b <= Int.max_signed ->
  force_val (sem_cast tlong tint (eval_binop Oadd tlong tint
     (eval_binop Osub (tptr tschar) (tptr tschar) (offset_val (b - 1) t) (offset_val a t))
     (Vint (Int.repr 1)))) = Vint (Int.repr (b - a)).
Proof.
  intros. unfold eval_binop. simpl.
  rewrite sub_pp_off by auto. simpl.
  rewrite !Int64.Z_mod_modulus_eq. rewrite Zplus_mod_idemp_l.
  replace (b - 1 - a + 1) with (b - a) by lia. rewrite Z.mod_small by rep_lia. reflexivity.
Qed.

Lemma tc_sub_pp: forall t a b, isptr t -> 0 <= a <= b -> b <= Int.max_signed ->
  (Int64.min_signed <= Int64.signed (Int64.repr (b - 1 - a)) + 1 <= Int64.max_signed) /\
  is_true (sameblock (offset_val (b - 1) t) (offset_val a t)).
Proof.
  intros. split. rewrite Int64.signed_repr by rep_lia. rep_lia.
  destruct t as [| | | | | bb ofs]; try contradiction. unfold sameblock, offset_val.
  destruct (peq bb bb); [reflexivity | congruence].
Qed.

(* ---------- unescaping ---------- *)

Definition unesc_c (c: byte) : byte :=
  if Byte.eq_dec c (Byte.repr 110) then Byte.repr 10
  else if Byte.eq_dec c (Byte.repr 116) then Byte.repr 9
  else if Byte.eq_dec c (Byte.repr 114) then Byte.repr 13
  else c.

Lemma upd_out: forall (out w: list byte) d c, Zlength out = d -> d < Zlength w + 1 ->
  upd_Znth d (map Vbyte (out ++ sublist d (Zlength w + 1) (w ++ [Byte.zero]))) (Vbyte c) =
  map Vbyte ((out ++ [c]) ++ sublist (d + 1) (Zlength w + 1) (w ++ [Byte.zero])).
Proof. intros. list_solve. Qed.

Lemma esc_read: forall (out w: list byte) d j, Zlength out = d -> d <= j -> j <= Zlength w ->
  Znth j (map Vbyte (out ++ sublist d (Zlength w + 1) (w ++ [Byte.zero]))) = Vbyte (Znth j (w ++ [Byte.zero])).
Proof. intros. list_solve. Qed.

Lemma esc_len: forall (out w: list byte) d, Zlength out = d -> d <= Zlength w + 1 ->
  Zlength (map Vbyte (out ++ sublist d (Zlength w + 1) (w ++ [Byte.zero]))) = Zlength w + 1.
Proof. intros. list_solve. Qed.

Lemma esc_done: forall (out w: list byte) d, Zlength out = d -> d <= Zlength w ->
  upd_Znth d (map Vbyte (out ++ sublist d (Zlength w + 1) (w ++ [Byte.zero]))) (Vint (Int.repr 0)) =
  map Vbyte (out ++ [Byte.zero]) ++ map Vbyte (sublist (d + 1) (Zlength w + 1) (w ++ [Byte.zero])).
Proof. intros. list_solve. Qed.

