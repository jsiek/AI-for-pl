(* picolExpr *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import Picol.picol_full Picol.spec_picol Picol.picol_defs Picol.verif_libc Picol.verif_util
  Picol.verif_parse Picol.verif_parse3 Picol.verif_strutil.

Lemma lit8_len: Zlength (litb v___stringlit_8) = 4.
Proof. reflexivity. Qed.

Lemma cstring_split_at: forall sh s sp k, 0 <= k <= Zlength s -> ~ In Byte.zero s ->
  field_compatible (tarray tschar (Zlength s + 1)) [] sp ->
  data_at sh (tarray tschar (Zlength s + 1)) (map Vbyte (s ++ [Byte.zero])) sp =
  (data_at sh (tarray tschar k) (map Vbyte (sublist 0 k s)) sp *
   cstring sh (sublist k (Zlength s) s) (offset_val k sp))%logic.
Proof.
  intros.
  replace (map Vbyte (s ++ [Byte.zero]))
    with (map Vbyte (sublist 0 k s) ++ map Vbyte (sublist k (Zlength s) s ++ [Byte.zero])) by list_solve.
  rewrite (arr_split2 sh (Zlength s + 1) k (Zlength s - k + 1)) by (auto; try lia; list_solve).
  unfold cstring. rewrite prop_true_andp.
  2: { intro X. apply sublist_In in X. auto. }
  replace (Zlength (sublist k (Zlength s) s)) with (Zlength s - k) by list_solve.
  reflexivity.
Qed.

Lemma add_ptr_n: forall p j n, isptr p -> Int.min_signed <= n <= Int.max_signed ->
  force_val (sem_add_ptr_int tschar Signed (offset_val j p) (Vint (Int.repr n))) = offset_val (j + n) p.
Proof.
  intros. destruct p; try contradiction. unfold offset_val, sem_add_ptr_int. simpl.
  f_equal. rewrite Ptrofs.add_assoc. f_equal.
  unfold Ptrofs.of_ints. rewrite Int.signed_repr by lia.
  rewrite ptrofs_mul_repr, ptrofs_add_repr. f_equal. lia.
Qed.

Lemma cfold: forall sh s p, ~ In Byte.zero s ->
  data_at sh (tarray tschar (Zlength s + 1)) (map Vbyte (s ++ [Byte.zero])) p |-- cstring sh s p.
Proof. intros. unfold cstring. entailer!. Qed.

(* keep only the variables of picolExpr that live across statements *)
Ltac keep_q Q :=
  lazymatch Q with
  | nil => constr:(@nil localdef)
  | temp ?id ?v :: ?Q' =>
      let r := keep_q Q' in
      let b := eval compute in
        (Pos.eqb id _a || Pos.eqb id _i || Pos.eqb id _p || Pos.eqb id _err || Pos.eqb id _prec)%bool in
      match b with true => constr:(temp id v :: r) | false => r end
  | ?x :: ?Q' => let r := keep_q Q' in constr:(x :: r)
  end.

Ltac keep_q_noa Q :=
  lazymatch Q with
  | nil => constr:(@nil localdef)
  | temp ?id ?v :: ?Q' =>
      let r := keep_q_noa Q' in
      let b := eval compute in
        (Pos.eqb id _i || Pos.eqb id _p || Pos.eqb id _err || Pos.eqb id _prec)%bool in
      match b with true => constr:(temp id v :: r) | false => r end
  | ?x :: ?Q' => let r := keep_q_noa Q' in constr:(x :: r)
  end.

Ltac drop_pp pp R :=
  lazymatch R with
  | data_at Tsh (tptr tschar) _ pp :: ?R' => R'
  | ?x :: ?R' => let r := drop_pp pp R' in constr:(x :: r)
  end.

Ltac show_goal := match goal with |- ?g => idtac g end.

Ltac ws_loop pp sp s k0 :=
  match goal with |- semax _ (PROPx ?P (LOCALx ?Q (SEPx ?R))) _ _ =>
  let Q' := keep_q Q in let R' := drop_pp pp R in
  forward_loop (EX k1: Z, PROPx ((k0 <= k1 <= Zlength s) :: P)
                  (LOCALx Q' (SEPx (data_at Tsh (tptr tschar) (offset_val k1 sp) pp :: R'))))%assert
    break: (EX k1: Z, PROPx ((k0 <= k1 <= Zlength s) :: P)
                  (LOCALx Q' (SEPx (data_at Tsh (tptr tschar) (offset_val k1 sp) pp :: R'))))%assert
  end.

Lemma lit_valid: forall gv i0, 0 <= i0 < 4 ->
  lit gv ___stringlit_8 v___stringlit_8 |-- valid_pointer (offset_val i0 (gv ___stringlit_8)).
Proof.
  intros. unfold lit, cstring. Intros. apply arr_valid; auto; try (rewrite lit8_len; lia); try list_solve.
Qed.

Lemma Znth_lit8_nz: forall i0 c, Znth i0 (litb v___stringlit_8) = c -> c <> Byte.zero ->
  0 <= i0 < 4.
Proof.
  intros. rewrite <- lit8_len. destruct (zlt i0 0); [rewrite Znth_underflow in H by lia; subst; contradiction|].
  destruct (zlt i0 (Zlength (litb v___stringlit_8))); [lia|].
  rewrite Znth_overflow in H by lia. subst; contradiction.
Qed.

Ltac ws_body pp sp s gv tv :=
  let k1 := fresh "k1" in Intros k1;
  forward; char_addr k1 s sp; forward;
  match goal with |- semax _ (PROPx ?P (LOCALx ?Q (SEPx ?R))) _ _ =>
    forward_if (EX b: bool, PROPx ((b = true -> k1 < Zlength s) :: P)
                  (LOCALx (temp tv (Val.of_bool b) :: Q) (SEPx R)))%assert end;
  [ let Hc := fresh "Hc" in
    match goal with H: typed_true tschar _ |- _ => apply typed_true_byte in H; rename H into Hc end;
    forward; forward;
    forward_call (Ers, gv ___stringlit_8, litb v___stringlit_8, Znth k1 (s ++ [Byte.zero]));
    [ unfold lit; cancel | ];
    let r := fresh "r" in Intros r;
    change (cstring Ers (litb v___stringlit_8) (gv ___stringlit_8)) with (lit gv ___stringlit_8 v___stringlit_8);
    let i0 := fresh "i0" in let Hi0 := fresh "Hi0" in let Hf := fresh "Hf" in
    match goal with H: (exists _, _) \/ _ |- _ =>
      destruct H as [(i0 & Hi0 & Hf & ->)|(Hf & ->)] end;
    [ pose proof (Znth_lit8_nz _ _ Hi0 Hc);
      forward;
      [ entailer!; apply denote_tc_test_eq_split; [|apply valid_pointer_null];
        repeat apply sepcon_valid_pointer1; apply lit_valid; lia | ];
      Exists true;
      assert_PROP (isptr (gv ___stringlit_8)) by (unfold lit, cstring; entailer!);
      entailer!; split; [intros _; lt_len k1 s|];
      destruct (gv ___stringlit_8); try contradiction; reflexivity
    | forward; Exists false; entailer! ]
  | forward; Exists false; entailer!
  | let b := fresh "b" in Intros b;
    forward_if;
    [ forward; forward; Exists (k1 + 1);
      match goal with H: b = true -> _ |- _ => destruct b; [specialize (H eq_refl)| discriminate] end;
      entailer!; change (sizeof tschar) with 1; cancel
    | forward; Exists k1; entailer! ] ].

Ltac char_addr1 j s text :=
  assert_PROP (force_val (sem_add_ptr_int tschar Signed (offset_val j text) (Vint (Int.repr 1))) =
               field_address (tarray tschar (Zlength s + 1)) (SUB (j + 1)) text)
    by (rewrite add_ptr_n by (auto; rep_lia); entailer!; unfold field_address; rewrite if_true;
        [simpl; f_equal; lia | auto with field_compatible]).

Ltac lt_len1 j s :=
  let Hge := fresh in
  destruct (zlt (j + 1) (Zlength s)) as [?|Hge]; [auto | exfalso;
    let Ej := fresh in assert (Ej: j + 1 = Zlength s) by lia; rewrite Ej in *;
    rewrite ?tail_char in *; repeat kill_zero ].

Ltac and_cond tv j s sp n :=
  match goal with |- semax _ (PROPx ?P (LOCALx ?Q (SEPx ?R))) _ _ =>
    forward_if (EX b: bool, PROPx ((b = true -> j + 1 < Zlength s) :: P)
                  (LOCALx (temp tv (Val.of_bool b) :: Q) (SEPx R)))%assert end;
  [ assert (j < Zlength s) by lt_len j s;
    forward; char_addr1 j s sp; forward; forward;
    Exists (Int.eq (Int.repr (Byte.signed (Znth (j + 1) (s ++ [Byte.zero])))) (Int.repr n));
    entailer!;
    repeat match goal with |- _ /\ _ => split end;
    try (let E := fresh "E" in intro E; lt_len1 j s);
    try (match goal with |- context [Int.eq ?a ?b] => destruct (Int.eq a b); reflexivity end)
  | forward; Exists false; entailer!
  | let b := fresh "b" in Intros b ].

Ltac or_cond tv j s n2 :=
  match goal with |- semax _ (PROPx ?P (LOCALx ?Q (SEPx ?R))) _ _ =>
    forward_if (EX b: bool, PROPx ((b = true -> j < Zlength s) :: P)
                  (LOCALx (temp tv (Val.of_bool b) :: Q) (SEPx R)))%assert end;
  [ forward; Exists true; entailer!; try intros _; lt_len j s
  | forward; forward; forward;
    Exists (Int.eq (Int.repr (Byte.signed (Znth j (s ++ [Byte.zero])))) (Int.repr n2));
    entailer!; close_or j s
  | let b := fresh "b" in Intros b ].

Ltac chain_post j s :=
  match goal with |- semax _ (PROPx ?P (LOCALx ?Q (SEPx ?R))) _ _ =>
   let Q' := keep_q Q in
   forward_if (EX op: Z, EX oprec: Z, EX ln: Z,
     PROPx ((-128 <= op <= 127) :: (0 <= oprec <= 4) ::
            (ln = 1 /\ j < Zlength s \/ ln = 2 /\ j + 1 < Zlength s) :: P)
     (LOCALx (temp _op (Vint (Int.repr op)) :: temp _oprec (Vint (Int.repr oprec)) ::
              temp _len (Vint (Int.repr ln)) :: Q') (SEPx R)))%assert end.

Ltac use_b :=
  match goal with
  | H: typed_true _ (Val.of_bool ?b) |- _ => destruct b; [| inv H]
  | H: typed_true _ (if ?b then _ else _) |- _ => destruct b; [| inv H] end;
  repeat match goal with H: true = true -> _ |- _ => specialize (H eq_refl) end.

Ltac close_chain j s :=
  entailer!;
  repeat match goal with |- _ /\ _ => split end; try lia;
  first [ left; split; [reflexivity | lt_len j s] | right; split; [reflexivity | lia] | idtac ].

Ltac op2 j s op prc :=
  use_b; forward; forward; forward; Exists op prc 2; close_chain j s.
Ltac op1 j s prc :=
  use_b; forward; forward; forward;
  pose proof (Byte.signed_range (Znth j (s ++ [Byte.zero])));
  Exists (Byte.signed (Znth j (s ++ [Byte.zero]))) prc 1; close_chain j s.

Ltac sw_fin :=
  match goal with |- ENTAIL _, PROPx _ (LOCALx ?Q _) |-- _ =>
    match Q with context [temp _a (Vfloat ?x)] => Exists x; entailer! end end.

Ltac sw_bool tv :=
  match goal with |- semax _ (PROPx ?P (LOCALx ?Q (SEPx ?R))) _ _ =>
   forward_if (EX t: int, PROPx P (LOCALx (temp tv (Vint t) :: Q) (SEPx R)))%assert end;
  [ forward; match goal with |- ENTAIL _, PROPx _ (LOCALx (temp tv (Vint ?x) :: _) _) |-- _ =>
      Exists x end; entailer!
  | forward; match goal with |- ENTAIL _, PROPx _ (LOCALx (temp tv (Vint ?x) :: _) _) |-- _ =>
      Exists x end; entailer!
  | let t := fresh "t" in Intros t; forward; forward; sw_fin ].

Ltac ws pp sp s gv k0 tv :=
  ws_loop pp sp s k0; [ Exists k0; entailer! | ws_body pp sp s gv tv | ].

Definition xR gv i lvl rest pp errp sh s sp ve k (e: int) : list mpred :=
  [data_at Tsh (tptr tschar) (offset_val k sp) pp; data_at_ Tsh (tptr tschar) ve;
   lit gv ___stringlit_8 v___stringlit_8; data_at Ews t_interp (Vint (Int.repr lvl), rest) i;
   data_at Tsh tint (Vint e) errp;
   data_at sh (tarray tschar (Zlength s + 1)) (map Vbyte (s ++ [Byte.zero])) sp].

Definition xst gv i lvl rest pp errp sh s sp ve prec k e a : environ -> mpred :=
  PROPx [0 <= k <= Zlength s]
  (LOCALx [temp _a (Vfloat a); lvar _e (tptr tschar) ve; gvars gv; temp _i i; temp _p pp;
           temp _err errp; temp _prec (Vint (Int.repr prec))]
  (SEPx (xR gv i lvl rest pp errp sh s sp ve k e))).

Lemma body_picolExpr: semax_body Vprog Gprog f_picolExpr picolExpr_spec.
Proof.
start_function.
unfold cstring. Intros.
match goal with H: ~ In Byte.zero s |- _ => rename H into Hnz end.
assert_PROP (isptr sp) as Hsp by entailer!.
forward. forward. forward.
forward_if.
{ forward. forward. forward. forward.
  Exists k (Int.repr 1) (Float.of_int (Int.repr 0)).
  unfold cstring. entailer!. replace (lvl + 1 - 1) with lvl by lia. auto. }
rewrite add_repr.
ws pp sp s gv k _t'2.
Intros k1.
forward. char_addr k1 s sp. forward.
forward_if (EX k2: Z, EX e2: int, EX a: float,
  xst gv i (lvl + 1) rest pp errp sh s sp v_e prec k2 e2 a)%assert.
{ (* ( *)
  assert (k1 < Zlength s) by lt_len k1 s.
  forward. forward. rewrite add_ptr_n by (auto; rep_lia).
  sep_apply (cfold sh s sp Hnz).
  forward_call (gv, i, lvl + 1, rest, pp, errp, e, sh, s, sp, k1 + 1, 0).
  Intros vret. destruct vret as [[k' e'] d]. simpl fst in *; simpl snd in *.
  unfold cstring. Intros.
  ws pp sp s gv k' _t'5.
  Intros k3.
  forward. char_addr k3 s sp. forward.
  forward_if.
  { assert (k3 < Zlength s) by lt_len k3 s.
    forward. forward. Exists (k3 + 1) e' d. unfold xst, xR. entailer!.
    change (sizeof tschar) with 1. cancel. }
  { forward. Exists k3 (Int.repr 1) d. unfold xst, xR. entailer!. } }
forward. forward.
forward_if.
{ (* - *)
  assert (k1 < Zlength s) by lt_len k1 s.
  forward. forward. rewrite add_ptr_n by (auto; rep_lia).
  sep_apply (cfold sh s sp Hnz).
  forward_call (gv, i, lvl + 1, rest, pp, errp, e, sh, s, sp, k1 + 1, 5).
  Intros vret. destruct vret as [[k' e'] d]. simpl fst in *; simpl snd in *.
  unfold cstring. Intros.
  forward.
  Exists k' e' (Float.neg d). unfold xst, xR. entailer!. }
forward. forward.
forward_if.
{ (* + *)
  assert (k1 < Zlength s) by lt_len k1 s.
  forward. forward. rewrite add_ptr_n by (auto; rep_lia).
  sep_apply (cfold sh s sp Hnz).
  forward_call (gv, i, lvl + 1, rest, pp, errp, e, sh, s, sp, k1 + 1, 5).
  Intros vret. destruct vret as [[k' e'] d]. simpl fst in *; simpl snd in *.
  unfold cstring. Intros.
  forward.
  Exists k' e' d. unfold xst, xR. entailer!. }
(* strtod *)
forward.
assert_PROP (field_compatible (tarray tschar (Zlength s + 1)) [] sp) by entailer!.
assert_PROP (isptr v_e) by entailer!.
rewrite (cstring_split_at sh s sp k1) by (auto; lia).
rewrite buf_split_tsh. Intros.
forward_call (sh, offset_val k1 sp, sublist k1 (Zlength s) s, v_e).
{ rewrite if_false by (intro; subst; contradiction). cancel. }
Intros vret. destruct vret as [d k']. simpl fst in *; simpl snd in *.
rewrite if_false by (intro; subst; contradiction).
rewrite offset_offset_val.
sep_apply (derives_refl' _ _ (eq_sym (cstring_split_at sh s sp k1 ltac:(lia) Hnz ltac:(auto)))).
forward. forward. forward.
assert (Zlength (sublist k1 (Zlength s) s) = Zlength s - k1) by list_solve.
forward_if (EX e3: int, PROP ()
  LOCAL (temp _a (Vfloat d); lvar _e (tptr tschar) v_e; gvars gv; temp _i i; temp _p pp;
         temp _err errp; temp _prec (Vint (Int.repr prec)))
  SEP (data_at sh (tarray tschar (Zlength s + 1)) (map Vbyte (s ++ [Byte.zero])) sp;
       data_at Ews (tptr tschar) (offset_val (k1 + k') sp) v_e;
       data_at Tsh (tptr tschar) (offset_val k1 sp) pp;
       data_at_ (Share.comp Ews) (tptr tschar) v_e;
       lit gv ___stringlit_8 v___stringlit_8;
       data_at Ews t_interp (Vint (Int.repr (lvl + 1)), rest) i;
       data_at Tsh tint (Vint e3) errp))%assert.
{ entailer!. apply denote_tc_test_eq_split;
  repeat apply sepcon_valid_pointer1; apply arr_valid; auto; try lia; list_solve. }
{ forward. Exists (Int.repr 1). entailer!. }
{ forward. Exists e. entailer!. }
Intros e3.
forward. forward.
sep_apply (data_at_data_at_ Ews (tptr tschar) (offset_val (k1 + k') sp) v_e).
sep_apply (derives_refl' _ _ (eq_sym (buf_split_tsh (tptr tschar) v_e))).
Exists (k1 + k') e3 d. unfold xst, xR. entailer!.
Intros k2 e2 a. unfold xst, xR. Intros.
ws pp sp s gv k2 _t'10.
Intros k3.
forward_loop (EX k4: Z, EX e4: int, EX a4: float, xst gv i (lvl + 1) rest pp errp sh s sp v_e prec k4 e4 a4)%assert
  break: (EX k4: Z, EX e4: int, EX a4: float, xst gv i (lvl + 1) rest pp errp sh s sp v_e prec k4 e4 a4)%assert.
{ Exists k3 e2 a. unfold xst, xR. entailer!. }
{ Intros k4 e4 a4. unfold xst, xR. Intros.
  forward. forward. char_addr k4 s sp. forward.
  and_cond _t'19 k4 s sp 124.
  chain_post k4 s.
  { op2 k4 s 111 0. }
  { forward. forward. and_cond _t'18 k4 s sp 38.
    forward_if.
    { op2 k4 s 97 1. }
    forward. forward. or_cond _t'17 k4 s 47.
    forward_if.
    { op1 k4 s 4. }
    forward. forward. or_cond _t'16 k4 s 45.
    forward_if.
    { op1 k4 s 3. }
    forward. forward. and_cond _t'15 k4 s sp 61.
    forward_if.
    { op2 k4 s 76 2. }
    forward. forward. and_cond _t'14 k4 s sp 61.
    forward_if.
    { op2 k4 s 71 2. }
    forward. forward. and_cond _t'13 k4 s sp 61.
    forward_if.
    { op2 k4 s 69 2. }
    forward. forward. and_cond _t'12 k4 s sp 61.
    forward_if.
    { op2 k4 s 78 2. }
    forward. forward.
    forward_if.
    { forward. forward. Exists 60 2 1. close_chain k4 s. }
    forward. forward.
    forward_if.
    { forward. forward. Exists 62 2 1. close_chain k4 s. }
    forward. Exists k4 e4 a4. unfold xst, xR. entailer!. }
  Intros op oprec ln.
  assert (1 <= ln <= 2 /\ k4 + ln <= Zlength s) as [Hln Hkl] by lia.
  forward_if (prec <= oprec).
  { forward. Exists k4 e4 a4. unfold xst, xR. entailer!. }
  { forward. entailer!. }
  Intros.
  forward. forward. rewrite add_ptr_n by (auto; rep_lia).
  sep_apply (cfold sh s sp Hnz).
  forward_call (gv, i, lvl + 1, rest, pp, errp, e4, sh, s, sp, k4 + ln, oprec + 1).
  Intros vret. destruct vret as [[k5 e5] d]. simpl fst in *; simpl snd in *.
  unfold cstring. Intros.
  match goal with |- semax _ (PROPx ?P (LOCALx ?Q (SEPx ?R))) _ _ =>
    let Q' := keep_q_noa Q in
    forward_if (EX a5: float, PROPx P (LOCALx (temp _a (Vfloat a5) :: Q') (SEPx R)))%assert end.
  1-10: (forward; forward; sw_fin).
  1: sw_bool _t'21.
  1: sw_bool _t'22.
  1: (forward; sw_fin).
  Intros a5.
  ws pp sp s gv k5 _t'23.
  Intros k6.
  Exists k6 e5 a5. unfold xst, xR. entailer!. }
Intros k4 e4 a4. unfold xst, xR. Intros.
forward. forward. forward.
Exists k4 e4 a4. unfold cstring. entailer!.
replace (lvl + 1 - 1) with lvl by lia. auto.
Qed.
