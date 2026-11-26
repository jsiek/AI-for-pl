(* picolParseVar *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import Picol.picol_full Picol.spec_picol Picol.picol_defs Picol.verif_libc Picol.verif_util
  Picol.verif_parse Picol.verif_parse2.

Lemma arr_valid: forall sh n (l: list val) p j, readable_share sh -> 0 <= j < n -> Zlength l = n ->
  data_at sh (tarray tschar n) l p |-- valid_pointer (offset_val j p).
Proof.
  intros sh n l p j Hsh Hj Hl. subst n. saturate_local.
  assert (E: l = sublist 0 j l ++ sublist j (Zlength l) l)
    by (rewrite sublist_rejoin by lia; rewrite sublist_same by lia; auto).
  replace (data_at sh (tarray tschar (Zlength l)) l p)
    with (data_at sh (tarray tschar (Zlength l)) (sublist 0 j l ++ sublist j (Zlength l) l) p)
    by (rewrite <- E; reflexivity).
  rewrite (split2_data_at_Tarray_app j (Zlength l) sh tschar (sublist 0 j l) (sublist j (Zlength l) l))
    by list_solve.
  rewrite field_address0_offset
    by (apply field_compatible0_cons; simpl; split; [lia | auto with field_compatible]).
  apply sepcon_valid_pointer2.
  replace (nested_field_offset (tarray tschar (Zlength l)) (SUB j)) with j by (simpl; lia).
  apply data_at_valid_ptr; [apply readable_nonidentity; auto | simpl; rewrite Z.max_r by lia; lia].
Qed.

(* the character at j is not the terminator *)
Ltac nz_tac :=
  repeat match goal with |- _ -> _ => intro end;
  match goal with Hz: Znth _ _ = Byte.zero |- _ => rewrite Hz in * end;
  change (Byte.signed Byte.zero) with 0 in *;
  first [ lia
        | match goal with H: Int.eq _ _ = true |- _ => vm_compute in H; discriminate H end
        | match goal with H: _ = true |- _ => vm_compute in H; discriminate H end ].

Ltac bpost t j s :=
  match goal with |- semax _ (PROPx ?P (LOCALx ?Q (SEPx ?R))) _ _ =>
    forward_if (EX b: bool,
      PROPx ((b = true -> Znth j (s ++ [Byte.zero]) <> Byte.zero) :: P)
      (LOCALx (temp t (bool2val b) :: Q) (SEPx R)))%assert end.

Lemma body_picolParseVar: semax_body Vprog Gprog f_picolParseVar picolParseVar_spec.
Proof.
start_function. unfold parser_at, cstring. Intros.
assert_PROP (isptr text) by entailer!.
forward. forward. forward. forward. forward. forward.
forward_loop (EX j: Z,
  PROP (k + 1 <= j <= Zlength s)
  LOCAL (temp _p p)
  SEP (data_at Tsh t_parser (text, (offset_val j text, (Vint (Int.repr (Zlength s - j)),
         (offset_val (k + 1) text, (en, (Vint ty, Vint iq)))))) p;
       data_at sh (tarray tschar (Zlength s + 1)) (map Vbyte (s ++ [Byte.zero])) text))%assert
 break: (EX j: Z,
  PROP (k + 1 <= j <= Zlength s)
  LOCAL (temp _p p)
  SEP (data_at Tsh t_parser (text, (offset_val j text, (Vint (Int.repr (Zlength s - j)),
         (offset_val (k + 1) text, (en, (Vint ty, Vint iq)))))) p;
       data_at sh (tarray tschar (Zlength s + 1)) (map Vbyte (s ++ [Byte.zero])) text))%assert.
{ Exists (k + 1). entailer!. pa_eq. }
{ Intros j.
  char_addr j s text.
  forward. forward. forward.
  bpost _t'2 j s.
  { forward. forward. forward. ex_bool _t'2. nz_tac. }
  { forward. Exists false. entailer!. }
  Intros b2.
  bpost _t'3 j s.
  { destruct b2; [|kill_bool]. forward. Exists true. entailer!. }
  { destruct b2; [kill_bool|].
    forward. forward.
    forward_if.
    { forward. forward. forward. forward. ex_bool _t'3. nz_tac. }
    { forward. Exists false. entailer!. } }
  Intros b3.
  bpost _t'4 j s.
  { destruct b3; [|kill_bool]. forward. Exists true. entailer!. }
  { destruct b3; [kill_bool|].
    forward. forward.
    forward_if.
    { forward. forward. forward. forward. ex_bool _t'4. nz_tac. }
    { forward. Exists false. entailer!. } }
  Intros b4.
  bpost _t'5 j s.
  { destruct b4; [|kill_bool]. forward. Exists true. entailer!. }
  { destruct b4; [kill_bool|].
    forward. forward. forward. ex_bool _t'5. nz_tac. }
  Intros b5.
  match goal with |- semax _ ?Pre _ _ => forward_if Pre end.
  { destruct b5; [|kill_bool].
    assert (j < Zlength s).
    { destruct (zlt j (Zlength s)); auto. exfalso.
      assert (j = Zlength s) by lia. subst j.
      match goal with H: true = true -> _ |- _ => apply H; auto end.
      rewrite app_Znth2, Z.sub_diag by lia. reflexivity. }
    forward. forward. forward. forward. forward.
    Exists (j + 1). entailer!. pa_eq. }
  { forward. entailer!. }
  forward. Exists j. entailer!. }
Intros j.
forward. forward.
forward_if (EX st': val, EX ty': int,
  PROP (ptok s text st' (offset_val (j - 1) text))
  LOCAL (temp _p p)
  SEP (data_at Tsh t_parser (text, (offset_val j text, (Vint (Int.repr (Zlength s - j)),
         (st', (offset_val (j - 1) text, (Vint ty', Vint iq)))))) p;
       data_at sh (tarray tschar (Zlength s + 1)) (map Vbyte (s ++ [Byte.zero])) text))%assert.
{ assert (Hv: forall i, 0 <= i <= Zlength s ->
    data_at sh (tarray tschar (Zlength s + 1)) (map Vbyte (s ++ [Byte.zero])) text
    |-- valid_pointer (offset_val i text))
    by (intros; apply arr_valid; [auto | lia | list_solve]).
  apply denote_tc_test_eq_split; apply sepcon_valid_pointer2; apply Hv; lia. }
{ forward. forward. forward. forward. forward.
  Exists (offset_val (j - 1) text) (Int.repr 1).
  rewrite ptr_sub1 by auto. entailer!.
  exists (j - 1), j. split3; [lia | lia | ]. split; auto. }
{ forward. forward. forward.
  Exists (offset_val (k + 1) text) (Int.repr 3).
  rewrite ptr_sub1 by auto. entailer!.
  exists (k + 1), j. split3; [lia | lia | ]. split; auto. }
Intros st' ty'.
forward.
Exists j st' (offset_val (j - 1) text) ty' iq.
unfold parser_at, cstring. entailer!.
Qed.
