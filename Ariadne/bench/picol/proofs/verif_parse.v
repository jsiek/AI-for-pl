Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import Picol.picol_full Picol.spec_picol Picol.picol_defs Picol.verif_libc Picol.verif_util.

Lemma tail_char: forall s, Znth (Zlength s) (s ++ [Byte.zero]) = Byte.zero.
Proof. intros. rewrite app_Znth2, Z.sub_diag by lia. reflexivity. Qed.

Ltac kill_zero :=
  match goal with
  | H: Int.repr _ = Int.repr _ |- _ => vm_compute in H; discriminate H
  | H: typed_true _ _ |- _ => vm_compute in H; discriminate H
  | H: typed_false _ _ |- _ => vm_compute in H; discriminate H
  | H: Int.eq _ _ = true |- _ => vm_compute in H; discriminate H
  | H: _ <> _ |- _ => solve [exfalso; apply H; reflexivity]
  | H: negb (Int.eq _ _) = true |- _ => vm_compute in H; discriminate H
  | H: Byte.signed Byte.zero = _ |- _ => vm_compute in H; discriminate H
  | H: Byte.signed Byte.zero <> _ |- _ => vm_compute in H; lia
  | H: Byte.signed Byte.zero >= _ |- _ => vm_compute in H; lia
  | H: Byte.signed Byte.zero <= _ |- _ => vm_compute in H; lia
  | H: Byte.signed Byte.zero > _ |- _ => vm_compute in H; lia
  | H: Byte.signed Byte.zero < _ |- _ => vm_compute in H; lia
  | H: _ <= Byte.signed Byte.zero |- _ => vm_compute in H; lia
  | H: _ >= Byte.signed Byte.zero |- _ => vm_compute in H; lia
  | H: Int.lt _ _ = true |- _ => vm_compute in H; discriminate H
  | H: Int.lt _ _ = false |- _ => vm_compute in H; discriminate H
  end.

(* in a path where the loop continues, the current char is not the terminator *)
Ltac lt_len j s :=
  let Hge := fresh in
  destruct (zlt j (Zlength s)) as [?|Hge]; [auto |
    exfalso; assert (j = Zlength s) by lia; subst j;
    rewrite ?Z.sub_diag in *; rewrite ?tail_char in *; repeat kill_zero ].

Ltac char_addr j s text :=
  assert_PROP (offset_val j text = field_address (tarray tschar (Zlength s + 1)) (SUB j) text)
    by (entailer!; unfold field_address; rewrite if_true; [simpl; f_equal; lia | auto with field_compatible]).

Ltac fif tv j s p :=
  match goal with |- semax _ (PROPx _ (LOCALx _ (SEPx ?R))) _ _ =>
    forward_if (EX b: bool, PROPx [b = true -> j < Zlength s]
                 (LOCALx [temp tv (Val.of_bool b); temp _p p] (SEPx R)))%assert end.

Ltac close_or j s :=
  repeat match goal with |- _ /\ _ => split end;
  try (let E := fresh in intro E; lt_len j s);
  try (match goal with |- context [Int.eq ?a ?b] => destruct (Int.eq a b); reflexivity end).

Ltac use_imp :=
  repeat match goal with H: true = true -> _ |- _ => specialize (H eq_refl) end.

Ltac stage1 tv j s p n :=
  fif tv j s p;
  [ forward; Exists true; entailer!; lt_len j s
  | forward; forward; forward;
    Exists (Int.eq (Int.repr (Byte.signed (Znth j (s ++ [Byte.zero])))) (Int.repr n));
    entailer!; close_or j s
  | ].

Ltac stageN tv j s p n :=
  let b := fresh "b" in Intros b;
  fif tv j s p;
  [ destruct b; [| match goal with H: typed_true _ _ |- _ => inv H end];
    use_imp; forward; Exists true; entailer!
  | forward; forward; forward;
    Exists (Int.eq (Int.repr (Byte.signed (Znth j (s ++ [Byte.zero])))) (Int.repr n));
    entailer!; close_or j s
  | ].

Lemma ptr_sub1: forall j p, isptr p ->
  force_val (sem_sub_pi tschar Signed (offset_val j p) (Vint (Int.repr 1))) = offset_val (j - 1) p.
Proof.
  intros. destruct p; try contradiction. unfold sem_sub_pi, offset_val. simpl.
  f_equal. rewrite Ptrofs.sub_add_opp, Ptrofs.add_assoc. f_equal.
  unfold Ptrofs.of_ints. rewrite Int.signed_repr by rep_lia.
  change (Ptrofs.repr 1) with Ptrofs.one. rewrite Ptrofs.mul_one.
  change Ptrofs.one with (Ptrofs.repr 1). rewrite Ptrofs.neg_repr.
  rewrite Ptrofs.add_unsigned. apply Ptrofs.eqm_samerepr.
  replace (j - 1) with (j + -1) by lia.
  apply Ptrofs.eqm_add; apply Ptrofs.eqm_sym; apply Ptrofs.eqm_unsigned_repr.
Qed.

Lemma cstring_len2: forall sh s p,
  cstring sh s p |-- !! (Zlength s + 1 <= Ptrofs.max_unsigned /\ isptr p).
Proof.
  intros. unfold cstring. entailer!.
  destruct H0 as (? & ? & Hsz & _). destruct p; try contradiction.
  simpl in Hsz. pose proof (Ptrofs.unsigned_range i).
  rewrite Z.max_r in Hsz by rep_lia. rep_lia.
Qed.

Lemma body_picolInitParser: semax_body Vprog Gprog f_picolInitParser picolInitParser_spec.
Proof.
start_function.
sep_apply (cstring_len2 sh s text). Intros.
forward. forward. forward.
forward_call (sh, s, text).
forward. forward. forward. forward. forward.
unfold parser_at. entailer!.
apply derives_refl'. rewrite Int64.Z_mod_modulus_eq, Z.mod_small by rep_lia. reflexivity.
Qed.

Lemma body_picolParseSep: semax_body Vprog Gprog f_picolParseSep picolParseSep_spec.
Proof.
start_function. unfold parser_at, cstring. Intros.
forward. forward.
forward_loop (EX j: Z,
  PROP (k <= j <= Zlength s)
  LOCAL (temp _p p)
  SEP (data_at Tsh t_parser (text, (offset_val j text, (Vint (Int.repr (Zlength s - j)),
         (offset_val k text, (en, (Vint ty, Vint iq)))))) p;
       data_at sh (tarray tschar (Zlength s + 1)) (map Vbyte (s ++ [Byte.zero])) text))%assert
 break: (EX j: Z,
  PROP (k <= j <= Zlength s)
  LOCAL (temp _p p)
  SEP (data_at Tsh t_parser (text, (offset_val j text, (Vint (Int.repr (Zlength s - j)),
         (offset_val k text, (en, (Vint ty, Vint iq)))))) p;
       data_at sh (tarray tschar (Zlength s + 1)) (map Vbyte (s ++ [Byte.zero])) text))%assert.
- Exists k. entailer!.
- Intros j. char_addr j s text.
  forward. forward.
  fif _t'1 j s p.
  + forward. Exists true. entailer!. lt_len j s.
  + forward. forward. forward.
    Exists (Int.eq (Int.repr (Byte.signed (Znth j (s ++ [Byte.zero])))) (Int.repr 9)).
    entailer!. close_or j s.
  + Intros b. forward_if.
    * destruct b; [|discriminate]. assert (j < Zlength s) by auto.
      forward. forward. forward. forward. Exists (j+1). entailer!.
      replace (Zlength s - (j+1)) with (Zlength s - j - 1) by lia.
      change (sizeof tschar) with 1. apply derives_refl.
    * forward. Exists j. entailer!.
- Intros j. forward. forward. forward. forward.
  Exists j (offset_val k text) (offset_val (j - 1) text) (Int.repr 4) iq.
  rewrite ptr_sub1 by auto. unfold parser_at, cstring. entailer!.
  exists k, j. split3; [lia | lia | ]. split; auto.
Qed.

Lemma body_picolParseComment: semax_body Vprog Gprog f_picolParseComment picolParseComment_spec.
Proof.
start_function. unfold parser_at, cstring. Intros.
forward_loop (EX j: Z,
  PROP (k <= j <= Zlength s)
  LOCAL (temp _p p)
  SEP (data_at Tsh t_parser (text, (offset_val j text, (Vint (Int.repr (Zlength s - j)),
         (st, (en, (Vint ty, Vint iq)))))) p;
       data_at sh (tarray tschar (Zlength s + 1)) (map Vbyte (s ++ [Byte.zero])) text))%assert
 break: (EX j: Z,
  PROP (k <= j <= Zlength s)
  LOCAL (temp _p p)
  SEP (data_at Tsh t_parser (text, (offset_val j text, (Vint (Int.repr (Zlength s - j)),
         (st, (en, (Vint ty, Vint iq)))))) p;
       data_at sh (tarray tschar (Zlength s + 1)) (map Vbyte (s ++ [Byte.zero])) text))%assert.
- Exists k. entailer!.
- Intros j. char_addr j s text.
  forward.
  fif _t'1 j s p.
  + forward. forward. forward.
    Exists (negb (Int.eq (Int.repr (Byte.signed (Znth j (s ++ [Byte.zero])))) (Int.repr 10))).
    entailer!. close_or j s.
  + forward. Exists false. entailer!.
  + Intros b. forward_if.
    * destruct b; [|discriminate]. use_imp.
      forward. forward. forward. forward. Exists (j+1). entailer!.
      replace (Zlength s - (j+1)) with (Zlength s - j - 1) by lia.
      change (sizeof tschar) with 1. apply derives_refl.
    * forward. Exists j. entailer!.
- Intros j. forward. Exists j. unfold parser_at, cstring. entailer!.
Qed.

Lemma body_picolParseEol: semax_body Vprog Gprog f_picolParseEol picolParseEol_spec.
Proof.
start_function. unfold parser_at, cstring. Intros.
forward. forward.
forward_loop (EX j: Z,
  PROP (k <= j <= Zlength s)
  LOCAL (temp _p p)
  SEP (data_at Tsh t_parser (text, (offset_val j text, (Vint (Int.repr (Zlength s - j)),
         (offset_val k text, (en, (Vint ty, Vint iq)))))) p;
       data_at sh (tarray tschar (Zlength s + 1)) (map Vbyte (s ++ [Byte.zero])) text))%assert
 break: (EX j: Z,
  PROP (k <= j <= Zlength s)
  LOCAL (temp _p p)
  SEP (data_at Tsh t_parser (text, (offset_val j text, (Vint (Int.repr (Zlength s - j)),
         (offset_val k text, (en, (Vint ty, Vint iq)))))) p;
       data_at sh (tarray tschar (Zlength s + 1)) (map Vbyte (s ++ [Byte.zero])) text))%assert.
- Exists k. entailer!.
- Intros j. char_addr j s text.
  forward. forward.
  stage1 _t'1 j s p 9.
  stageN _t'2 j s p 10.
  stageN _t'3 j s p 13.
  stageN _t'4 j s p 59.
  Intros b4. forward_if.
  * destruct b4; [|discriminate]. use_imp.
    forward. forward. forward. forward. Exists (j+1). entailer!.
    replace (Zlength s - (j+1)) with (Zlength s - j - 1) by lia.
    change (sizeof tschar) with 1. apply derives_refl.
  * forward. Exists j. entailer!.
- Intros j. forward. forward. forward. forward.
  Exists j (offset_val k text) (offset_val (j - 1) text) (Int.repr 5) iq.
  rewrite ptr_sub1 by auto. unfold parser_at, cstring. entailer!.
  exists k, j. split3; [lia | lia | ]. split; auto.
Qed.
