(* picolGetToken *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import Picol.picol_full Picol.spec_picol Picol.picol_defs Picol.verif_libc Picol.verif_util
  Picol.verif_parse.

Ltac ret_tok :=
  let k2 := fresh "k2" in let st2 := fresh "st2" in let en2 := fresh "en2" in
  let ty2 := fresh "ty2" in let iq2 := fresh "iq2" in let vret := fresh "vret" in
  Intros vret; destruct vret as [[[[k2 st2] en2] ty2] iq2]; simpl fst in *; simpl snd in *;
  forward;
  Exists k2 st2 en2 ty2 iq2; entailer!; unfold pinv; intuition.

Ltac post_ty p text s st en iq sh T :=
  forward_if (PROP () LOCAL (temp _p p)
    SEP (data_at Tsh t_parser (text, (offset_val (Zlength s) text,
           (Vint (Int.repr (Zlength s - Zlength s)), (st, (en, (Vint T, Vint iq)))))) p;
         cstring sh s text)).

Lemma cfold: forall sh s p, ~ In Byte.zero s ->
  data_at sh (tarray tschar (Zlength s + 1)) (map Vbyte (s ++ [Byte.zero])) p |-- cstring sh s p.
Proof. intros. unfold cstring. entailer!. Qed.

Lemma pa_fold: forall p t s k a b c d,
  data_at Tsh t_parser (t, (offset_val k t, (Vint (Int.repr (Zlength s - k)), (a, (b, (Vint c, Vint d)))))) p
  |-- parser_at p t s k a b c d.
Proof. intros. unfold parser_at. apply derives_refl. Qed.

Ltac fold_pa :=
  match goal with |- context [parser_at] => idtac | _ =>
  match goal with |- context [data_at Tsh t_parser (?t, (offset_val ?k ?t, (Vint (Int.repr (Zlength ?s - ?k)), (?a, (?b, (Vint ?c, Vint ?d)))))) ?p] =>
    sep_apply (pa_fold p t s k a b c d) end end.

Ltac same_pre_if := match goal with |- semax _ ?Pre _ _ => forward_if Pre end.

Ltac pinv_tac :=
  unfold pinv in *;
  match goal with H: _ \/ ptok _ _ _ _ |- _ => destruct H as [[? [? ?]]|?] end;
  intuition.

Ltac absurd_any := first [ contradiction | discriminate
  | match goal with H: _ <> _ |- _ => solve [exfalso; apply H; reflexivity] end
  | match goal with H: typed_true _ _ |- _ => solve [inv H] end
  | match goal with H: typed_false _ _ |- _ => solve [inv H] end
  | match goal with H: @eq int _ _ |- _ => solve [discriminate H] end ].

Lemma body_picolGetToken: semax_body Vprog Gprog f_picolGetToken picolGetToken_spec.
Proof.
start_function.
forward_loop (EX k1: Z,
  PROP (0 <= k1 <= Zlength s)
  LOCAL (temp _p p)
  SEP (parser_at p text s k1 st en ty iq; cstring sh s text))%assert
 break: (PROP (False) LOCAL () SEP ()).
{ Exists k. entailer!. }
Intros k1.
unfold parser_at.
forward. forward.
match goal with |- semax _ (PROPx ?A ?B) _ _ =>
  forward_if (PROPx ((k1 < Zlength s) :: A) B) end.
{ (* end of input *)
  assert (k1 = Zlength s).
  { match goal with H: Int.repr _ = Int.zero |- _ =>
      change Int.zero with (Int.repr 0) in H;
      apply repr_inj_signed in H; [lia | rep_lia | rep_lia] end. }
  subst k1.
  forward.
  destruct (Int.eq_dec ty (Int.repr 5)) as [E5|E5].
  { subst ty.
    forward_if (temp _t'1 (Vint Int.zero)).
    { absurd_any. }
    { forward. entailer!. }
    post_ty p text s st en iq sh (Int.repr 6). { absurd_any. } { forward. entailer!. }
    forward.
    Exists (Zlength s) st en (Int.repr 6) iq. unfold parser_at. entailer!.
    pinv_tac. }
  destruct (Int.eq_dec ty (Int.repr 6)) as [E6|E6].
  { subst ty.
    forward_if (temp _t'1 (Vint Int.zero)).
    { forward. forward. entailer!. }
    { forward. entailer!. }
    post_ty p text s st en iq sh (Int.repr 6). { absurd_any. } { forward. entailer!. }
    forward.
    Exists (Zlength s) st en (Int.repr 6) iq. unfold parser_at. entailer!.
    all: pinv_tac. }
  forward_if (temp _t'1 (Vint Int.one)).
  { forward. forward. entailer!. rewrite Int.eq_false by auto. reflexivity. }
  { absurd_any. }
  post_ty p text s st en iq sh (Int.repr 5). { forward. entailer!. } { absurd_any. }
  forward.
  Exists (Zlength s) st en (Int.repr 5) iq. unfold parser_at. entailer!.
  unfold pinv in *.
  match goal with H: _ \/ ptok _ _ _ _ |- _ => destruct H as [[? [? [?|?]]]|?] end;
    try contradiction.
  split; right; auto. }
{ forward. entailer!.
  destruct (zlt k1 (Zlength s)); auto. exfalso.
  assert (k1 = Zlength s) by lia. subst k1. rewrite Z.sub_diag in *. contradiction. }
Intros.
unfold cstring. Intros.
char_addr k1 s text.
forward. forward.
sep_apply (cfold sh s text ltac:(auto)).
forward_if.
all: first [
  (* '#': a comment at the start of a command is skipped *)
  forward; same_pre_if;
    [ fold_pa; forward_call (p, text, sh, s, k1, st, en, ty, iq);
      let k2 := fresh "k2" in Intros k2; forward; Exists k2; entailer!
    | forward; entailer!
    | fold_pa; forward_call (p, text, sh, s, k1, st, en, ty, iq); ret_tok ]
| (* blanks and separators: inside quotes they belong to the string *)
  forward; same_pre_if;
    [ fold_pa; forward_call (p, text, sh, s, k1, st, en, ty, iq); ret_tok
    | forward; entailer!
    | fold_pa; forward_call (p, text, sh, s, k1, st, en, ty, iq); ret_tok ]
| fold_pa; forward_call (p, text, sh, s, k1, st, en, ty, iq); ret_tok ].
Qed.
