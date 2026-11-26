(* picolParseString *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import Picol.picol_full Picol.spec_picol Picol.picol_defs Picol.verif_libc Picol.verif_util
  Picol.verif_parse Picol.verif_parse2.

Definition ps_post (p text: val) (sh: share) (s: list byte) (k0: Z) (en: val) (ty iq1: int)
    : environ -> mpred :=
  (EX j1: Z,
   PROP (k0 <= j1 < Zlength s)
   LOCAL (temp _p p)
   SEP (data_at Tsh t_parser (text, (offset_val j1 text, (Vint (Int.repr (Zlength s - j1)),
          (offset_val k0 text, (en, (Vint ty, Vint iq1)))))) p;
        data_at sh (tarray tschar (Zlength s + 1)) (map Vbyte (s ++ [Byte.zero])) text))%assert.

Ltac ret0 j k0 text :=
  forward; forward; forward; forward;
  match goal with |- context [data_at Tsh t_parser (_, (_, (_, (_, (_, (_, Vint ?q)))))) _] =>
    Exists j (offset_val k0 text) (offset_val (j - 1) text) (Int.repr 0) q end;
  rewrite ptr_sub1 by auto; unfold parser_at, cstring; entailer!;
  exists k0, j; split3; [lia | lia | ]; split; auto.

Lemma body_picolParseString: semax_body Vprog Gprog f_picolParseString picolParseString_spec.
Proof.
start_function. unfold parser_at, cstring. Intros.
assert_PROP (isptr text) by entailer!.
forward.
forward_if (EX b: bool, PROP () LOCAL (temp _t'1 (bool2val b); temp _p p)
  SEP (data_at Tsh t_parser
    (text, (offset_val k text, (Vint (Int.repr (Zlength s - k)), (st, (en, (Vint ty, Vint iq)))))) p;
       data_at sh (tarray tschar (Zlength s + 1)) (map Vbyte (s ++ [Byte.zero])) text))%assert.
{ forward. Exists true. entailer!. }
{ forward. forward. Exists (Int.eq ty (Int.repr 5)). entailer!. }
Intros b1.
forward_if (EX b: bool, PROP () LOCAL (temp _t'2 (bool2val b); temp _p p)
  SEP (data_at Tsh t_parser
    (text, (offset_val k text, (Vint (Int.repr (Zlength s - k)), (st, (en, (Vint ty, Vint iq)))))) p;
       data_at sh (tarray tschar (Zlength s + 1)) (map Vbyte (s ++ [Byte.zero])) text))%assert.
{ forward. Exists true. entailer!. }
{ forward. forward. Exists (Int.eq ty (Int.repr 1)). entailer!. }
Intros b2.
forward.
forward_if (EX b: bool, PROP (b = true -> k < Zlength s)
  LOCAL (temp _t'5 (Val.of_bool b); temp _newword (bool2val b2); temp _p p)
  SEP (data_at Tsh t_parser
    (text, (offset_val k text, (Vint (Int.repr (Zlength s - k)), (st, (en, (Vint ty, Vint iq)))))) p;
       data_at sh (tarray tschar (Zlength s + 1)) (map Vbyte (s ++ [Byte.zero])) text))%assert.
{ char_addr k s text. forward. forward. forward.
  Exists (Int.eq (Int.repr (Byte.signed (Znth k (s ++ [Byte.zero])))) (Int.repr 123)).
  entailer!. close_or k s. }
{ forward. Exists false. entailer!. }
Intros b5.
forward_if.
{ destruct b5; [|kill_bool]. use_imp.
  forward_call (p, text, sh, s, k, st, en, ty, iq).
  { unfold parser_at, cstring. entailer!. }
  Intros vret. destruct vret as [[[[k' st'] en'] ty'] iq']. simpl fst in *; simpl snd in *.
  forward. Exists k' st' en' ty' iq'. entailer!. }
destruct b5; [kill_bool|].
forward_if (EX b: bool, PROP (b = true -> k < Zlength s)
  LOCAL (temp _t'4 (Val.of_bool b); temp _newword (bool2val b2); temp _p p)
  SEP (data_at Tsh t_parser
    (text, (offset_val k text, (Vint (Int.repr (Zlength s - k)), (st, (en, (Vint ty, Vint iq)))))) p;
       data_at sh (tarray tschar (Zlength s + 1)) (map Vbyte (s ++ [Byte.zero])) text))%assert.
{ char_addr k s text. forward. forward. forward.
  Exists (Int.eq (Int.repr (Byte.signed (Znth k (s ++ [Byte.zero])))) (Int.repr 34)).
  entailer!. close_or k s. }
{ forward. Exists false. entailer!. }
Intros b4.
forward_if (EX iq1: int, EX k0: Z,
  PROP (k <= k0 <= Zlength s)
  LOCAL (temp _p p)
  SEP (data_at Tsh t_parser
    (text, (offset_val k0 text, (Vint (Int.repr (Zlength s - k0)), (st, (en, (Vint ty, Vint iq1)))))) p;
       data_at sh (tarray tschar (Zlength s + 1)) (map Vbyte (s ++ [Byte.zero])) text))%assert.
{ destruct b4; [|kill_bool]. use_imp.
  forward. forward. forward. forward. forward.
  Exists (Int.repr 1) (k + 1). entailer!. pa_eq. }
{ forward. Exists iq k. entailer!. }
Intros iq1 k0.
forward. forward.
forward_loop (EX j: Z,
  PROP (k0 <= j <= Zlength s)
  LOCAL (temp _p p)
  SEP (data_at Tsh t_parser (text, (offset_val j text, (Vint (Int.repr (Zlength s - j)),
         (offset_val k0 text, (en, (Vint ty, Vint iq1)))))) p;
       data_at sh (tarray tschar (Zlength s + 1)) (map Vbyte (s ++ [Byte.zero])) text))%assert
 break: (PROP (False) LOCAL () SEP ()).
{ Exists k0. entailer!. }
Intros j.
forward.
forward_if.
{ forward. forward. forward. forward.
  Exists j (offset_val k0 text) (offset_val (j - 1) text) (Int.repr 0) iq1.
  rewrite ptr_sub1 by auto. unfold parser_at, cstring. entailer!.
  exists k0, j. split3; [lia | lia | ]. split; auto. }
assert (Hj: j < Zlength s).
{ destruct (zlt j (Zlength s)); auto. assert (j = Zlength s) by lia. subst j.
  rewrite Z.sub_diag in *. exfalso. auto. }
char_addr j s text.
forward. forward.
forward_if (EX j1: Z,
  PROP (k0 <= j1 < Zlength s)
  LOCAL (temp _p p)
  SEP (data_at Tsh t_parser (text, (offset_val j1 text, (Vint (Int.repr (Zlength s - j1)),
         (offset_val k0 text, (en, (Vint ty, Vint iq1)))))) p;
       data_at sh (tarray tschar (Zlength s + 1)) (map Vbyte (s ++ [Byte.zero])) text))%assert.
(* '\\' *)
{ forward.
  forward_if (ps_post p text sh s k0 en ty iq1).
  { forward. forward. forward. forward. unfold ps_post. Exists (j + 1). entailer!. pa_eq. }
  { forward. unfold ps_post. Exists j. entailer!. }
  unfold ps_post. Intros j1. forward. Exists j1. entailer!. }
(* '$' and '[' *)
{ ret0 j k0 text. }
{ ret0 j k0 text. }
(* blanks and ';' *)
1-5: (forward;
  forward_if (ps_post p text sh s k0 en ty iq1);
  [ ret0 j k0 text
  | forward; unfold ps_post; Exists j; entailer!
  | unfold ps_post; Intros j1; forward; Exists j1; entailer! ]).
(* double quote *)
{ forward.
  forward_if (ps_post p text sh s k0 en ty iq1).
  { forward. forward. forward. forward. forward. forward. forward. forward. forward.
    Exists (j + 1) (offset_val k0 text) (offset_val (j - 1) text) (Int.repr 0) (Int.repr 0).
    rewrite ptr_sub1 by auto. unfold parser_at, cstring. entailer!.
    { exists k0, j. split3; [lia | lia | ]. split; auto. }
    pa_eq. }
  { forward. unfold ps_post. Exists j. entailer!. }
  unfold ps_post. Intros j1. forward. Exists j1. entailer!. }
(* default *)
{ forward. Exists j. entailer!. }
Intros j1.
forward. forward. forward. forward.
Exists (j1 + 1). entailer!. pa_eq.
Qed.
