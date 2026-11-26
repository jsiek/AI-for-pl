(* picolParseBrace, picolParseCommand *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import Picol.picol_full Picol.spec_picol Picol.picol_defs Picol.verif_libc Picol.verif_util
  Picol.verif_parse.

Definition pstate (p text: val) (s: list byte) (j: Z) (st en: val) (ty iq: int) : mpred :=
  data_at Tsh t_parser
    (text, (offset_val j text, (Vint (Int.repr (Zlength s - j)), (st, (en, (Vint ty, Vint iq)))))) p.

Ltac kill_bool := first [
    match goal with H: typed_true _ _ |- _ => solve [inv H] end
  | match goal with H: typed_false _ _ |- _ => solve [inv H] end
  | match goal with H: _ <> _ |- _ => solve [exfalso; apply H; reflexivity] end
  | match goal with H: @eq int _ _ |- _ => solve [discriminate H] end
  | match goal with H: false = true |- _ => discriminate H end
  | match goal with H: true = false |- _ => discriminate H end
  | solve [contradiction] ].

Ltac at_end j s :=
  destruct (zlt j (Zlength s)); auto; exfalso;
  assert (j = Zlength s) by lia; subst j; rewrite Z.sub_diag in *;
  match goal with H: _ <> _ |- _ => apply H; reflexivity end.

Ltac ex_bool t :=
  match goal with
  | |- context [temp t (bool2val ?b)] => Exists b
  | |- context [temp t (Val.of_bool ?b)] => Exists b
  | |- context [temp t (Vint (Int.repr 0))] => Exists false
  | |- context [temp t (Vint Int.zero)] => Exists false
  end; entailer!.

Ltac pa_eq :=
  change (sizeof tschar) with 1;
  match goal with |- context [Int.repr (Zlength ?s - ?j - 1)] =>
    replace (Zlength s - j - 1) with (Zlength s - (j + 1)) by lia end;
  apply derives_refl.

Lemma body_picolParseBrace: semax_body Vprog Gprog f_picolParseBrace picolParseBrace_spec.
Proof.
start_function. unfold parser_at, cstring. Intros.
assert_PROP (isptr text) by entailer!.
forward. forward. forward. forward. forward. forward. forward.
forward_loop (EX j: Z, EX lvl: Z,
  PROP (k + 1 <= j <= Zlength s; 1 <= lvl <= j)
  LOCAL (temp _level (Vint (Int.repr lvl)); temp _p p)
  SEP (data_at Tsh t_parser (text, (offset_val j text, (Vint (Int.repr (Zlength s - j)),
         (offset_val (k + 1) text, (en, (Vint ty, Vint iq)))))) p;
       data_at sh (tarray tschar (Zlength s + 1)) (map Vbyte (s ++ [Byte.zero])) text))%assert
 break: (PROP (False) LOCAL () SEP ()).
{ Exists (k + 1) 1. entailer!.
  change (sizeof tschar) with 1. replace (Zlength s - k - 1) with (Zlength s - (k + 1)) by lia.
  apply derives_refl. }
Intros j lvl.
forward.
forward_if (EX b: bool,
  PROP (b = true -> j + 2 <= Zlength s)
  LOCAL (temp _t'4 (bool2val b); temp _level (Vint (Int.repr lvl)); temp _p p)
  SEP (data_at Tsh t_parser (text, (offset_val j text, (Vint (Int.repr (Zlength s - j)),
         (offset_val (k + 1) text, (en, (Vint ty, Vint iq)))))) p;
       data_at sh (tarray tschar (Zlength s + 1)) (map Vbyte (s ++ [Byte.zero])) text))%assert.
{ char_addr j s text.
  forward. forward. forward.
  Exists (Int.eq (Int.repr (Byte.signed (Znth j (s ++ [Byte.zero])))) (Int.repr 92)).
  entailer!. }
{ forward. Exists false. entailer!. }
Intros b.
(* the state just before the final p->p++, p->len-- *)
forward_if (EX j1: Z, EX lvl1: Z,
  PROP (k + 1 <= j1 < Zlength s; 1 <= lvl1 <= j1 + 1)
  LOCAL (temp _level (Vint (Int.repr lvl1)); temp _p p)
  SEP (data_at Tsh t_parser (text, (offset_val j1 text, (Vint (Int.repr (Zlength s - j1)),
         (offset_val (k + 1) text, (en, (Vint ty, Vint iq)))))) p;
       data_at sh (tarray tschar (Zlength s + 1)) (map Vbyte (s ++ [Byte.zero])) text))%assert.
{ destruct b; [|kill_bool].
  assert (j + 2 <= Zlength s) by auto.
  forward. forward. forward. forward.
  Exists (j + 1) lvl. entailer!.
  change (sizeof tschar) with 1. replace (Zlength s - j - 1) with (Zlength s - (j + 1)) by lia.
  apply derives_refl. }
{ forward.
  forward_if (EX b2: bool,
    PROP (b2 = false -> j < Zlength s)
    LOCAL (temp _t'3 (bool2val b2); temp _level (Vint (Int.repr lvl)); temp _p p)
    SEP (data_at Tsh t_parser (text, (offset_val j text, (Vint (Int.repr (Zlength s - j)),
           (offset_val (k + 1) text, (en, (Vint ty, Vint iq)))))) p;
         data_at sh (tarray tschar (Zlength s + 1)) (map Vbyte (s ++ [Byte.zero])) text))%assert.
  { forward. Exists true. entailer!. }
  { char_addr j s text.
    forward. forward. forward.
    Exists (Int.eq (Int.repr (Byte.signed (Znth j (s ++ [Byte.zero])))) (Int.repr 125)).
    entailer!.
    all: intros; at_end j s. }
  Intros b2.
  forward_if.
  { destruct b2; [|kill_bool].
    forward.
    forward_if (EX b3: bool,
      PROP (b3 = false -> lvl - 1 <> 0 /\ j < Zlength s)
      LOCAL (temp _t'2 (bool2val b3); temp _level (Vint (Int.repr (lvl - 1))); temp _p p)
      SEP (data_at Tsh t_parser (text, (offset_val j text, (Vint (Int.repr (Zlength s - j)),
             (offset_val (k + 1) text, (en, (Vint ty, Vint iq)))))) p;
           data_at sh (tarray tschar (Zlength s + 1)) (map Vbyte (s ++ [Byte.zero])) text))%assert.
    { forward. Exists true. entailer!. }
    { forward. forward.
      Exists (if zeq (Zlength s - j) 0 then true else false).
      entailer!.
      repeat match goal with |- _ /\ _ => split end.
      all: try (destruct (zeq (Zlength s - j) 0); reflexivity).
      all: try (intro X; match goal with H: Int.repr (_ - 1) <> _ |- _ =>
                  apply H; rewrite X; reflexivity end).
      all: try (match goal with H: (if zeq ?a ?b then _ else _) = false |- _ =>
                  destruct (zeq a b); [discriminate|] end; lia). }
    Intros b3.
    forward_if.
    { (* the closing brace (or the end): the token ends here *)
      forward. forward. forward.
      forward_if (EX j2: Z,
        PROP (j <= j2 <= Zlength s)
        LOCAL (temp _p p)
        SEP (data_at Tsh t_parser (text, (offset_val j2 text, (Vint (Int.repr (Zlength s - j2)),
               (offset_val (k + 1) text, (offset_val (j - 1) text, (Vint ty, Vint iq)))))) p;
             data_at sh (tarray tschar (Zlength s + 1)) (map Vbyte (s ++ [Byte.zero])) text))%assert.
      { forward. forward. forward. forward.
        Exists (j + 1). rewrite ptr_sub1 by auto. entailer!.
        all: try (assert (j < Zlength s) by (at_end j s); lia).
        change (sizeof tschar) with 1. replace (Zlength s - j - 1) with (Zlength s - (j + 1)) by lia.
        apply derives_refl. }
      { forward. Exists j. rewrite ptr_sub1 by auto. entailer!. }
      Intros j2.
      forward. forward.
      Exists j2 (offset_val (k + 1) text) (offset_val (j - 1) text) (Int.repr 1) iq.
      unfold parser_at, cstring. entailer!.
      exists (k + 1), j. split3; [lia | lia | ]. split; auto. }
    { forward. destruct b3; [kill_bool|].
      match goal with H: false = false -> _ |- _ => destruct (H eq_refl) end.
      Exists j (lvl - 1). entailer!. } }
  { destruct b2; [kill_bool|].
    match goal with H: false = false -> _ |- _ => specialize (H eq_refl) end.
    char_addr j s text.
    forward. forward.
    forward_if.
    { forward. Exists j (lvl + 1). entailer!. }
    { forward. Exists j lvl. entailer!. } } }
Intros j1 lvl1.
forward. forward. forward. forward.
Exists (j1 + 1) lvl1. entailer!.
change (sizeof tschar) with 1. replace (Zlength s - j1 - 1) with (Zlength s - (j1 + 1)) by lia.
apply derives_refl.
Qed.

Definition cmd_mid (p text: val) (sh: share) (s: list byte) (k: Z) (en: val) (ty iq: int) (j: Z)
    : environ -> mpred :=
  (EX j1: Z, EX lvl1: Z, EX blv1: Z,
   PROP (k + 1 <= j1 < Zlength s; 1 <= lvl1 <= j1 + 1; 0 <= blv1 <= j1 + 1; j <= j1)
   LOCAL (temp _level (Vint (Int.repr lvl1)); temp _blevel (Vint (Int.repr blv1)); temp _p p)
   SEP (data_at Tsh t_parser (text, (offset_val j1 text, (Vint (Int.repr (Zlength s - j1)),
          (offset_val (k + 1) text, (en, (Vint ty, Vint iq)))))) p;
        data_at sh (tarray tschar (Zlength s + 1)) (map Vbyte (s ++ [Byte.zero])) text))%assert.

Ltac mid j l b := unfold cmd_mid; Exists j l b; entailer!.

Lemma body_picolParseCommand: semax_body Vprog Gprog f_picolParseCommand picolParseCommand_spec.
Proof.
start_function. unfold parser_at, cstring. Intros.
assert_PROP (isptr text) by entailer!.
forward. forward. forward. forward. forward. forward. forward. forward.
forward_loop (EX j: Z, EX lvl: Z, EX blv: Z,
  PROP (k + 1 <= j <= Zlength s; 1 <= lvl <= j; 0 <= blv <= j)
  LOCAL (temp _level (Vint (Int.repr lvl)); temp _blevel (Vint (Int.repr blv)); temp _p p)
  SEP (data_at Tsh t_parser (text, (offset_val j text, (Vint (Int.repr (Zlength s - j)),
         (offset_val (k + 1) text, (en, (Vint ty, Vint iq)))))) p;
       data_at sh (tarray tschar (Zlength s + 1)) (map Vbyte (s ++ [Byte.zero])) text))%assert
 break: (EX j: Z,
  PROP (k + 1 <= j <= Zlength s)
  LOCAL (temp _p p)
  SEP (data_at Tsh t_parser (text, (offset_val j text, (Vint (Int.repr (Zlength s - j)),
         (offset_val (k + 1) text, (en, (Vint ty, Vint iq)))))) p;
       data_at sh (tarray tschar (Zlength s + 1)) (map Vbyte (s ++ [Byte.zero])) text))%assert.
{ Exists (k + 1) 1 0. entailer!. pa_eq. }
{ Intros j lvl blv.
  forward.
  forward_if.
  { forward. Exists j. entailer!. }
  assert (Hj: j < Zlength s).
  { destruct (zlt j (Zlength s)); auto. assert (j = Zlength s) by lia. subst j.
    rewrite Z.sub_diag in *. exfalso. auto. }
  char_addr j s text.
  forward. forward.
  forward_if (EX b: bool, PROP ()
    LOCAL (temp _t'4 (bool2val b); temp _level (Vint (Int.repr lvl));
           temp _blevel (Vint (Int.repr blv)); temp _p p)
    SEP (data_at Tsh t_parser (text, (offset_val j text, (Vint (Int.repr (Zlength s - j)),
           (offset_val (k + 1) text, (en, (Vint ty, Vint iq)))))) p;
         data_at sh (tarray tschar (Zlength s + 1)) (map Vbyte (s ++ [Byte.zero])) text))%assert.
  { forward. ex_bool _t'4. }
  { forward. Exists false. entailer!. }
  Intros b.
  forward_if (cmd_mid p text sh s k en ty iq j).
  { forward. mid j (lvl + 1) blv. }
  { forward. forward.
    forward_if (EX b: bool, PROP ()
      LOCAL (temp _t'3 (bool2val b); temp _level (Vint (Int.repr lvl));
             temp _blevel (Vint (Int.repr blv)); temp _p p)
      SEP (data_at Tsh t_parser (text, (offset_val j text, (Vint (Int.repr (Zlength s - j)),
             (offset_val (k + 1) text, (en, (Vint ty, Vint iq)))))) p;
           data_at sh (tarray tschar (Zlength s + 1)) (map Vbyte (s ++ [Byte.zero])) text))%assert.
    { forward. ex_bool _t'3. }
    { forward. Exists false. entailer!. }
    Intros b'.
    forward_if (cmd_mid p text sh s k en ty iq j).
    { forward. forward.
      forward_if.
      { forward. Exists j. entailer!. }
      { forward. mid j (lvl - 1) blv.
        match goal with H: Int.repr (lvl - 1) <> _ |- _ =>
          assert (lvl - 1 <> 0) by (intro X; apply H; rewrite X; reflexivity) end. lia. } }
    { forward. forward.
      forward_if (cmd_mid p text sh s k en ty iq j).
      { forward.
        forward_if (cmd_mid p text sh s k en ty iq j).
        { forward. forward. forward. forward. mid (j + 1) lvl blv. pa_eq. }
        { forward. mid j lvl blv. } }
      { forward. forward.
        forward_if (cmd_mid p text sh s k en ty iq j).
        { forward. mid j lvl (blv + 1). }
        { forward. forward.
          forward_if (cmd_mid p text sh s k en ty iq j).
          { forward_if (cmd_mid p text sh s k en ty iq j).
            { forward. mid j lvl (blv - 1). }
            { forward. mid j lvl blv. } }
          { forward. mid j lvl blv. } } } } }
  unfold cmd_mid. Intros j1 lvl1 blv1.
  forward. forward. forward. forward.
  Exists (j1 + 1) lvl1 blv1. entailer!. pa_eq. }
Intros j.
forward. forward. forward.
char_addr j s text.
forward. forward.
forward_if (EX j2: Z,
  PROP (j <= j2 <= Zlength s)
  LOCAL (temp _p p)
  SEP (data_at Tsh t_parser (text, (offset_val j2 text, (Vint (Int.repr (Zlength s - j2)),
         (offset_val (k + 1) text, (offset_val (j - 1) text, (Vint (Int.repr 2), Vint iq)))))) p;
       data_at sh (tarray tschar (Zlength s + 1)) (map Vbyte (s ++ [Byte.zero])) text))%assert.
{ assert (j < Zlength s) by (lt_len j s).
  forward. forward. forward. forward.
  Exists (j + 1). rewrite ptr_sub1 by auto. entailer!. pa_eq. }
{ forward. Exists j. rewrite ptr_sub1 by auto. entailer!. }
Intros j2.
forward.
Exists j2 (offset_val (k + 1) text) (offset_val (j - 1) text) (Int.repr 2) iq.
unfold parser_at, cstring. entailer!.
exists (k + 1), j. split3; [lia | lia | ]. split; auto.
Qed.
