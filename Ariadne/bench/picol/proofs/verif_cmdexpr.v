(* picolCommandExpr *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import Picol.picol_full Picol.spec_picol Picol.picol_defs Picol.verif_util Picol.verif_parse
  Picol.verif_interp Picol.verif_cmd_common Picol.verif_retcodes Picol.verif_vars Picol.verif_cmds
  Picol.verif_control Picol.verif_strutil.

Ltac t_ := first [ reflexivity | assumption | lia | list_solve | auto ].

Definition sp1 (j: Z) : Z := if zeq j 1 then 0 else 1.

Lemma sub1_bound: forall args argc, 2 <= argc -> Zlength args = argc ->
  1 <= args_size (sublist 1 argc args).
Proof.
  intros. rewrite (sublist_split 1 2 argc) by lia. rewrite args_size_app, sublist_len_1 by lia.
  rewrite args_size_cons. pose proof (args_size_nonneg (sublist 2 argc args)).
  pose proof (Zlength_nonneg (Znth 1 args)). unfold args_size at 1; simpl. lia.
Qed.

Lemma body_picolCommandExpr: semax_body Vprog Gprog f_picolCommandExpr picolCommandExpr_spec.
Proof.
start_function.
pose proof (args_size_ge args).
forward. forward.
pre_if_with (2 <= argc).
{ sep_apply (data_at_data_at_ Tsh tint). arity_ret gv i st args ptrs. }
{ forward. entailer!. }
Intros.
assert (HL1: 1 <= args_size (sublist 1 argc args)) by (apply sub1_bound; auto).
assert (HL2: args_size (sublist 1 argc args) <= Int.max_signed - 10)
  by (pose proof (args_size_sub args 1 argc ltac:(lia) ltac:(lia)); lia).
forward_for_simple_bound argc (EX j: Z,
  PROP (1 <= j)
  LOCAL (temp _len (Vint (Int.repr (args_size (sublist 1 j args))));
         temp _i i; temp _argc (Vint (Int.repr argc)); temp _argv argv; gvars gv;
         lvar _buf (tarray tschar 64) v_buf; lvar _err tint v_err; lvar _p (tptr tschar) v_p)
  SEP (mem_mgr gv; G gv; interp_rep i st;
       data_at Ews (tarray (tptr tschar) argc) ptrs argv; args_pred args ptrs;
       data_at_ Tsh (tarray tschar 64) v_buf; data_at Tsh tint (Vint (Int.repr 0)) v_err;
       data_at_ Tsh (tptr tschar) v_p))%assert.
{ entailer!. rewrite sublist_nil. reflexivity. }
{ sep_apply (args_isptr i0 args ptrs ltac:(lia) ltac:(lia)). Intros.
  forward.
  rewrite (args_focus i0 args ptrs) by lia. Intros.
  forward_call (Ews, Znth i0 args, Znth i0 ptrs).
  sep_apply (derives_refl' _ _ (eq_sym (args_focus i0 args ptrs ltac:(lia) ltac:(lia)))).
  forward.
  entailer!.
  do 2 f_equal.
  pose proof (args_size_sub args 1 (i0 + 1) ltac:(lia) ltac:(lia)).
  rewrite (args_size_snoc args 1 i0) in * by lia.
  pose proof (args_size_nonneg (sublist 1 i0 args)). pose proof (Zlength_nonneg (Znth i0 args)).
  rewrite !Int.signed_repr by rep_lia. rewrite Int64.unsigned_repr by rep_lia. lia. }
unfold G. Intros.
forward_call (existT (fun t => list (reptype t)) tschar [], nullval, 0, args_size (sublist 1 argc args), gv).
all: try solve [rep_lia | cancel].
Intros e. simpl projT1 in *; simpl projT2 in *.
forward.
assert_PROP (field_compatible (tarray tschar (args_size (sublist 1 argc args))) [] e) by entailer!.
replace (sublist 0 (Z.min 0 (args_size (sublist 1 argc args))) [] ++
         Zrepeat (default_val tschar) (args_size (sublist 1 argc args) - Z.min 0 (args_size (sublist 1 argc args))))
  with (map Vbyte [] ++ Zrepeat Vundef (args_size (sublist 1 argc args) - Zlength (@nil byte)))
  by (rewrite Z.min_l by lia; rewrite sublist_nil; reflexivity).
forward_for_simple_bound argc (EX j: Z, EX cat: list byte,
  PROP (1 <= j; ~ In Byte.zero cat;
        (Zlength cat + sp1 j)%Z = args_size (sublist 1 j args))
  LOCAL (temp _expr e; temp _i i; temp _argc (Vint (Int.repr argc)); temp _argv argv; gvars gv;
         lvar _buf (tarray tschar 64) v_buf; lvar _err tint v_err; lvar _p (tptr tschar) v_p)
  SEP (mem_mgr gv; Gx gv; Gr gv; interp_rep i st;
       data_at Ews (tarray (tptr tschar) argc) ptrs argv; args_pred args ptrs;
       data_at_ Tsh (tarray tschar 64) v_buf; data_at Tsh tint (Vint (Int.repr 0)) v_err;
       data_at Tsh (tptr tschar) (offset_val (Zlength cat) e) v_p;
       malloc_token Ews (tarray tschar (args_size (sublist 1 argc args))) e;
       data_at Ews (tarray tschar (args_size (sublist 1 argc args)))
         (map Vbyte cat ++ Zrepeat Vundef (args_size (sublist 1 argc args) - Zlength cat)) e))%assert.
{ assert_PROP (isptr e) by entailer!.
  sep_apply (dat_off0 Tsh e v_p ltac:(auto)).
  Exists (@nil byte). entailer!. rewrite sublist_nil. reflexivity. }
{ Intros.
  match goal with H: ~ In Byte.zero cat |- _ => rename H into Hcat_nz end.
  match goal with H: (Zlength cat + sp1 i0)%Z = _ |- _ => rename H into Hcat_len end.
  assert (Hs1: args_size (sublist 1 (i0+1) args) = args_size (sublist 1 i0 args) + Zlength (Znth i0 args) + 1)
    by (apply args_size_snoc; lia).
  assert (Hs2: args_size (sublist 1 (i0+1) args) <= args_size (sublist 1 argc args))
    by (apply args_size_mono; lia).
  pose proof (Zlength_nonneg (Znth i0 args)).
  sep_apply (args_isptr i0 args ptrs ltac:(lia) ltac:(lia)). Intros.
  forward.
  rewrite (args_focus i0 args ptrs) by lia. Intros.
  forward_call (Ews, Znth i0 args, Znth i0 ptrs).
  forward.
  pose proof (args_elem args i0 ltac:(lia)).
  rewrite len_norm by rep_lia.
  forward_if (EX cat1: list byte,
    PROP (~ In Byte.zero cat1; Zlength cat1 = args_size (sublist 1 i0 args))
    LOCAL (temp _l (Vint (Int.repr (Zlength (Znth i0 args)))); temp _j (Vint (Int.repr i0));
           temp _expr e; temp _i i; temp _argc (Vint (Int.repr argc)); temp _argv argv; gvars gv;
           lvar _buf (tarray tschar 64) v_buf; lvar _err tint v_err; lvar _p (tptr tschar) v_p)
    SEP (cstring Ews (Znth i0 args) (Znth i0 ptrs);
         args_pred (sublist 0 i0 args) (sublist 0 i0 ptrs);
         args_pred (sublist (i0 + 1) (Zlength args) args) (sublist (i0 + 1) (Zlength ptrs) ptrs);
         mem_mgr gv; Gx gv; Gr gv; interp_rep i st;
         data_at Ews (tarray (tptr tschar) argc) ptrs argv;
         data_at_ Tsh (tarray tschar 64) v_buf; data_at Tsh tint (Vint (Int.repr 0)) v_err;
         data_at Tsh (tptr tschar) (offset_val (Zlength cat1) e) v_p;
         malloc_token Ews (tarray tschar (args_size (sublist 1 argc args))) e;
         data_at Ews (tarray tschar (args_size (sublist 1 argc args)))
           (map Vbyte cat1 ++ Zrepeat Vundef (args_size (sublist 1 argc args) - Zlength cat1)) e))%assert.
  { assert (sp1 i0 = 1) by (unfold sp1; rewrite if_false by lia; auto).
    forward. forward.
    pose proof (arr_field_address (args_size (sublist 1 argc args)) (Zlength cat) e
                  ltac:(pose proof (Zlength_nonneg cat); lia) H8).
    forward.
    Exists (cat ++ [Byte.repr 32]). entailer!.
    { split. apply not_in_snoc; auto. vm_compute; discriminate.
      rewrite Zlength_app, Zlength_cons, Zlength_nil. lia. }
    change (Vint (Int.repr 32)) with (Vbyte (Byte.repr 32)).
    rewrite upd_app_byte by lia.
    change (sizeof tschar) with 1. rewrite !Zlength_app, Zlength_cons, Zlength_nil.
    unfold data_at at 2. cancel. }
  { forward. Exists cat. entailer!.
    unfold sp1 in *. destruct (zeq i0 1); lia. }
  Intros cat1.
  forward. forward.
  set (a := Znth i0 args) in *.
  set (L := args_size (sublist 1 argc args)) in *.
  assert (Hc1: Zlength cat1 + Zlength a + 1 <= L) by lia.
  pose proof (Zlength_nonneg cat1). pose proof (Zlength_nonneg a).
  replace (L - Zlength cat1) with (Zlength a + (L - Zlength cat1 - Zlength a)) by lia.
  rewrite (Zrepeat_split Vundef (Zlength a) (L - Zlength cat1 - Zlength a)) by lia.
  rewrite app_assoc.
  rewrite (arr_split2 Ews L (Zlength cat1 + Zlength a) (L - Zlength cat1 - Zlength a))
    by (try lia; try list_solve; auto).
  assert_PROP (field_compatible (tarray tschar (Zlength cat1 + Zlength a)) [] e) by entailer!.
  rewrite (arr_split2 Ews (Zlength cat1 + Zlength a) (Zlength cat1) (Zlength a))
    by (try lia; try list_solve; auto).
  rewrite data_at_undef.
  unfold cstring. Intros.
  assert_PROP (field_compatible (tarray tschar (Zlength a + 1)) [] (Znth i0 ptrs)) by entailer!.
  rewrite map_app.
  rewrite (arr_split2 Ews (Zlength a + 1) (Zlength a) 1 (map Vbyte a) (map Vbyte [Byte.zero]))
    by (try lia; try list_solve; auto).
  Intros.
  forward_call (Ews, Ews, offset_val (Zlength cat1) e, Znth i0 ptrs, Zlength a, a).
  sep_apply (derives_refl' _ _ (eq_sym (arr_split2 Ews (Zlength a + 1) (Zlength a) 1
     (map Vbyte a) (map Vbyte [Byte.zero]) (Znth i0 ptrs)
     ltac:(lia) ltac:(list_solve) ltac:(list_solve) ltac:(lia) ltac:(lia) ltac:(auto)))).
  sep_apply (derives_refl' _ _ (eq_sym (arr_split2 Ews (Zlength cat1 + Zlength a) (Zlength cat1) (Zlength a)
     (map Vbyte cat1) (map Vbyte a) e
     ltac:(lia) ltac:(list_solve) ltac:(list_solve) ltac:(lia) ltac:(lia) ltac:(auto)))).
  sep_apply (derives_refl' _ _ (eq_sym (arr_split2 Ews L (Zlength cat1 + Zlength a) (L - Zlength cat1 - Zlength a)
     (map Vbyte cat1 ++ map Vbyte a) (Zrepeat Vundef (L - Zlength cat1 - Zlength a)) e
     ltac:(lia) ltac:(list_solve) ltac:(list_solve) ltac:(lia) ltac:(lia) ltac:(auto)))).
  replace (map Vbyte a ++ map Vbyte [Byte.zero]) with (map Vbyte (a ++ [Byte.zero])) by (rewrite map_app; auto).
  sep_apply (cstring_fold Ews a (Znth i0 ptrs) ltac:(auto)).
  subst a L.
  sep_apply (derives_refl' _ _ (eq_sym (args_focus i0 args ptrs ltac:(lia) ltac:(lia)))).
  forward. forward.
  Exists (cat1 ++ Znth i0 args). entailer!.
  { split. apply not_in_app; auto.
    rewrite Zlength_app. unfold sp1. destruct (zeq (i0 + 1) 1); lia. }
  rewrite map_app, Zlength_app.
  replace (args_size (sublist 1 (Zlength args) args) - Zlength cat1 - Zlength (Znth i0 args))
    with (args_size (sublist 1 (Zlength args) args) - (Zlength cat1 + Zlength (Znth i0 args))) by lia.
  cancel. }
Intros cat.
match goal with H: ~ In Byte.zero cat |- _ => rename H into Hcat_nz end.
assert (HLc: args_size (sublist 1 argc args) = Zlength cat + 1).
{ match goal with H: (Zlength cat + sp1 argc)%Z = _ |- _ => rewrite <- H end.
  unfold sp1. destruct (zeq argc 1); lia. }
rewrite HLc in *.
forward.
pose proof (arr_field_address (Zlength cat + 1) (Zlength cat) e
              ltac:(pose proof (Zlength_nonneg cat); lia) H8).
forward.
forward.
change (Vint (Int.repr 0)) with (Vbyte Byte.zero).
replace (Zlength cat + 1 - Zlength cat) with 1 by lia.
replace (upd_Znth (Zlength cat) (map Vbyte cat ++ Zrepeat Vundef 1) (Vbyte Byte.zero))
  with (map Vbyte (cat ++ [Byte.zero])) by list_solve.
sep_apply (cstring_fold Ews cat e Hcat_nz).
rewrite Gr_GL. Intros.
take_lit gv lits 6 ___stringlit_8 v___stringlit_8.
change (cstring Ers (litb v___stringlit_8) (gv ___stringlit_8)) with (lit gv ___stringlit_8 v___stringlit_8).
assert_PROP (isptr e) by entailer!.
sep_apply (dat_off0 Tsh e v_p ltac:(auto)).
unfold interp_rep. Intros.
forward_call (gv, i, i_level st,
  (hdp f_ptr (i_frames st) nullval, (hdp c_ptr (i_cmds st) nullval, i_resultp st)),
  v_p, v_err, Int.repr 0, Ews, cat, e, 0, 0).
Intros vret. destruct vret as [[k' e'] d]. simpl fst in *; simpl snd in *.
change (lit gv ___stringlit_8 v___stringlit_8) with (cstring Ers (litb v___stringlit_8) (gv ___stringlit_8)).
give_lit gv lits 6 ___stringlit_8 v___stringlit_8.
sep_apply (interp_refold i st ltac:(auto) ltac:(auto)).
unfold cstring. Intros.
forward_loop (EX k: Z,
  PROP (k' <= k <= Zlength cat)
  LOCAL (temp _v (Vfloat d); temp _expr e; temp _i i; gvars gv;
         lvar _buf (tarray tschar 64) v_buf; lvar _err tint v_err; lvar _p (tptr tschar) v_p)
  SEP (mem_mgr gv; Gx gv; GL gv lits; Gs gv; interp_rep i st;
       data_at Ews (tarray (tptr tschar) argc) ptrs argv; args_pred args ptrs;
       data_at_ Tsh (tarray tschar 64) v_buf; data_at Tsh tint (Vint e') v_err;
       data_at Tsh (tptr tschar) (offset_val k e) v_p;
       malloc_token Ews (tarray tschar (Zlength cat + 1)) e;
       data_at Ews (tarray tschar (Zlength cat + 1)) (map Vbyte (cat ++ [Byte.zero])) e))%assert
 break: (EX k: Z,
  PROP (k' <= k <= Zlength cat)
  LOCAL (temp _v (Vfloat d); temp _expr e; temp _i i; gvars gv;
         lvar _buf (tarray tschar 64) v_buf; lvar _err tint v_err; lvar _p (tptr tschar) v_p)
  SEP (mem_mgr gv; Gx gv; GL gv lits; Gs gv; interp_rep i st;
       data_at Ews (tarray (tptr tschar) argc) ptrs argv; args_pred args ptrs;
       data_at_ Tsh (tarray tschar 64) v_buf; data_at Tsh tint (Vint e') v_err;
       data_at Tsh (tptr tschar) (offset_val k e) v_p;
       malloc_token Ews (tarray tschar (Zlength cat + 1)) e;
       data_at Ews (tarray tschar (Zlength cat + 1)) (map Vbyte (cat ++ [Byte.zero])) e))%assert.
{ Exists k'. entailer!. }
{ Intros k. forward. char_addr k cat e. forward.
  forward_if.
  { assert (k < Zlength cat).
    { destruct (zlt k (Zlength cat)); auto. assert (k = Zlength cat) by lia. subst k.
      match goal with H: context [Znth (Zlength cat) (cat ++ [Byte.zero])] |- _ =>
        rewrite tail_char in H; change (Byte.signed Byte.zero) with 0 in H;
        try (vm_compute in H); first [lia | discriminate] end. }
    forward. forward. Exists (k + 1). entailer!.
    change (sizeof tschar) with 1. apply derives_refl. }
  { forward. Exists k. entailer!. } }
Intros k. forward. char_addr k cat e. forward.
forward_if (EX e2: int,
  PROP ()
  LOCAL (temp _v (Vfloat d); temp _expr e; temp _i i; gvars gv;
         lvar _buf (tarray tschar 64) v_buf; lvar _err tint v_err; lvar _p (tptr tschar) v_p)
  SEP (mem_mgr gv; Gx gv; GL gv lits; Gs gv; interp_rep i st;
       data_at Ews (tarray (tptr tschar) argc) ptrs argv; args_pred args ptrs;
       data_at_ Tsh (tarray tschar 64) v_buf; data_at Tsh tint (Vint e2) v_err;
       data_at Tsh (tptr tschar) (offset_val k e) v_p;
       malloc_token Ews (tarray tschar (Zlength cat + 1)) e;
       data_at Ews (tarray tschar (Zlength cat + 1)) (map Vbyte (cat ++ [Byte.zero])) e))%assert.
{ forward. Exists (Int.repr 1). entailer!. }
{ forward. Exists e'. entailer!. }
Intros e2.
forward_call (tarray tschar (Zlength cat + 1), e, gv).
{ rewrite if_false by (intro; subst; contradiction). cancel. }
forward.
forward_if.
{ take_lit gv lits 9 ___stringlit_11 v___stringlit_11.
  unfold interp_rep. Intros.
  forward_call (gv, i, Vint (Int.repr (i_level st)), hdp f_ptr (i_frames st) nullval,
                hdp c_ptr (i_cmds st) nullval, i_result st, i_resultp st,
                Ers, litb v___stringlit_11, gv ___stringlit_11).
  Intros q.
  give_lit gv lits 9 ___stringlit_11 v___stringlit_11.
  sep_apply (data_at_data_at_ Tsh tint). sep_apply (data_at_data_at_ Tsh (tptr tschar)).
  forward.
  Exists (set_res st (litb v___stringlit_11) q) (Int.repr 1).
  unfold interp_rep, set_res, G. rewrite Gr_GL.
  cbn [i_level i_frames i_cmds i_result i_resultp]. entailer!. }
rewrite buf_split_tsh. Intros.
forward_call (v_buf, 64, d).
Intros s0.
assert_PROP (Zlength s0 + 1 <= 64) by entailer!.
unfold cstringn. Intros.
rewrite (strbuf_split Ews s0 64 (Zrepeat Vundef (64 - (Zlength s0 + 1))) v_buf) by (auto; list_solve).
Intros.
unfold interp_rep. Intros.
forward_call (gv, i, Vint (Int.repr (i_level st)), hdp f_ptr (i_frames st) nullval,
              hdp c_ptr (i_cmds st) nullval, i_result st, i_resultp st, Ews, s0, v_buf).
Intros q.
sep_apply (derives_refl' _ _ (eq_sym (strbuf_split Ews s0 64 (Zrepeat Vundef (64 - (Zlength s0 + 1))) v_buf
   ltac:(auto) ltac:(lia) ltac:(list_solve)))).
sep_apply (data_at_data_at_ Ews (tarray tschar 64)).
sep_apply (derives_refl' _ _ (eq_sym (buf_split_tsh (tarray tschar 64) v_buf))).
sep_apply (data_at_data_at_ Tsh tint). sep_apply (data_at_data_at_ Tsh (tptr tschar)).
forward.
Exists (set_res st s0 q) (Int.repr 0).
unfold interp_rep, set_res, G. rewrite Gr_GL.
cbn [i_level i_frames i_cmds i_result i_resultp]. entailer!.
Qed.
