(* picolEval *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import Picol.picol_full Picol.spec_picol Picol.picol_defs Picol.verif_libc Picol.verif_util
  Picol.verif_parse Picol.verif_parse3 Picol.verif_interp Picol.verif_cmd_common Picol.verif_retcodes
  Picol.verif_vars Picol.verif_cmds Picol.verif_control Picol.verif_strutil Picol.verif_evalutil
  Picol.verif_evalutil2.

Ltac show_goal := match goal with |- ?g => idtac g end.


Definition ev_inv (gv: globals) (i: val) (st: istate) (sh: share) (s: list byte) (t v_p v_errbuf: val)
    : environ -> mpred :=
 (EX st1: istate, EX k: Z, EX stp: val, EX en: val, EX ty: int, EX iq: int,
  EX argv: val, EX L: list tok, EX argsize: Z, EX rc: int,
  PROP (cmds_ok gv (i_cmds st1); (i_level st1 = i_level st + 1)%Z;
        Zlength (i_frames st1) = Zlength (i_frames st);
        (0 <= k <= Zlength s)%Z; pinv s t stp en ty;
        (args_size (map tk_s L) <= argsize <= Int.max_signed - 10)%Z;
        (L = [] <-> argv = nullval);
        ty = Int.repr 4 \/ ty = Int.repr 5 \/ L <> [])
  LOCAL (temp _argc (Vint (Int.repr (Zlength L))); temp _argv argv;
         temp _argsize (Vlong (Int64.repr argsize)); temp _retcode (Vint rc);
         temp _i i; temp _t t; gvars gv;
         lvar _p t_parser v_p; lvar _errbuf (tarray tschar 1024) v_errbuf)
  SEP (mem_mgr gv; G gv; interp_rep i st1; cstring sh s t;
       parser_at v_p t s k stp en ty iq; data_at_ Tsh (tarray tschar 1024) v_errbuf;
       argv_rep argv L; tbufs L))%assert.

Definition ev_brk (gv: globals) (i: val) (st: istate) (sh: share) (s: list byte) (t v_p v_errbuf: val)
    : environ -> mpred :=
 (EX st1: istate, EX argv: val, EX L: list tok, EX rc: int,
  PROP (cmds_ok gv (i_cmds st1); (i_level st1 = i_level st + 1)%Z;
        Zlength (i_frames st1) = Zlength (i_frames st);
        (L = [] <-> argv = nullval); args_size (map tk_s L) <= Int.max_signed - 10)
  LOCAL (temp _argc (Vint (Int.repr (Zlength L))); temp _argv argv; temp _retcode (Vint rc);
         temp _i i; temp _t t; gvars gv;
         lvar _p t_parser v_p; lvar _errbuf (tarray tschar 1024) v_errbuf)
  SEP (mem_mgr gv; G gv; interp_rep i st1; cstring sh s t;
       data_at_ Tsh t_parser v_p; data_at_ Tsh (tarray tschar 1024) v_errbuf;
       argv_rep argv L; tbufs L))%assert.

(* the unescape loop of picolEval: src at j, dst at d in the buffer q *)
Definition esc_base (gv: globals) (i: val) (st1: istate) (sh: share) (s: list byte) (t v_p v_errbuf: val)
    (pa: mpred) (ty: int) (argv: val) (L: list tok) (argsize: Z) (rc: int) (w: list byte) (q: val)
    (j d: Z) (out: list byte) : environ -> mpred :=
 (PROP (0 <= d <= j; j <= Zlength w; Zlength out = d; ~ In Byte.zero out)
  LOCAL (temp _src (offset_val j q); temp _dst (offset_val d q);
         temp _t__1 q; temp _prevtype (Vint ty);
         temp _argc (Vint (Int.repr (Zlength L))); temp _argv argv;
         temp _argsize (Vlong (Int64.repr argsize)); temp _retcode (Vint rc);
         temp _i i; temp _t t; gvars gv;
         lvar _p t_parser v_p; lvar _errbuf (tarray tschar 1024) v_errbuf)
  SEP (mem_mgr gv; G gv; interp_rep i st1; cstring sh s t; pa;
       data_at_ Tsh (tarray tschar 1024) v_errbuf; argv_rep argv L; tbufs L;
       malloc_token Ews (tarray tschar (Zlength w + 1)) q;
       data_at Ews (tarray tschar (Zlength w + 1))
         (map Vbyte (out ++ sublist d (Zlength w + 1) (w ++ [Byte.zero]))) q))%assert.

(* put the (common) funspec of the built-in commands for the function pointer f in SEP *)
Ltac call_builtin Hbi :=
  match goal with |- semax ?D (PROPx ?P (LOCALx ?Q (SEPx ?R))) ?c ?Post =>
   match type of Hbi with In ?f _ =>
    let HFP := fresh "HFP" in
    assert (HFP: semax D (PROPx P (LOCALx Q (SEPx (func_ptr' (snd picolCommandSet_spec) f :: R)))) c Post ->
                 semax D (PROPx P (LOCALx Q (SEPx R))) c Post);
    [ let HS := fresh "HS" in intro HS; unfold builtin_addrs in Hbi; simpl in Hbi;
      let E := fresh "E" in
      destruct Hbi as [E|[E|[E|[E|[E|[E|[E|[E|[]]]]]]]]];
      [ make_func_ptr _picolCommandExpr | make_func_ptr _picolCommandSet
      | make_func_ptr _picolCommandPuts | make_func_ptr _picolCommandIf
      | make_func_ptr _picolCommandWhile | make_func_ptr _picolCommandRetCodes
      | make_func_ptr _picolCommandProc | make_func_ptr _picolCommandReturn ];
      rewrite E; exact HS
    | apply HFP; clear HFP ]
  end end.

Ltac use_bb :=
  match goal with
  | H: typed_true _ (Val.of_bool ?b) |- _ => destruct b; [| inv H]
  | H: typed_true _ (if ?b then _ else _) |- _ => destruct b; [| inv H] end.

Ltac drop_tbufs R :=
  lazymatch R with
  | tbufs _ :: ?R' => R'
  | ?x :: ?R' => let r := drop_tbufs R' in constr:(x :: r)
  end.

Lemma args_size_len: forall (L: list tok), Zlength L <= args_size (map tk_s L).
Proof. intros. pose proof (args_size_ge (map tk_s L)). rewrite Zlength_map in H. auto. Qed.

Ltac cmd_tail st2 argv L :=
  let vret := fresh "vret" in Intros vret;
  let st3 := fresh "st3" in let r3 := fresh "r3" in
  destruct vret as [st3 r3]; simpl fst in *; simpl snd in *;
  forward;
  sep_apply (derives_refl' _ _ (eq_sym (tbufs_split L)));
  sep_apply (derives_refl' _ _ (eq_sym (argv_rep_nn argv L ltac:(assumption))));
  forward_if;
  [ forward; unfold ev_brk; Exists st3 argv L r3;
    sep_apply (data_at_data_at_ Tsh t_parser); entailer!; apply func_ptr'_emp
  | forward; Exists st3 r3; entailer!; apply func_ptr'_emp ].

Ltac free_body L argv gv j :=
    pose proof (args_size_len L);
    let HnL := fresh "HnL" in let Hav := fresh "Hav" in
    assert (HnL: L <> []) by (intro; subst L; list_solve);
    assert (Hav: argv <> nullval) by (let E := fresh in intro E;
       match goal with H: (L = [] <-> argv = nullval) |- _ => apply H in E end; contradiction);
    rewrite argv_rep_nn by auto; Intros;
    rewrite tbufs_sub by lia; Intros;
    let Hp := fresh "Hp" in
    assert_PROP (isptr (tk_p (Znth j L))) as Hp by (sep_apply (tbuf_isptr (Znth j L)); entailer!);
    forward;
    try (solve [entailer!; rewrite Znth_map by lia; destruct (tk_p (Znth j L)); try contradiction; simpl; auto]);
    sep_apply (tbuf_free (Znth j L));
    rewrite Znth_map by lia;
    forward_call (tarray tschar (tk_n (Znth j L)), tk_p (Znth j L), gv);
    [ rewrite if_false by (let E := fresh in intro E; rewrite E in *; contradiction); cancel | ];
    sep_apply (derives_refl' _ _ (eq_sym (argv_rep_nn argv L ltac:(assumption)))); entailer!.

(* for (j = 0; j < argc; j++) free(argv[j]); *)
Ltac free_args L argv gv :=
  lazymatch goal with |- semax _ (PROPx ?P (LOCALx ?Q (SEPx ?R))) _ _ =>
   let R' := drop_tbufs R in
   forward_for_simple_bound (Zlength L)
     (EX j: Z, PROPx P (LOCALx Q (SEPx (tbufs (sublist j (Zlength L) L) :: R'))))%assert
  end;
  [ pose proof (args_size_len L); rep_lia
  | rewrite sublist_same by auto; entailer!
  | match goal with Hj: 0 <= ?j < Zlength L |- _ => free_body L argv gv j end
  | rewrite sublist_nil, tbufs_nil;
    sep_apply (argv_rep_free argv L);
    forward_call (tarray (tptr tschar) (Zlength L), argv, gv) ].

Definition esc_step (gv: globals) (i: val) (st1: istate) (sh: share) (s: list byte) (t v_p v_errbuf: val)
    (pa: mpred) (ty: int) (argv: val) (L: list tok) (argsize: Z) (rc: int) (w: list byte) (q: val)
    (j d: Z) (out: list byte) : environ -> mpred :=
 (PROP (0 <= d <= j + 1; j < Zlength w; Zlength out = d; ~ In Byte.zero out)
  LOCAL (temp _src (offset_val j q); temp _dst (offset_val d q);
         temp _t__1 q; temp _prevtype (Vint ty);
         temp _argc (Vint (Int.repr (Zlength L))); temp _argv argv;
         temp _argsize (Vlong (Int64.repr argsize)); temp _retcode (Vint rc);
         temp _i i; temp _t t; gvars gv;
         lvar _p t_parser v_p; lvar _errbuf (tarray tschar 1024) v_errbuf)
  SEP (mem_mgr gv; G gv; interp_rep i st1; cstring sh s t; pa;
       data_at_ Tsh (tarray tschar 1024) v_errbuf; argv_rep argv L; tbufs L;
       malloc_token Ews (tarray tschar (Zlength w + 1)) q;
       data_at Ews (tarray tschar (Zlength w + 1))
         (map Vbyte (out ++ sublist d (Zlength w + 1) (w ++ [Byte.zero]))) q))%assert.

Lemma esc_read': forall (out w: list byte) d j, Zlength out = d -> d <= j -> j <= Zlength w ->
  Znth j (out ++ sublist d (Zlength w + 1) (w ++ [Byte.zero])) = Znth j (w ++ [Byte.zero]).
Proof. intros. list_solve. Qed.

Lemma add_ptr_bo: forall p j n, isptr p -> Int.min_signed <= n <= Int.max_signed ->
  force_val (sem_binary_operation' Oadd (tptr tschar) tint (offset_val j p) (Vint (Int.repr n))) =
  offset_val (j + n) p.
Proof.
  intros. rewrite <- (add_ptr_n p j n) by auto. destruct p; try contradiction; simpl; reflexivity.
Qed.

Lemma tbuf_join: forall w n q,
  (cstring Ews w q * ttail (mktok w n q))%logic |-- tbuf (mktok w n q).
Proof. intros. rewrite tbuf_split. simpl. cancel. Qed.

Lemma argsize_upd: forall argsize len, 0 <= argsize <= Int64.max_signed -> 0 <= len <= Int64.max_signed ->
  Int64.add (Int64.repr argsize)
    (Int64.add (Ptrofs.to_int64 (Ptrofs.repr len)) (Int64.repr (Int.signed (Int.repr 1)))) =
  Int64.repr (argsize + (len + 1)).
Proof.
  intros. rewrite (ptrofs_to_int64_repr (eq_refl _)).
  rewrite Int.signed_repr by rep_lia.
  unfold Int64.add.
  rewrite (Int64.unsigned_repr len), (Int64.unsigned_repr 1), (Int64.unsigned_repr argsize) by rep_lia.
  rewrite Int64.unsigned_repr by rep_lia. reflexivity.
Qed.

Lemma data_at_eq_list: forall sh (T: type) (l1 l2: reptype T) p, l1 = l2 ->
  data_at sh T l1 p |-- data_at sh T l2 p.
Proof. intros. subst. auto. Qed.

Lemma join3: forall sh n k1 m2 m3 (l1 l2 l3: list val) p,
  Zlength l1 = k1 -> Zlength l2 = m2 -> Zlength l3 = m3 -> 0 <= k1 -> 0 <= m2 -> 0 <= m3 ->
  n = k1 + m2 + m3 -> field_compatible (tarray tschar n) [] p ->
  (data_at sh (tarray tschar k1) l1 p * data_at sh (tarray tschar m2) l2 (offset_val k1 p) *
   data_at sh (tarray tschar m3) l3 (offset_val (k1 + m2) p))%logic
  |-- data_at sh (tarray tschar n) (l1 ++ l2 ++ l3) p.
Proof.
  intros. subst. rewrite (arr3 sh l1 l2 l3 (Zlength l1 + Zlength l2 + Zlength l3) p) by auto.
  apply derives_refl.
Qed.

Lemma br_nz: forall z, 0 < z < 128 -> Byte.repr z <> Byte.zero.
Proof.
  intros z H X. apply (f_equal Byte.signed) in X. rewrite Byte.signed_repr in X by rep_lia.
  rewrite Byte.signed_zero in X. lia.
Qed.

Ltac esc_case j d out z :=
  forward; forward; rewrite add_ptr_bo by (auto; rep_lia); forward; forward;
  Exists (j + 1) (d + 1) (out ++ [Byte.repr z]); unfold esc_step;
  change (Vint (Int.repr z)) with (Vbyte (Byte.repr z));
  rewrite upd_out by (auto; lia);
  entailer!; split; [list_solve | apply not_in_snoc; [auto | apply br_nz; lia]].

(* after the token has been read and substituted: it is in the buffer q *)
Definition ev_mid (gv: globals) (i: val) (st: istate) (sh: share) (s: list byte) (t v_p v_errbuf: val)
    (k': Z) (stp' en': val) (ty' iq': int) (ty: int) (argv: val) (L: list tok) (argsize: Z)
    : environ -> mpred :=
 (EX st2: istate, EX w: list byte, EX n: Z, EX q: val, EX rc: int,
  PROP (cmds_ok gv (i_cmds st2); (i_level st2 = i_level st + 1)%Z;
        Zlength (i_frames st2) = Zlength (i_frames st))
  LOCAL (temp _t__1 q; temp _prevtype (Vint ty);
         temp _argc (Vint (Int.repr (Zlength L))); temp _argv argv;
         temp _argsize (Vlong (Int64.repr argsize)); temp _retcode (Vint rc);
         temp _i i; temp _t t; gvars gv;
         lvar _p t_parser v_p; lvar _errbuf (tarray tschar 1024) v_errbuf)
  SEP (mem_mgr gv; G gv; interp_rep i st2; cstring sh s t;
       parser_at v_p t s k' stp' en' ty' iq'; data_at_ Tsh (tarray tschar 1024) v_errbuf;
       argv_rep argv L; tbufs L; tbuf (mktok w n q)))%assert.

Lemma body_picolEval: semax_body Vprog Gprog f_picolEval picolEval_spec.
Proof.
start_function.
forward. forward. forward. forward.
take_G gv.
take_lit gv lits 0 ___stringlit_2 v___stringlit_2.
unfold interp_rep. Intros.
forward_call (gv, i, Vint (Int.repr (i_level st)), hdp f_ptr (i_frames st) nullval,
              hdp c_ptr (i_cmds st) nullval, i_result st, i_resultp st,
              Ers, litb v___stringlit_2, gv ___stringlit_2).
Intros q0.
give_lit gv lits 0 ___stringlit_2 v___stringlit_2.
forward. forward. forward.
forward_if.
{ forward. forward.
  rewrite ?add_repr, ?sub_repr.
  replace (i_level st + 1 - 1) with (i_level st) by lia.
  take_lit gv lits 1 ___stringlit_3 v___stringlit_3.
  forward_call (gv, i, Vint (Int.repr (i_level st)), hdp f_ptr (i_frames st) nullval,
              hdp c_ptr (i_cmds st) nullval, litb v___stringlit_2, q0,
              Ers, litb v___stringlit_3, gv ___stringlit_3).
  Intros q1.
  give_lit gv lits 1 ___stringlit_3 v___stringlit_3.
  forward.
  Exists (mkist (i_level st) (i_frames st) (i_cmds st) (litb v___stringlit_3) q1) (Int.repr 1).
  give_G gv. unfold interp_rep. entailer!. simpl. cancel. }
forward_call (v_p, t, sh, s).
give_G gv.
rewrite ?add_repr.
forward_loop (ev_inv gv i st sh s t v_p v_errbuf) break: (ev_brk gv i st sh s t v_p v_errbuf).
{ unfold ev_inv.
  Exists (mkist (i_level st + 1) (i_frames st) (i_cmds st) (litb v___stringlit_2) q0)
         0 nullval nullval (Int.repr 5) (Int.repr 0) nullval (@nil tok) 0 (Int.repr 0).
  unfold interp_rep, argv_rep. rewrite if_true by auto. rewrite tbufs_nil.
  cbn [i_level i_frames i_cmds i_result i_resultp].
  entailer!.
  split; [unfold pinv; left; repeat split; auto|].
  split; [unfold args_size; simpl; rep_lia | tauto]. }
{ unfold ev_inv. Intros st1 k stp en ty iq argv L argsize rc.
  unfold parser_at. forward. forward. fold (parser_at v_p t s k stp en ty iq).
  forward_call (v_p, t, sh, s, k, stp, en, ty, iq).
  Intros vret. destruct vret as [[[[k' stp'] en'] ty'] iq']. simpl fst in *; simpl snd in *.
  unfold parser_at. forward.
  forward_if.
  { forward. unfold ev_brk. Exists st1 argv L rc.
    sep_apply (data_at_data_at_ Tsh t_parser). entailer!. }
  match goal with H: _ \/ ptok _ _ _ _ |- _ => destruct H as [Heof|Hpt] end; [contradiction|].
  unfold ptok in Hpt. destruct Hpt as (a & b0 & Hab & Hb0 & Hst & Hen).
  subst stp' en'.
  sep_apply (cstring_unfold sh s t). Intros.
  match goal with H: ~ In Byte.zero s |- _ => rename H into Hnz end.
  assert_PROP (isptr t) as Ht by entailer!.
  assert_PROP (field_compatible (tarray tschar (Zlength s + 1)) [] t) as Hft by entailer!.
  forward. forward. forward.
  { entailer!. rewrite sub_pp_off by auto.
    destruct (tc_sub_pp t a b0 Ht ltac:(lia) ltac:(rep_lia)) as [Hx1 Hx2].
    simpl. apply andp_right; apply prop_right; auto. }
  rewrite tlen_val by (auto; rep_lia).
  forward_if (True).
  { exfalso. rewrite ?Int.signed_repr in * by rep_lia. lia. }
  { forward. entailer!. }
  Intros.
  take_G gv.
  forward_call (existT (fun t => list (reptype t)) tschar [], nullval, 0, b0 - a + 1, gv).
  all: try solve [rep_lia | (rewrite if_true by auto; cancel)].
  all: try solve [entailer!].
  Intros q. simpl projT1 in *; simpl projT2 in *.
  forward.
  rewrite (src3 sh s a b0 t) by (auto; lia).
  assert_PROP (field_compatible (tarray tschar (b0 - a + 1)) [] q) as Hfq by entailer!.
  assert_PROP (isptr q) as Hq by entailer!.
  rewrite (newbuf_split (b0 - a) q) by (auto; lia).
  Intros.
  forward_call (Ews, sh, q, offset_val a t, b0 - a, sublist a b0 s).
  all: try solve [repeat split; auto; try rep_lia; try list_solve].
  sep_apply (newbuf_join' (sublist a b0 s) (b0 - a) q ltac:(list_solve) Hfq).
  forward.
  rewrite (last0_upd (sublist a b0 s) (b0 - a)) by list_solve.
  sep_apply (derives_refl' _ _ (eq_sym (src3 sh s a b0 t ltac:(lia) ltac:(lia) Hft))).
  sep_apply (cstring_fold sh s t Hnz).
  assert (Hw: Zlength (sublist a b0 s) = b0 - a) by list_solve.
  assert (Hwnz: ~ In Byte.zero (sublist a b0 s)) by (apply not_in_sub; auto).
  set (w := sublist a b0 s) in *.
  replace (b0 - a + 1) with (Zlength w + 1) by lia.
  sep_apply (tbuf_mstr w q Hwnz).
  give_G gv.
  forward.
  forward_if (ev_mid gv i st sh s t v_p v_errbuf k' (offset_val a t) (offset_val (b0 - 1) t) ty' iq'
                ty argv L argsize).
  { (* VAR *)
    unfold mstr. Intros.
    forward_call (i, st1, Ews, w, q).
    Intros kk.
    destruct (find_var_split w (f_vars (Znth kk (i_frames st1))))
      as [[Hn _] | (V1 & r & V2 & HV & Hall & Hnm & Hfind)].
    + rewrite Hn.
      forward_if.
      2:{ absurd_hyp. }
      take_G gv.
      take_lit gv lits 3 ___stringlit_5 v___stringlit_5.
      take_lit gv (sublist 0 3 lits ++ sublist (3+1) (Zlength lits) lits) 2
         ___stringlit_4 v___stringlit_4.
      forward_call (Tsh, v_errbuf, 1024, Ers, litb v___stringlit_5, gv ___stringlit_5, Ews, w, q,
                    Ers, litb v___stringlit_4, gv ___stringlit_4).
      Intros s0. unfold strbuf. Intros rest.
      rewrite strbuf_split by auto.
      sep_apply (derives_refl' _ _ (eq_sym (mstr_eq w q))).
      sep_apply (mstr_free w q). Intros.
      forward_call (tarray tschar (Zlength w + 1), q, gv).
      { rewrite if_false by (intro; subst; contradiction). cancel. }
      unfold interp_rep. Intros.
      forward_call (gv, i, Vint (Int.repr (i_level st1)), hdp f_ptr (i_frames st1) nullval,
                    hdp c_ptr (i_cmds st1) nullval, i_result st1, i_resultp st1, Tsh, s0, v_errbuf).
      Intros q1.
      sep_apply (derives_refl' _ _ (eq_sym (strbuf_split Tsh s0 1024 rest v_errbuf
                    ltac:(auto) ltac:(auto) ltac:(auto)))).
      give_lit gv (sublist 0 3 lits ++ sublist (3+1) (Zlength lits) lits) 2
         ___stringlit_4 v___stringlit_4.
      give_lit gv lits 3 ___stringlit_5 v___stringlit_5.
      sep_apply (data_at_data_at_ Tsh (tarray tschar 1024)).
      sep_apply (data_at_data_at_ Tsh t_parser).
      forward. forward.
      unfold ev_brk. Exists (set_res st1 s0 q1) argv L (Int.repr 1).
      unfold interp_rep, set_res, G. rewrite Gr_GL. cbn [i_level i_frames i_cmds i_result i_resultp].
      entailer!.
    + rewrite Hfind.
      destruct (split_at (i_frames st1) kk ltac:(auto)) as (F1 & F2 & HFk & HF1).
      set (f := Znth kk (i_frames st1)) in *. clearbody f.
      unfold interp_rep. Intros.
      rewrite HFk, (frames_var_focus F1 f F2 V1 r V2 HV). Intros.
      forward_if.
      { nonnull_contra (v_ptr r). }
      sep_apply (derives_refl' _ _ (eq_sym (mstr_eq w q))).
      sep_apply (mstr_free w q). Intros.
      forward_call (tarray tschar (Zlength w + 1), q, gv).
      { rewrite if_false by (intro; subst; contradiction). cancel. }
      forward.
      take_G gv.
      forward_call (Ews, v_val r, v_valp r, gv).
      Intros q2.
      give_G gv.
      try forward.
      unfold ev_mid. Exists st1 (v_val r) (Zlength (v_val r) + 1) q2 rc.
      sep_apply (mstr_tbuf (v_val r) q2).
      unfold interp_rep. rewrite HFk, (frames_var_focus F1 f F2 V1 r V2 HV).
      entailer!. }
  forward.
  forward_if.
  { (* CMD *)
    unfold mstr. Intros.
    forward_call (gv, i, st1, Ews, w, q).
    Intros vret. destruct vret as [st2 r2]. simpl fst in *; simpl snd in *.
    sep_apply (derives_refl' _ _ (eq_sym (mstr_eq w q))).
    sep_apply (mstr_free w q). Intros.
    forward_call (tarray tschar (Zlength w + 1), q, gv).
    { rewrite if_false by (intro; subst; contradiction). cancel. }
    forward_if (r2 = Int.repr 0).
    { forward. unfold ev_brk. Exists st2 argv L r2.
      sep_apply (data_at_data_at_ Tsh t_parser). entailer!. }
    { forward. entailer!. }
    Intros.
    unfold interp_rep. Intros. forward.
    unfold mstr. Intros.
    take_G gv.
    forward_call (Ews, i_result st2, i_resultp st2, gv).
    Intros q2. give_G gv.
    try forward.
    unfold ev_mid. Exists st2 (i_result st2) (Zlength (i_result st2) + 1) q2 r2.
    sep_apply (mstr_tbuf (i_result st2) q2).
    unfold interp_rep, mstr, parser_at. entailer!. }
  forward.
  forward_if.
  { (* ESC *)
    unfold mstr. Intros.
    sep_apply (cstring_unfold Ews w q). Intros.
    forward. forward.
    forward_loop (EX j: Z, EX d: Z, EX out: list byte,
        esc_base gv i st1 sh s t v_p v_errbuf
          (parser_at v_p t s k' (offset_val a t) (offset_val (b0 - 1) t) ty' iq')
          ty argv L argsize rc w q j d out)%assert
      break: (EX d: Z, EX out: list byte,
        esc_base gv i st1 sh s t v_p v_errbuf
          (parser_at v_p t s k' (offset_val a t) (offset_val (b0 - 1) t) ty' iq')
          ty argv L argsize rc w q (Zlength w) d out)%assert.
    { Exists 0 0 (@nil byte). unfold esc_base, parser_at.
      rewrite sublist_same by list_solve. simpl app.
      rewrite isptr_offset_val_zero by auto. entailer!. }
    { Intros j d out. unfold esc_base. Intros.
      char_addr j w q.
      forward.
      rewrite esc_read' by (auto; lia).
      forward_if.
      2:{ match goal with H: typed_false tschar _ |- _ => apply typed_false_byte in H; rename H into Hz end.
          destruct (char_cases w j ltac:(lia) Hwnz) as [(Hlt & Heq & Hnz')|(Hj & _)];
            [rewrite Heq in Hz; contradiction | subst j].
          forward. Exists d out. unfold esc_base. entailer!. }
      match goal with H: typed_true tschar _ |- _ => apply typed_true_byte in H; rename H into Hc end.
      assert (Hj: j < Zlength w).
      { destruct (char_cases w j ltac:(lia) Hwnz) as [(Hlt & _ & _)|(Hj & Heq)]; auto.
        rewrite Heq in Hc; contradiction. }
      rewrite app_Znth1 in Hc |- * by lia.
      forward.
      rewrite esc_read' by (auto; lia). rewrite app_Znth1 by lia.
      match goal with |- semax _ (PROPx ?P (LOCALx ?Q (SEPx ?R))) _ _ =>
        forward_if (EX b: bool, PROPx ((b = true -> j + 1 < Zlength w) :: P)
                      (LOCALx (temp _t'12 (Val.of_bool b) :: Q) (SEPx R)))%assert end.
      { (* backslash: look at the next char *)
        assert_PROP (force_val (sem_add_ptr_int tschar Signed (offset_val j q) (Vint (Int.repr 1))) =
               field_address (tarray tschar (Zlength w + 1)) (SUB (j + 1)) q) as Ha1.
        { rewrite add_ptr_n by (auto; rep_lia). entailer!. unfold field_address.
          rewrite if_true; [simpl; f_equal; lia | auto with field_compatible]. }
        forward.
        rewrite esc_read' by (auto; lia).
        forward.
        Exists (negb (Int.eq (Int.repr (Byte.signed (Znth (j + 1) (w ++ [Byte.zero])))) Int.zero)).
        entailer!. split.
        { intro E. destruct (char_cases w (j + 1) ltac:(lia) Hwnz) as [(Hlt & _ & _)|(Hj1 & Heq)]; auto.
          rewrite Heq in E. vm_compute in E. discriminate. }
        { destruct (Int.eq _ _); reflexivity. } }
      { forward. Exists false. entailer!. }
      Intros b.
      forward_if (EX j1: Z, EX d1: Z, EX out1: list byte,
        esc_step gv i st1 sh s t v_p v_errbuf
          (parser_at v_p t s k' (offset_val a t) (offset_val (b0 - 1) t) ty' iq')
          ty argv L argsize rc w q j1 d1 out1)%assert.
      { use_bb. match goal with H: true = true -> _ |- _ => specialize (H eq_refl) end.
        forward.
        rewrite add_ptr_bo by (auto; rep_lia).
        char_addr (j + 1) w q.
        forward.
        rewrite esc_read' by (auto; lia). rewrite app_Znth1 by lia.
        assert (Hc1: Znth (j + 1) w <> Byte.zero) by (intro X; apply Hwnz; rewrite <- X; apply Znth_In; lia).
        pose proof (Byte.signed_range (Znth (j + 1) w)).
        char_addr d w q.
        forward_if.
        { esc_case j d out 10. }
        { esc_case j d out 9. }
        { esc_case j d out 13. }
        { forward. forward. rewrite add_ptr_bo by (auto; rep_lia).
          forward. rewrite esc_read' by (auto; lia). rewrite app_Znth1 by lia.
          forward. forward.
          Exists (j + 1) (d + 1) (out ++ [Znth (j + 1) w]). unfold esc_step.
          change (Vint (Int.repr (Byte.signed (Znth (j + 1) w)))) with (Vbyte (Znth (j + 1) w)).
          rewrite upd_out by (auto; lia).
          entailer!. split; [list_solve | apply not_in_snoc; auto]. } }
      { forward. forward. rewrite add_ptr_bo by (auto; rep_lia).
        forward. rewrite esc_read' by (auto; lia). rewrite app_Znth1 by lia.
        char_addr d w q. forward.
        assert (Hcj: Znth j w <> Byte.zero) by (intro X; apply Hwnz; rewrite <- X; apply Znth_In; lia).
        Exists j (d + 1) (out ++ [Znth j w]). unfold esc_step.
        change (Vint (Int.repr (Byte.signed (Znth j w)))) with (Vbyte (Znth j w)).
        rewrite upd_out by (auto; lia).
        entailer!.
        split; [list_solve | apply not_in_snoc; auto]. }
      Intros j1 d1 out1. unfold esc_step. Intros.
      forward.
      Exists (j1 + 1) d1 out1. unfold esc_base. entailer!. }
    Intros d out. unfold esc_base. Intros.
    char_addr d w q.
    forward.
    rewrite esc_done by (auto; lia).
    unfold ev_mid. Exists st1 out (Zlength w + 1) q rc.
    unfold tbuf, strbuf. cbn [tk_s tk_n tk_p].
    Exists (map Vbyte (sublist (d + 1) (Zlength w + 1) (w ++ [Byte.zero]))).
    unfold parser_at. entailer!.
    list_solve. }
  forward.
  forward_if.
  { (* SEP *)
    forward.
    sep_apply (mstr_free w q). Intros.
    forward_call (tarray tschar (Zlength w + 1), q, gv).
    { rewrite if_false by (intro; subst; contradiction). cancel. }
    forward.
    unfold ev_inv. Exists st1 k' (offset_val a t) (offset_val (b0 - 1) t) ty' iq' argv L argsize rc.
    unfold parser_at. entailer!. }
  { forward. unfold ev_mid. Exists st1 w (Zlength w + 1) q rc.
    sep_apply (mstr_tbuf w q). unfold parser_at. entailer!. }
  clear dependent w. clear dependent q.
  unfold ev_mid. Intros st2 w n q rc2.
  unfold parser_at. forward.
  forward_if (ty' <> Int.repr 5).
  { (* EOL *)
    sep_apply (tbuf_isptr (mktok w n q)). Intros. simpl tk_p in *.
    sep_apply (tbuf_free (mktok w n q)). simpl tk_n; simpl tk_p.
    forward_call (tarray tschar n, q, gv).
    { rewrite if_false by (intro; subst; contradiction). cancel. }
    forward.
    forward_if (EX st3: istate, EX rc3: int,
      PROP (cmds_ok gv (i_cmds st3); (i_level st3 = i_level st + 1)%Z;
            Zlength (i_frames st3) = Zlength (i_frames st))
      LOCAL (temp _prevtype (Vint ty'); temp _argc (Vint (Int.repr (Zlength L))); temp _argv argv;
             temp _argsize (Vlong (Int64.repr argsize)); temp _retcode (Vint rc3);
             temp _i i; temp _t t; gvars gv;
             lvar _p t_parser v_p; lvar _errbuf (tarray tschar 1024) v_errbuf)
      SEP (mem_mgr gv; G gv; interp_rep i st3; cstring sh s t;
           data_at Tsh t_parser (t, (offset_val k' t, (Vint (Int.repr (Zlength s - k')),
              (offset_val a t, (offset_val (b0 - 1) t, (Vint ty', Vint iq')))))) v_p;
           data_at_ Tsh (tarray tschar 1024) v_errbuf; argv_rep argv L; tbufs L))%assert.
    { (* argc <> 0: run the command *)
      assert (HL: L <> []) by (intro; subst L; absurd_hyp).
      assert (Hav: argv <> nullval) by (intro E; apply H10 in E; contradiction).
      assert (HL1: 1 <= Zlength L) by (destruct L; [contradiction | list_solve]).
      rewrite argv_rep_nn by auto. Intros.
      rewrite tbufs_split.
      rewrite (args_focus 0 (map tk_s L) (map tk_p L)) by list_solve. Intros.
      forward.
      forward_call (i, st2, Ews, Znth 0 (map tk_s L), Znth 0 (map tk_p L)).
      forward. forward.
      destruct (find_cmd_split (Znth 0 (map tk_s L)) (i_cmds st2))
        as [[Hn _] | (C1 & r & C2 & HC & Hall & Hnm & Hfind)].
      + rewrite Hn. forward_if.
        2:{ absurd_hyp. }
        forward.
        take_G gv.
        take_lit gv lits 4 ___stringlit_6 v___stringlit_6.
        take_lit gv (sublist 0 4 lits ++ sublist (4+1) (Zlength lits) lits) 2
           ___stringlit_4 v___stringlit_4.
        forward_call (Tsh, v_errbuf, 1024, Ers, litb v___stringlit_6, gv ___stringlit_6,
                      Ews, Znth 0 (map tk_s L), Znth 0 (map tk_p L),
                      Ers, litb v___stringlit_4, gv ___stringlit_4).
        Intros s0. unfold strbuf. Intros rest.
        rewrite strbuf_split by auto.
        unfold interp_rep. Intros.
        forward_call (gv, i, Vint (Int.repr (i_level st2)), hdp f_ptr (i_frames st2) nullval,
                      hdp c_ptr (i_cmds st2) nullval, i_result st2, i_resultp st2, Tsh, s0, v_errbuf).
        Intros q1.
        sep_apply (derives_refl' _ _ (eq_sym (strbuf_split Tsh s0 1024 rest v_errbuf
                      ltac:(auto) ltac:(auto) ltac:(auto)))).
        give_lit gv (sublist 0 4 lits ++ sublist (4+1) (Zlength lits) lits) 2
           ___stringlit_4 v___stringlit_4.
        give_lit gv lits 4 ___stringlit_6 v___stringlit_6.
        sep_apply (data_at_data_at_ Tsh (tarray tschar 1024)).
        sep_apply (data_at_data_at_ Tsh t_parser).
        sep_apply (derives_refl' _ _ (eq_sym (args_focus 0 (map tk_s L) (map tk_p L)
                      ltac:(list_solve) ltac:(list_solve)))).
        sep_apply (derives_refl' _ _ (eq_sym (tbufs_split L))).
        forward. forward.
        unfold ev_brk. Exists (set_res st2 s0 q1) argv L (Int.repr 1).
        rewrite argv_rep_nn by auto.
        unfold interp_rep, set_res, G. rewrite Gr_GL. cbn [i_level i_frames i_cmds i_result i_resultp].
        entailer!.
      + rewrite Hfind.
        sep_apply (derives_refl' _ _ (eq_sym (args_focus 0 (map tk_s L) (map tk_p L)
                      ltac:(list_solve) ltac:(list_solve)))).
        unfold interp_rep. Intros. rewrite HC. rewrite cmds_split, cmd_node_eq. Intros.
        forward_if.
        { nonnull_contra (c_ptr r). }
        assert (Hok: cmd_ok gv r).
        { match goal with H: cmds_ok gv (i_cmds st2) |- _ => rewrite HC in H; unfold cmds_ok in H;
            apply Forall_app in H; destruct H as [_ H]; inv H; auto end. }
        assert (Hin: In (c_ptr r) (map c_ptr (i_cmds st2))) by (rewrite HC, map_app; apply in_or_app; right; left; auto).
        destruct Hok as [Hbi | (Ecp & aa & bb & Ha & Hb & Hbb)].
        * call_builtin Hbi.
          forward.
          sep_apply (derives_refl' _ _ (eq_sym (cmd_node_eq r (hdp c_ptr C2 nullval)))).
          sep_apply (derives_refl' _ _ (eq_sym (cmds_split C1 r C2))).
          rewrite <- HC.
          sep_apply (interp_refold i st2 ltac:(auto) ltac:(auto)).
          forward_call (gv, i, st2, Zlength L, argv, map tk_p L, map tk_s L, c_ptr r).
          { rewrite !Zlength_map; auto. }
          cmd_tail st2 argv L.
        * match goal with |- semax ?D (PROPx ?P (LOCALx ?Q (SEPx ?R))) ?c ?Post =>
            assert (HFP: semax D (PROPx P (LOCALx Q (SEPx
                     (func_ptr' (snd picolCommandCallProc_spec) (c_func r) :: R)))) c Post ->
                     semax D (PROPx P (LOCALx Q (SEPx R))) c Post) end.
          { intro HS. make_func_ptr _picolCommandCallProc. rewrite <- Ecp. exact HS. }
          apply HFP; clear HFP.
          forward.
          sep_apply (derives_refl' _ _ (eq_sym (cmd_node_eq r (hdp c_ptr C2 nullval)))).
          sep_apply (derives_refl' _ _ (eq_sym (cmds_split C1 r C2))).
          rewrite <- HC.
          sep_apply (interp_refold i st2 ltac:(auto) ltac:(auto)).
          forward_call (gv, i, st2, Zlength L, argv, map tk_p L, map tk_s L, c_ptr r).
          { split; [rewrite Zlength_map; auto|]. split; [rewrite Zlength_map; auto|].
            exists r. split; [rewrite HC; apply in_or_app; right; left; auto|].
            split; auto. split; auto. exists aa, bb. auto. }
          cmd_tail st2 argv L. }
    { forward. Exists st2 rc2. entailer!. }
    Intros st3 rc3.
    free_args L argv gv.
    forward. forward. forward. forward.
    unfold ev_inv.
    Exists st3 k' (offset_val a t) (offset_val (b0 - 1) t) ty' iq' nullval (@nil tok) 0 rc3.
    rewrite argv_rep_null, tbufs_nil. unfold parser_at.
    entailer!. split; [unfold args_size; simpl; rep_lia | tauto]. }
  { forward. entailer!. }
  Intros.
  (* not EOL: append the token *)
  sep_apply (tbuf_isptr (mktok w n q)). Intros. simpl tk_p in *.
  rewrite tbuf_split. cbn [tk_s tk_p tk_n]. Intros.
  assert_PROP (Zlength w + 1 <= Ptrofs.max_unsigned) as Hwl by (sep_apply (cstring_len Ews w q); entailer!).
  forward_call (Ews, w, q).
  forward_if (Zlength w + 1 <= Int.max_signed - 10 - argsize).
  { (* Command too long *)
    sep_apply (tbuf_join w n q).
    sep_apply (tbuf_free (mktok w n q)). cbn [tk_n tk_p].
    forward_call (tarray tschar n, q, gv).
    { rewrite if_false by (intro; subst; contradiction). cancel. }
    take_G gv.
    take_lit gv lits 5 ___stringlit_7 v___stringlit_7.
    unfold interp_rep. Intros.
    forward_call (gv, i, Vint (Int.repr (i_level st2)), hdp f_ptr (i_frames st2) nullval,
                  hdp c_ptr (i_cmds st2) nullval, i_result st2, i_resultp st2,
                  Ers, litb v___stringlit_7, gv ___stringlit_7).
    Intros q1.
    give_lit gv lits 5 ___stringlit_7 v___stringlit_7.
    sep_apply (data_at_data_at_ Tsh t_parser).
    forward. forward.
    unfold ev_brk. Exists (set_res st2 (litb v___stringlit_7) q1) argv L (Int.repr 1).
    unfold interp_rep, set_res, G. rewrite Gr_GL. cbn [i_level i_frames i_cmds i_result i_resultp].
    entailer!. }
  { forward. entailer!.
    pose proof (args_size_nonneg (map tk_s L)).
    match goal with H: Int64.unsigned (Int64.repr _) >= Int64.unsigned (Int64.repr _) |- _ =>
      rewrite !Int64.unsigned_repr in H by rep_lia end.
    rep_lia. }
  Intros.
  forward.
  match goal with |- semax _ (PROPx ?P (LOCALx ?Q (SEPx ?R))) _ _ =>
    forward_if (EX b: bool, PROPx ((if b then True else (ty <> Int.repr 4 /\ ty <> Int.repr 5)) :: P)
                  (LOCALx (temp _t'21 (Val.of_bool b) :: Q) (SEPx R)))%assert end.
  { forward. Exists true. entailer!. }
  { forward. Exists (Int.eq ty (Int.repr 5)). entailer!.
    split; [| destruct (Int.eq ty (Int.repr 5)); reflexivity].
    destruct (Int.eq ty (Int.repr 5)) eqn:E5; auto.
    split.
    { assumption. }
    { intro X. subst. rewrite Int.eq_true in E5. discriminate. } }
  Intros bb.
  forward_if (EX argv': val, EX L': list tok, EX argsize': Z,
    PROP (args_size (map tk_s L') <= argsize' <= Int.max_signed - 10; L' <> []; argv' <> nullval)
    LOCAL (temp _argc (Vint (Int.repr (Zlength L'))); temp _argv argv';
           temp _argsize (Vlong (Int64.repr argsize')); temp _retcode (Vint rc2);
           temp _i i; temp _t t; gvars gv;
           lvar _p t_parser v_p; lvar _errbuf (tarray tschar 1024) v_errbuf)
    SEP (mem_mgr gv; G gv; interp_rep i st2; cstring sh s t;
         data_at Tsh t_parser (t, (offset_val k' t, (Vint (Int.repr (Zlength s - k')),
              (offset_val a t, (offset_val (b0 - 1) t, (Vint ty', Vint iq')))))) v_p;
         data_at_ Tsh (tarray tschar 1024) v_errbuf; argv_rep argv' L'; tbufs L'))%assert.
  { (* new argument *)
    use_bb.
    pose proof (args_size_nonneg (map tk_s L)). pose proof (args_size_len L).
    rewrite argsize_upd by rep_lia.
    unfold argv_rep. unfold G. Intros.
    forward_call (existT (fun t => list (reptype t)) (tptr tschar) (map tk_p L), argv,
                  Zlength L, Zlength L + 1, gv).
    all: try solve [rewrite ?Int.signed_repr by rep_lia; rep_lia | entailer!
                   | simpl projT1; simpl projT2; cancel
                   | split; [simpl; rep_lia| intro E; apply H10 in E; subst; auto]].
    Intros argv2. simpl projT1 in *; simpl projT2 in *.
    rewrite Z.min_l by lia. rewrite sublist_same by list_solve.
    replace (Zlength L + 1 - Zlength L) with 1 by lia.
    change (Zrepeat (default_val (tptr tschar)) 1) with [Vundef].
    forward.
    all: try solve [entailer!].
    forward.
    assert_PROP (isptr argv2) as Ha2 by entailer!.
    sep_apply (tbuf_join w n q).
    sep_apply (G_fold gv).
    Exists argv2 (L ++ [mktok w n q]) (argsize + (Zlength w + 1)).
    unfold argv_rep. rewrite if_false by (intro E; subst; contradiction).
    rewrite tbufs_app, tbufs_one.
    rewrite args_size_map_app.
    assert (Hz: Zlength (L ++ [mktok w n q]) = Zlength L + 1) by list_solve.
    rewrite Hz.
    replace (upd_Znth (Zlength L) (map tk_p L ++ [Vundef]) q) with (map tk_p (L ++ [mktok w n q]))
      by list_solve.
    entailer!.
    change (args_size [tk_s {| tk_s := w; tk_n := n; tk_p := q |}]) with (Zlength w + 1 + 0).
    repeat split; try lia.
    { intro X. apply app_eq_nil in X. destruct X as [_ X]. inv X. }
    { apply derives_refl'. f_equal. list_solve. } }
  { (* append to the last argument *)
    destruct bb; [match goal with H: typed_false _ _ |- _ => inv H end|].
    match goal with H: ty <> Int.repr 4 /\ ty <> Int.repr 5 |- _ => destruct H as [Hn4 Hn5] end.
    assert (HL: L <> []) by (destruct H11 as [?|[?|?]]; [contradiction|contradiction|auto]).
    pose proof (args_size_nonneg (map tk_s L)). pose proof (args_size_len L).
    rewrite argsize_upd by rep_lia.
    destruct (exists_last HL) as (L0 & x & HLx). subst L.
    assert (Hav: argv <> nullval) by (intro E; apply H10 in E; contradiction).
    rewrite argv_rep_nn by auto. Intros.
    rewrite tbufs_app, tbufs_one, tbuf_split. Intros.
    assert (HLz: Zlength (L0 ++ [x]) = Zlength L0 + 1) by list_solve.
    rewrite args_size_map_app in *.
    assert (Hxs: args_size (map tk_s [x]) = Zlength (tk_s x) + 1) by (unfold args_size; simpl; lia).
    pose proof (args_size_nonneg (map tk_s L0)).
    assert (Hlast: forall d: Inhabitant val, @Znth val d (Zlength (L0 ++ [x]) - 1) (map tk_p (L0 ++ [x])) = tk_p x).
    { intro d. rewrite HLz. rewrite map_app. rewrite app_Znth2 by list_solve.
      rewrite Zlength_map. replace (Zlength L0 + 1 - 1 - Zlength L0) with 0 by lia. reflexivity. }
    assert_PROP (isptr (tk_p x)) as Hpx by (sep_apply (cstring_len2 Ews (tk_s x) (tk_p x)); entailer!).
    forward.
    all: try solve [entailer!].
    { entailer!. match goal with |- is_pointer_or_null ?v => replace v with (tk_p x) by list_solve end.
      destruct (tk_p x); try contradiction; simpl; auto. }
    match goal with |- context [temp _t'27 ?v] => replace v with (tk_p x) by list_solve end.
    eapply semax_seq'.
    { forward_call (Ews, tk_s x, tk_p x). apply ENTAIL_refl. }
    unfold MORE_COMMANDS, abbreviate.
    assert_PROP (Zlength (tk_s x) + 1 <= Ptrofs.max_unsigned) as Hxl
      by (sep_apply (cstring_len Ews (tk_s x) (tk_p x)); entailer!).
    forward.
    try rewrite len_norm by rep_lia.
    eapply semax_seq'.
    { forward_call (Ews, w, q). forward. apply ENTAIL_refl. }
    unfold MORE_COMMANDS, abbreviate.
    try rewrite len_norm by rep_lia.
    forward.
    all: try solve [entailer!].
    all: try solve [entailer!; match goal with |- is_pointer_or_null ?v => replace v with (tk_p x) by list_solve end;
      destruct (tk_p x); try contradiction; simpl; auto].
    match goal with |- context [temp _t'26 ?v] => replace v with (tk_p x) by list_solve end.
    sep_apply (derives_refl' _ _ (eq_sym (tbuf_split x))).
    rewrite (tbuf_unfold x). Intros rest.
    unfold G. Intros.
    forward_call (existT (fun t => list (reptype t)) tschar (map Vbyte (tk_s x ++ [Byte.zero]) ++ rest),
                  tk_p x, tk_n x, Zlength (tk_s x) + Zlength w + 1, gv).
    all: try solve [rewrite ?Int.signed_repr by rep_lia; rep_lia | entailer!
                   | simpl projT1; simpl projT2; rewrite if_false by (intro E; rewrite E in Hpx; contradiction); cancel
                   | simpl; repeat split; try rep_lia; intro E; rewrite E in Hpx; contradiction].
    { entailer!. simpl. rewrite Int.signed_repr by rep_lia. reflexivity. }
    { simpl projT1; simpl projT2. split; [rep_lia|]. intro E; rewrite E in Hpx; contradiction. }
    Intros p2. simpl projT1 in *; simpl projT2 in *.
    assert_PROP (isptr p2) as Hp2 by entailer!.
    assert_PROP (field_compatible (tarray tschar (Zlength (tk_s x) + Zlength w + 1)) [] p2) as Hfp
      by entailer!.
    forward.
    all: try solve [entailer!].
    forward.
    all: try solve [entailer!; match goal with |- is_pointer_or_null ?v => replace v with p2 by list_solve end;
      destruct p2; try contradiction; simpl; auto].
    match goal with |- context [temp _t'25 ?v] => replace v with p2 by list_solve end.
    match goal with |- context [data_at Ews (tarray tschar _) ?C p2] => set (CC := C) end.
    assert (HCl: Zlength CC = Zlength (tk_s x) + Zlength w + 1).
    { subst CC.
      destruct (Z.min_spec (tk_n x) (Zlength (tk_s x) + Zlength w + 1)) as [[? Hm]|[? Hm]];
        rewrite Hm; list_solve. }
    assert (HC0: sublist 0 (Zlength (tk_s x)) CC = map Vbyte (tk_s x)).
    { subst CC.
      destruct (Z.min_spec (tk_n x) (Zlength (tk_s x) + Zlength w + 1)) as [[? Hm]|[? Hm]];
        rewrite Hm; list_solve. }
    pose proof (Zlength_nonneg w). pose proof (Zlength_nonneg (tk_s x)).
    rewrite (buf_split3 Ews (Zlength (tk_s x) + Zlength w + 1) (Zlength (tk_s x))
               (Zlength (tk_s x) + Zlength w) CC p2) by (auto; lia).
    Intros.
    sep_apply (data_at_eq_list Ews (tarray tschar (Zlength (tk_s x))) _ (map Vbyte (tk_s x)) p2 HC0).
    replace (Zlength (tk_s x) + Zlength w - Zlength (tk_s x)) with (Zlength w) by lia.
    replace (Zlength (tk_s x) + Zlength w + 1 - (Zlength (tk_s x) + Zlength w)) with 1 by lia.
    sep_apply (data_at_data_at_ Ews (tarray tschar (Zlength w))
                 (sublist (Zlength (tk_s x)) (Zlength (tk_s x) + Zlength w) CC)
                 (offset_val (Zlength (tk_s x)) p2)).
    sep_apply (cstring_unfold Ews w q). Intros.
    assert_PROP (field_compatible (tarray tschar (Zlength w + 1)) [] q) as Hfq by entailer!.
    rewrite map_app.
    rewrite (arr_split2 Ews (Zlength w + 1) (Zlength w) 1 (map Vbyte w) (map Vbyte [Byte.zero]) q)
      by (try lia; try list_solve; auto).
    Intros.
    forward_call (Ews, Ews, offset_val (Zlength (tk_s x)) p2, q, Zlength w, w).
    sep_apply (derives_refl' _ _ (eq_sym (arr_split2 Ews (Zlength w + 1) (Zlength w) 1 (map Vbyte w)
       (map Vbyte [Byte.zero]) q ltac:(lia) ltac:(list_solve) ltac:(list_solve) ltac:(lia) ltac:(lia) Hfq))).
    rewrite <- map_app.
    sep_apply (cstring_fold Ews w q ltac:(assumption)).
    sep_apply (join3 Ews (Zlength (tk_s x) + Zlength w + 1) (Zlength (tk_s x)) (Zlength w) 1
                 (map Vbyte (tk_s x)) (map Vbyte w)
                 (sublist (Zlength (tk_s x) + Zlength w) (Zlength (tk_s x) + Zlength w + 1) CC) p2
                 ltac:(list_solve) ltac:(list_solve) ltac:(list_solve) ltac:(lia) ltac:(lia) ltac:(lia)
                 ltac:(lia) Hfp).
    forward.
    all: try solve [entailer!; match goal with |- is_pointer_or_null ?v => replace v with p2 by list_solve end;
      destruct p2; try contradiction; simpl; auto].
    match goal with |- context [temp _t'24 ?v] => replace v with p2 by list_solve end.
    forward.
    all: try solve [entailer!].
    sep_apply (tbuf_join w n q).
    sep_apply (tbuf_free (mktok w n q)). cbn [tk_n tk_p].
    forward_call (tarray tschar n, q, gv).
    { rewrite if_false by (intro E; rewrite E in H19; contradiction). cancel. }
    sep_apply (G_fold gv).
    Exists argv (L0 ++ [mktok (tk_s x ++ w) (Zlength (tk_s x) + Zlength w + 1) p2])
           (argsize + (Zlength w + 1)).
    assert (Hxw: ~ In Byte.zero (tk_s x ++ w)) by (apply not_in_app; assumption).
    sep_apply (data_at_eq_list Ews (tarray tschar (Zlength (tk_s x) + Zlength w + 1))
                 (upd_Znth (Zlength (tk_s x) + Zlength w)
                    (map Vbyte (tk_s x) ++ map Vbyte w ++
                     sublist (Zlength (tk_s x) + Zlength w) (Zlength (tk_s x) + Zlength w + 1) CC)
                    (Vint (Int.repr 0)))
                 (map Vbyte ((tk_s x ++ w) ++ [Byte.zero])) p2 ltac:(list_solve)).
    sep_apply (data_at_eq_list Ews (tarray (tptr tschar) (Zlength (L0 ++ [x])))
                 (upd_Znth (Zlength (L0 ++ [x]) - 1) (map tk_p (L0 ++ [x])) p2)
                 (map tk_p (L0 ++ [mktok (tk_s x ++ w) (Zlength (tk_s x) + Zlength w + 1) p2]))
                 argv ltac:(list_solve)).
    replace (Zlength (tk_s x) + Zlength w + 1) with (Zlength (tk_s x ++ w) + 1) by list_solve.
    sep_apply (tbuf_of_buf (tk_s x ++ w) p2 Hxw).
    rewrite argv_rep_nn by auto. rewrite tbufs_app, tbufs_one.
    replace (Zlength (L0 ++ [mktok (tk_s x ++ w) (Zlength (tk_s x ++ w) + 1) p2]))
      with (Zlength (L0 ++ [x])) by list_solve.
    rewrite args_size_map_app.
    change (args_size (map tk_s [mktok (tk_s x ++ w) (Zlength (tk_s x ++ w) + 1) p2]))
      with (Zlength (tk_s x ++ w) + 1 + 0).
    rewrite Zlength_app.
    entailer!.
    repeat split; try rep_lia; try (rewrite Zlength_app; rep_lia).
    intro X. apply app_eq_nil in X. destruct X as [_ X]. inv X. }
  Intros argv' L' argsize'.
  forward.
  unfold ev_inv.
  Exists st2 k' (offset_val a t) (offset_val (b0 - 1) t) ty' iq' argv' L' argsize' rc2.
  unfold parser_at. entailer!.
  split; intro X; [subst; contradiction | contradiction]. }
unfold ev_brk. Intros st1 argv L rc.
free_args L argv gv.
unfold interp_rep. Intros.
forward. forward. forward.
Exists (mkist (i_level st) (i_frames st1) (i_cmds st1) (i_result st1) (i_resultp st1)) rc.
unfold interp_rep. cbn [i_level i_frames i_cmds i_result i_resultp].
entailer!.
match goal with H: i_level st1 = _ |- _ => rewrite H end.
replace (i_level st + 1 - 1) with (i_level st) by lia. auto.
Qed.
