(* picolCommandCallProc *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import Picol.picol_full Picol.spec_picol Picol.picol_defs Picol.verif_util Picol.verif_parse
  Picol.verif_parse3 Picol.verif_interp Picol.verif_cmd_common Picol.verif_retcodes Picol.verif_vars
  Picol.verif_cmds Picol.verif_control Picol.verif_strutil Picol.verif_parse2.

Definition cp_inv (gv: globals) (i: val) (st: istate) (argc: Z) (argv: val) (ptrs: list val)
    (args: list (list byte)) (r: cmdrec) (v_errbuf p0: val) (a: list byte) : environ -> mpred :=
  (EX j: Z, EX pre: list byte, EX arity: Z, EX st1: istate,
   PROP (0 <= j <= Zlength a; Zlength pre = j; 0 <= arity <= argc - 1;
         i_level st1 = i_level st; i_cmds st1 = i_cmds st;
         (Zlength (i_frames st1) = Zlength (i_frames st) + 1)%Z)
   LOCAL (temp _p (offset_val j p0); temp _tofree p0; temp _arity (Vint (Int.repr arity));
          temp _done (Vint (Int.repr 0)); temp _i i; temp _argc (Vint (Int.repr argc));
          temp _argv argv; temp _cmd (c_ptr r); gvars gv; lvar _errbuf (tarray tschar 1024) v_errbuf)
   SEP (mem_mgr gv; Gx gv; Gr gv; interp_rep i st1;
        data_at Ews (tarray (tptr tschar) argc) ptrs argv; args_pred args ptrs;
        data_at_ Tsh (tarray tschar 1024) v_errbuf;
        malloc_token Ews (tarray tschar (Zlength a + 1)) p0;
        data_at Ews (tarray tschar (Zlength a + 1))
          (map Vbyte (pre ++ sublist j (Zlength a + 1) (a ++ [Byte.zero]))) p0))%assert.

Definition cp_brk (gv: globals) (i: val) (st: istate) (argc: Z) (argv: val) (ptrs: list val)
    (args: list (list byte)) (r: cmdrec) (v_errbuf p0: val) (a: list byte) : environ -> mpred :=
  (EX arity: Z, EX st1: istate, EX bytes: list val,
   PROP (0 <= arity <= argc - 1; (Zlength bytes = Zlength a + 1)%Z;
         i_level st1 = i_level st; i_cmds st1 = i_cmds st;
         (Zlength (i_frames st1) = Zlength (i_frames st) + 1)%Z)
   LOCAL (temp _tofree p0; temp _arity (Vint (Int.repr arity));
          temp _i i; temp _argc (Vint (Int.repr argc));
          temp _argv argv; temp _cmd (c_ptr r); gvars gv; lvar _errbuf (tarray tschar 1024) v_errbuf)
   SEP (mem_mgr gv; Gx gv; Gr gv; interp_rep i st1;
        data_at Ews (tarray (tptr tschar) argc) ptrs argv; args_pred args ptrs;
        data_at_ Tsh (tarray tschar 1024) v_errbuf;
        malloc_token Ews (tarray tschar (Zlength a + 1)) p0;
        data_at Ews (tarray tschar (Zlength a + 1)) bytes p0))%assert.

Lemma body_picolCommandCallProc: semax_body Vprog Gprog f_picolCommandCallProc picolCommandCallProc_spec.
Proof.
start_function.
match goal with H: proc_extra _ _ _ |- _ =>
  destruct H as (r & Hr & Hcr & Hfr & a & b & Ha & Hb & Hbl) end.
subst c.
destruct (in_split r (i_cmds st) Hr) as (C1 & C2 & HC).
unfold interp_rep. Intros.
rewrite HC, cmds_split, cmd_node_eq, Ha, Hb. cbn [ostr]. rewrite (mstr_eq a). Intros.
forward.
unfold G. Intros.
forward_call (Ews, a, c_argp r, gv).
Intros p0.
forward_call (existT (fun t => list (reptype t)) t_frame [], nullval, 0, 1, gv).
{ rewrite if_true by auto. cancel. }
{ simpl projT1. change (sizeof t_frame) with 16. rep_lia. }
Intros cf. simpl projT1 in *; simpl projT2 in *. rewrite xr1.
forward. forward. forward.
forward.
unfold frames_rep. sep_apply (frames_hd (i_frames st) nullval ltac:(simpl; auto)). Intros.
forward. forward. forward. forward.
rewrite (mstr_eq a p0). unfold cstring at 2. Intros.
assert_PROP (field_compatible (tarray tschar (Zlength a + 1)) [] p0) by entailer!.
forward_loop (cp_inv gv i st argc argv ptrs args r v_errbuf p0 a)
  break: (cp_brk gv i st argc argv ptrs args r v_errbuf p0 a).
{ unfold cp_inv.
  Exists 0 (@nil byte) 0 (mkist (i_level st) (mkframe cf [] :: i_frames st) (i_cmds st)
                            (i_result st) (i_resultp st)).
  unfold interp_rep, frames_rep.
  cbn [i_level i_frames i_cmds i_result i_resultp lseg hdp f_ptr f_vars].
  rewrite HC, cmds_split, cmd_node_eq, Ha, Hb. cbn [ostr].
  rewrite (mstr_eq a (c_argp r)). unfold frame_node. cbn [f_ptr f_vars lseg hdp].
  rewrite app_nil_l, sublist_same by list_solve.
  entailer!. rewrite Zlength_cons. lia. }
{ unfold cp_inv. Intros j pre arity st1.
  forward. forward.
  forward_loop (EX j2: Z,
    PROP (j <= j2 <= Zlength a)
    LOCAL (temp _p (offset_val j2 p0); temp _start (offset_val j p0); temp _tofree p0;
           temp _arity (Vint (Int.repr arity)); temp _done (Vint (Int.repr 0));
           temp _i i; temp _argc (Vint (Int.repr argc)); temp _argv argv; temp _cmd (c_ptr r);
           gvars gv; lvar _errbuf (tarray tschar 1024) v_errbuf)
    SEP (mem_mgr gv; Gx gv; Gr gv; interp_rep i st1;
         data_at Ews (tarray (tptr tschar) argc) ptrs argv; args_pred args ptrs;
         data_at_ Tsh (tarray tschar 1024) v_errbuf;
         malloc_token Ews (tarray tschar (Zlength a + 1)) p0;
         data_at Ews (tarray tschar (Zlength a + 1))
           (map Vbyte (pre ++ sublist j (Zlength a + 1) (a ++ [Byte.zero]))) p0))%assert
   break: (EX j2: Z,
    PROP (j <= j2 <= Zlength a; j2 = Zlength a \/ (j2 < Zlength a /\ Znth j2 a = Byte.repr 32))
    LOCAL (temp _p (offset_val j2 p0); temp _start (offset_val j p0); temp _tofree p0;
           temp _arity (Vint (Int.repr arity)); temp _done (Vint (Int.repr 0));
           temp _i i; temp _argc (Vint (Int.repr argc)); temp _argv argv; temp _cmd (c_ptr r);
           gvars gv; lvar _errbuf (tarray tschar 1024) v_errbuf)
    SEP (mem_mgr gv; Gx gv; Gr gv; interp_rep i st1;
         data_at Ews (tarray (tptr tschar) argc) ptrs argv; args_pred args ptrs;
         data_at_ Tsh (tarray tschar 1024) v_errbuf;
         malloc_token Ews (tarray tschar (Zlength a + 1)) p0;
         data_at Ews (tarray tschar (Zlength a + 1))
           (map Vbyte (pre ++ sublist j (Zlength a + 1) (a ++ [Byte.zero]))) p0))%assert.
  { Exists j. entailer!. }
  { Intros j2.
    pose proof (arr_field_address (Zlength a + 1) j2 p0 ltac:(lia) ltac:(auto)).
    forward.
    assert (Hc: Znth j2 (pre ++ sublist j (Zlength a + 1) (a ++ [Byte.zero])) = Znth j2 (a ++ [Byte.zero]))
      by list_solve.
    rewrite Hc.
    forward_if (EX b: bool,
      PROP (b = true -> j2 < Zlength a /\ Znth j2 a <> Byte.repr 32;
            b = false -> j2 = Zlength a \/ (j2 < Zlength a /\ Znth j2 a = Byte.repr 32))
      LOCAL (temp _t'3 (bool2val b);
             temp _p (offset_val j2 p0); temp _start (offset_val j p0); temp _tofree p0;
             temp _arity (Vint (Int.repr arity)); temp _done (Vint (Int.repr 0));
             temp _i i; temp _argc (Vint (Int.repr argc)); temp _argv argv; temp _cmd (c_ptr r);
             gvars gv; lvar _errbuf (tarray tschar 1024) v_errbuf)
      SEP (mem_mgr gv; Gx gv; Gr gv; interp_rep i st1;
           data_at Ews (tarray (tptr tschar) argc) ptrs argv; args_pred args ptrs;
           data_at_ Tsh (tarray tschar 1024) v_errbuf;
           malloc_token Ews (tarray tschar (Zlength a + 1)) p0;
           data_at Ews (tarray tschar (Zlength a + 1))
             (map Vbyte (pre ++ sublist j (Zlength a + 1) (a ++ [Byte.zero]))) p0))%assert.
    { forward. forward. rewrite Hc.
      Exists (negb (Int.eq (Int.repr (Byte.signed (Znth j2 (a ++ [Byte.zero])))) (Int.repr 0))).
      entailer!.
      destruct (char_cases a j2 ltac:(lia) ltac:(auto)) as [(Hlt & Heq & Hnz)|(Heq1 & Heq2)].
      - rewrite Heq in *. rewrite (int_eq_byte _ Hnz). simpl. split; intros; [|discriminate].
        split; auto. intro X. rewrite X in *. contradiction.
      - rewrite Heq2 in *. simpl. split; intros; [discriminate | left; auto]. }
    { forward. Exists false. entailer!.
      destruct (char_cases a j2 ltac:(lia) ltac:(auto)) as [(Hlt & Heq & Hnz)|(Heq1 & Heq2)].
      - rewrite Heq in *. right. split; auto. apply byte_of_signed; auto.
      - left; auto. }
    Intros bb.
    forward_if.
    { destruct bb; [|kill_bool]. forward. Exists (j2 + 1). entailer!. }
    { destruct bb; [kill_bool|]. forward. Exists j2. entailer!. } }
  Intros j2.
  match goal with H: j2 = Zlength a \/ _ |- _ => rename H into Hbrk end.
  pose proof (arr_field_address (Zlength a + 1) j2 p0 ltac:(lia) ltac:(auto)).
  forward.
  assert (Hc: Znth j2 (pre ++ sublist j (Zlength a + 1) (a ++ [Byte.zero])) = Znth j2 (a ++ [Byte.zero]))
    by list_solve.
  rewrite Hc.
  forward_if (EX bb: bool,
    PROP (bb = true -> j2 < Zlength a /\ j2 = j; bb = false -> j2 = Zlength a \/ j2 <> j)
    LOCAL (temp _t'4 (bool2val bb); temp _p (offset_val j2 p0); temp _start (offset_val j p0); temp _tofree p0;
           temp _arity (Vint (Int.repr arity)); temp _done (Vint (Int.repr 0));
           temp _i i; temp _argc (Vint (Int.repr argc)); temp _argv argv; temp _cmd (c_ptr r);
           gvars gv; lvar _errbuf (tarray tschar 1024) v_errbuf)
    SEP (mem_mgr gv; Gx gv; Gr gv; interp_rep i st1;
         data_at Ews (tarray (tptr tschar) argc) ptrs argv; args_pred args ptrs;
         data_at_ Tsh (tarray tschar 1024) v_errbuf;
         malloc_token Ews (tarray tschar (Zlength a + 1)) p0;
         data_at Ews (tarray tschar (Zlength a + 1))
           (map Vbyte (pre ++ sublist j (Zlength a + 1) (a ++ [Byte.zero]))) p0))%assert.
  { forward.
    { entailer!. apply denote_tc_test_eq_split; apply sepcon_valid_pointer2;
      apply arr_valid; auto; try lia; list_solve. }
    rewrite (ptr_cmp_eq p0 j2 j (Zlength a + 1)) by (auto; lia).
    Exists (Z.eqb j2 j). entailer!.
    destruct (char_cases a j2 ltac:(lia) ltac:(auto)) as [(Hlt & Heq & Hnz)|(Heq1 & Heq2)].
    - all: repeat match goal with
               | H: (_ =? _) = true |- _ => apply Z.eqb_eq in H
               | H: (_ =? _) = false |- _ => apply Z.eqb_neq in H end;
        try split; try lia; auto.
    - rewrite Heq2 in *. exfalso. congruence. }
  { forward. Exists false. entailer!.
    destruct (char_cases a j2 ltac:(lia) ltac:(auto)) as [(Hlt & Heq & Hnz)|(Heq1 & Heq2)].
    - rewrite Heq in *. exfalso. congruence.
    - left; auto. }
  Intros bb.
  forward_if (PROP (bb = false)
    LOCAL (temp _p (offset_val j2 p0); temp _start (offset_val j p0); temp _tofree p0;
           temp _arity (Vint (Int.repr arity)); temp _done (Vint (Int.repr 0));
           temp _i i; temp _argc (Vint (Int.repr argc)); temp _argv argv; temp _cmd (c_ptr r);
           gvars gv; lvar _errbuf (tarray tschar 1024) v_errbuf)
    SEP (mem_mgr gv; Gx gv; Gr gv; interp_rep i st1;
         data_at Ews (tarray (tptr tschar) argc) ptrs argv; args_pred args ptrs;
         data_at_ Tsh (tarray tschar 1024) v_errbuf;
         malloc_token Ews (tarray tschar (Zlength a + 1)) p0;
         data_at Ews (tarray tschar (Zlength a + 1))
           (map Vbyte (pre ++ sublist j (Zlength a + 1) (a ++ [Byte.zero]))) p0))%assert.
  { destruct bb; [|kill_bool].
    assert (Hlt: j2 < Zlength a /\ j2 = j)
      by (repeat match goal with H: true = true -> _ |- _ => specialize (H eq_refl) end; tauto).
    destruct Hlt as [Hlt Hjj]. subst j2.
    forward. forward.
    unfold cp_inv. Exists (j + 1) (pre ++ [Znth j a]) arity st1. entailer!.
    - list_solve.
    - apply derives_refl'. do 2 f_equal. list_solve. }
  { forward. destruct bb; [kill_bool|]. entailer!. }
  Intros.
  forward_if.
  { entailer!. apply denote_tc_test_eq_split; apply sepcon_valid_pointer2;
      apply arr_valid; auto; try lia; list_solve. }
  { forward. unfold cp_brk.
    Exists arity st1 (map Vbyte (pre ++ sublist j (Zlength a + 1) (a ++ [Byte.zero]))).
    entailer!. }
  forward.
  rewrite Hc.
  forward_if (EX dn: Z,
    PROP ((dn = 1 /\ j2 = Zlength a) \/ (dn = 0 /\ j2 < Zlength a))
    LOCAL (temp _done (Vint (Int.repr dn)); temp _p (offset_val j2 p0); temp _start (offset_val j p0);
           temp _tofree p0; temp _arity (Vint (Int.repr arity));
           temp _i i; temp _argc (Vint (Int.repr argc)); temp _argv argv; temp _cmd (c_ptr r);
           gvars gv; lvar _errbuf (tarray tschar 1024) v_errbuf)
    SEP (mem_mgr gv; Gx gv; Gr gv; interp_rep i st1;
         data_at Ews (tarray (tptr tschar) argc) ptrs argv; args_pred args ptrs;
         data_at_ Tsh (tarray tschar 1024) v_errbuf;
         malloc_token Ews (tarray tschar (Zlength a + 1)) p0;
         data_at Ews (tarray tschar (Zlength a + 1))
           (map Vbyte (pre ++ sublist j j2 a ++ [Byte.zero] ++
                       sublist (j2 + 1) (Zlength a + 1) (a ++ [Byte.zero]))) p0))%assert.
  { forward. Exists 1.
    destruct (char_cases a j2 ltac:(lia) ltac:(auto)) as [(Hlt & Heq & Hnz)|(Heq1 & Heq2)].
    - rewrite Heq in *. exfalso. congruence.
    - subst j2. entailer!. all: try (left; split; auto; fail).
      all: try (apply derives_refl'; do 2 f_equal; list_solve). }
  { forward. Exists 0.
    destruct (char_cases a j2 ltac:(lia) ltac:(auto)) as [(Hlt & Heq & Hnz)|(Heq1 & Heq2)].
    - entailer!. all: try (right; split; auto; fail).
      all: try (unfold data_at; apply derives_refl'; change (Vint (Int.repr 0)) with (Vbyte Byte.zero);
                f_equal; list_solve).
    - rewrite Heq2 in *. exfalso. congruence. }
  Intros dn.
  assert (HFn: exists f F, i_frames st1 = f :: F /\ F <> []).
  { destruct (i_frames st1) as [|f F] eqn:HF.
    - rewrite Zlength_nil in *. pose proof (Zlength_nonneg (i_frames st)). lia.
    - exists f, F. split; auto. intro X. subst F. rewrite Zlength_cons, Zlength_nil in *.
      destruct (i_frames st); [contradiction|]. rewrite Zlength_cons in *.
      pose proof (Zlength_nonneg l). lia. }
  destruct HFn as (f & F & HF & HFn).
  assert (HFl: Zlength F = Zlength (i_frames st))
    by (rewrite HF, Zlength_cons in *; lia).
  pose proof (args_size_ge args).
  assert (arity + 1 <= Int.max_signed) by rep_lia.
  forward.
  rewrite add_repr.
  forward.
  forward_if (PROP (arity + 1 <= argc - 1)
    LOCAL (temp _arity (Vint (Int.repr (arity + 1))); temp _done (Vint (Int.repr dn));
           temp _p (offset_val j2 p0); temp _start (offset_val j p0);
           temp _tofree p0; temp _i i; temp _argc (Vint (Int.repr argc)); temp _argv argv;
           temp _cmd (c_ptr r); gvars gv; lvar _errbuf (tarray tschar 1024) v_errbuf)
    SEP (mem_mgr gv; Gx gv; Gr gv; interp_rep i st1;
         data_at Ews (tarray (tptr tschar) argc) ptrs argv; args_pred args ptrs;
         data_at_ Tsh (tarray tschar 1024) v_errbuf;
         malloc_token Ews (tarray tschar (Zlength a + 1)) p0;
         data_at Ews (tarray tschar (Zlength a + 1))
           (map Vbyte (pre ++ sublist j j2 a ++ [Byte.zero] ++
                       sublist (j2 + 1) (Zlength a + 1) (a ++ [Byte.zero]))) p0))%assert.
  { sep_apply (args_isptr 0 args ptrs ltac:(lia) ltac:(lia)). Intros.
    forward.
    rewrite (args_focus 0 args ptrs) by lia. Intros.
    rewrite Gr_GL. Intros.
    take_lit gv lits 19 ___stringlit_21 v___stringlit_21.
    take_lit gv (sublist 0 19 lits ++ sublist (19+1) (Zlength lits) lits) 18 ___stringlit_20 v___stringlit_20.
    forward_call (Tsh, v_errbuf, 1024, Ers, litb v___stringlit_21, gv ___stringlit_21, Ews,
                  Znth 0 args, Znth 0 ptrs, Ers, litb v___stringlit_20, gv ___stringlit_20).
    Intros s. unfold strbuf. Intros rest. rewrite strbuf_split by auto. Intros.
    assert_PROP (isptr p0) by entailer!.
    sep_apply (to_obuf (Zlength a + 1) p0 (map Vbyte (pre ++ sublist j j2 a ++ [Byte.zero] ++
                       sublist (j2 + 1) (Zlength a + 1) (a ++ [Byte.zero]))) ltac:(auto)).
    forward_call (gv, i, st1, f, F, Tsh, s, v_errbuf, p0, Zlength a + 1).
    Intros q.
    sep_apply (derives_refl' _ _ (eq_sym (strbuf_split Tsh s 1024 rest v_errbuf ltac:(auto) ltac:(auto) ltac:(auto)))).
    give_lit gv (sublist 0 19 lits ++ sublist (19+1) (Zlength lits) lits) 18 ___stringlit_20 v___stringlit_20.
    give_lit gv lits 19 ___stringlit_21 v___stringlit_21.
    sep_apply (derives_refl' _ _ (eq_sym (args_focus 0 args ptrs ltac:(lia) ltac:(lia)))).
    sep_apply (data_at_data_at_ Tsh (tarray tschar 1024)).
    forward.
    Exists (mkist (i_level st1) F (i_cmds st1) s q) (Int.repr 1).
    unfold G. rewrite Gr_GL. entailer!. simpl. rewrite H14. auto. }
  { forward. entailer!. }
  Intros.
  pose proof (arr_field_address (Zlength a + 1) j p0 ltac:(lia) ltac:(auto)).
  assert (Hnz: ~ In Byte.zero (sublist j j2 a)) by (intro X; apply sublist_In in X; contradiction).
  assert (Hnz': ~ In Byte.zero (sublist (Zlength pre) j2 a)) by (rewrite H11; auto).
  assert_PROP (isptr p0) by entailer!.
  assert (force_val (sem_add_ptr_int tschar Signed (offset_val j p0) (Vint (Int.repr 0))) =
          field_address (tarray tschar (Zlength a + 1)) (SUB j) p0)
    by (rewrite add0_ptr by auto; auto).
  forward. forward.
  forward_if (PROP ()
    LOCAL (temp _arity (Vint (Int.repr (arity + 1))); temp _done (Vint (Int.repr dn));
           temp _p (offset_val j2 p0); temp _start (offset_val j p0);
           temp _tofree p0; temp _i i; temp _argc (Vint (Int.repr argc)); temp _argv argv;
           temp _cmd (c_ptr r); gvars gv; lvar _errbuf (tarray tschar 1024) v_errbuf)
    SEP (mem_mgr gv; Gx gv; Gr gv; interp_rep i st1;
         data_at Ews (tarray (tptr tschar) argc) ptrs argv; args_pred args ptrs;
         data_at_ Tsh (tarray tschar 1024) v_errbuf;
         malloc_token Ews (tarray tschar (Zlength a + 1)) p0;
         data_at Ews (tarray tschar (Zlength a + 1))
           (map Vbyte (pre ++ sublist j j2 a ++ [Byte.zero] ++
                       sublist (j2 + 1) (Zlength a + 1) (a ++ [Byte.zero]))) p0))%assert.
  { rewrite Gr_GL. Intros.
    take_lit gv lits 21 ___stringlit_23 v___stringlit_23.
    take_lit gv (sublist 0 21 lits ++ sublist (21+1) (Zlength lits) lits) 20 ___stringlit_22 v___stringlit_22.
    rewrite (buf3 pre (sublist j j2 a) (sublist (j2 + 1) (Zlength a + 1) (a ++ [Byte.zero]))
               (Zlength a + 1) p0) by (auto; list_solve).
    Intros. rewrite H11.
    forward_call (Tsh, v_errbuf, 1024, Ers, litb v___stringlit_23, gv ___stringlit_23, Ews,
                  sublist j j2 a, offset_val j p0, Ers, litb v___stringlit_22, gv ___stringlit_22).
    Intros s. unfold strbuf. Intros rest. rewrite strbuf_split by auto. Intros.
    rewrite <- H11.
    sep_apply (derives_refl' _ _ (eq_sym (buf3 pre (sublist (Zlength pre) j2 a)
       (sublist (j2 + 1) (Zlength a + 1) (a ++ [Byte.zero])) (Zlength a + 1) p0
       ltac:(list_solve) ltac:(auto) ltac:(auto)))).
    assert_PROP (isptr p0) by entailer!.
    sep_apply (to_obuf (Zlength a + 1) p0 (map Vbyte (pre ++ sublist (Zlength pre) j2 a ++ [Byte.zero] ++
                       sublist (j2 + 1) (Zlength a + 1) (a ++ [Byte.zero]))) ltac:(auto)).
    forward_call (gv, i, st1, f, F, Tsh, s, v_errbuf, p0, Zlength a + 1).
    Intros q.
    sep_apply (derives_refl' _ _ (eq_sym (strbuf_split Tsh s 1024 rest v_errbuf ltac:(auto) ltac:(auto) ltac:(auto)))).
    give_lit gv (sublist 0 21 lits ++ sublist (21+1) (Zlength lits) lits) 20 ___stringlit_22 v___stringlit_22.
    give_lit gv lits 21 ___stringlit_23 v___stringlit_23.
    sep_apply (data_at_data_at_ Tsh (tarray tschar 1024)).
    forward.
    Exists (mkist (i_level st1) F (i_cmds st1) s q) (Int.repr 1).
    unfold G. rewrite Gr_GL. entailer!. simpl. rewrite H14. auto. }
  { forward. entailer!. }
  sep_apply (args_isptr (arity + 1) args ptrs ltac:(lia) ltac:(lia)). Intros.
  forward.
  rewrite (args_focus (arity + 1) args ptrs) by lia. Intros.
  rewrite (buf3 pre (sublist j j2 a) (sublist (j2 + 1) (Zlength a + 1) (a ++ [Byte.zero]))
             (Zlength a + 1) p0) by (auto; list_solve).
  Intros. rewrite H11.
  forward_call (gv, i, st1, Ews, sublist j j2 a, offset_val j p0, Ews,
                Znth (arity + 1) args, Znth (arity + 1) ptrs).
  Intros st2.
  rewrite <- H11.
  sep_apply (derives_refl' _ _ (eq_sym (buf3 pre (sublist (Zlength pre) j2 a)
     (sublist (j2 + 1) (Zlength a + 1) (a ++ [Byte.zero])) (Zlength a + 1) p0
     ltac:(list_solve) ltac:(auto) ltac:(auto)))).
  sep_apply (derives_refl' _ _ (eq_sym (args_focus (arity + 1) args ptrs ltac:(lia) ltac:(lia)))).
  forward.
  forward_if.
  { forward. unfold cp_brk.
    Exists (arity + 1) st2 (map Vbyte (pre ++ sublist (Zlength pre) j2 a ++ [Byte.zero] ++
                       sublist (j2 + 1) (Zlength a + 1) (a ++ [Byte.zero]))).
    entailer!. }
  { destruct H22 as [[Hd Hj]|[Hd Hj]]; subst dn; [absurd_hyp|].
    forward. unfold cp_inv.
    Exists (j2 + 1) (pre ++ sublist (Zlength pre) j2 a ++ [Byte.zero]) (arity + 1) st2.
    entailer!.
    - repeat split; try lia; try list_solve; auto.
    - apply derives_refl'. do 2 f_equal. list_solve. } }
unfold cp_brk. Intros arity st1 bytes.
match goal with H: i_cmds st1 = i_cmds st |- _ => rename H into Hcm end.
match goal with H: i_level st1 = i_level st |- _ => rename H into Hlv end.
assert (HFn: exists f F, i_frames st1 = f :: F /\ F <> []).
{ destruct (i_frames st1) as [|f F] eqn:HF.
  - rewrite Zlength_nil in *. pose proof (Zlength_nonneg (i_frames st)). lia.
  - exists f, F. split; auto. intro X. subst F. rewrite Zlength_cons, Zlength_nil in *.
    destruct (i_frames st); [contradiction|]. rewrite Zlength_cons in *.
    pose proof (Zlength_nonneg l). lia. }
destruct HFn as (f & F & HF & HFn).
assert (HFl: Zlength F = Zlength (i_frames st)) by (rewrite HF, Zlength_cons in *; lia).
assert_PROP (isptr p0) by entailer!.
forward_call (tarray tschar (Zlength a + 1), p0, gv).
{ rewrite if_false by (intro; subst; contradiction). cancel. }
forward.
change (Vlong (Int64.repr (Int.signed (Int.repr 0)))) with nullval.
pose proof (args_size_ge args).
forward_if (PROP (arity = argc - 1)
  LOCAL (temp _tofree nullval; temp _arity (Vint (Int.repr arity));
         temp _i i; temp _argc (Vint (Int.repr argc));
         temp _argv argv; temp _cmd (c_ptr r); gvars gv; lvar _errbuf (tarray tschar 1024) v_errbuf)
  SEP (mem_mgr gv; Gx gv; Gr gv; interp_rep i st1;
       data_at Ews (tarray (tptr tschar) argc) ptrs argv; args_pred args ptrs;
       data_at_ Tsh (tarray tschar 1024) v_errbuf))%assert.
{ sep_apply (args_isptr 0 args ptrs ltac:(lia) ltac:(lia)). Intros.
  forward.
  rewrite (args_focus 0 args ptrs) by lia. Intros.
  rewrite Gr_GL. Intros.
  take_lit gv lits 19 ___stringlit_21 v___stringlit_21.
  take_lit gv (sublist 0 19 lits ++ sublist (19+1) (Zlength lits) lits) 18 ___stringlit_20 v___stringlit_20.
  forward_call (Tsh, v_errbuf, 1024, Ers, litb v___stringlit_21, gv ___stringlit_21, Ews,
                Znth 0 args, Znth 0 ptrs, Ers, litb v___stringlit_20, gv ___stringlit_20).
  Intros s. unfold strbuf. Intros rest. rewrite strbuf_split by auto. Intros.
  sep_apply (obuf_null' (Zlength a + 1) (mem_mgr gv)).
  Intros.
  forward_call (gv, i, st1, f, F, Tsh, s, v_errbuf, nullval, Zlength a + 1).
  Intros q.
  sep_apply (derives_refl' _ _ (eq_sym (strbuf_split Tsh s 1024 rest v_errbuf ltac:(auto) ltac:(auto) ltac:(auto)))).
  give_lit gv (sublist 0 19 lits ++ sublist (19+1) (Zlength lits) lits) 18 ___stringlit_20 v___stringlit_20.
  give_lit gv lits 19 ___stringlit_21 v___stringlit_21.
  sep_apply (derives_refl' _ _ (eq_sym (args_focus 0 args ptrs ltac:(lia) ltac:(lia)))).
  sep_apply (data_at_data_at_ Tsh (tarray tschar 1024)).
  forward.
  Exists (mkist (i_level st1) F (i_cmds st1) s q) (Int.repr 1).
  unfold G. rewrite Gr_GL. entailer!. simpl. rewrite Hcm. auto. }
{ forward. entailer!. all: try lia.
  all: first [
    match goal with H: Int.repr _ = Int.sub _ _ |- _ =>
      rewrite sub_repr in H; apply repr_inj_signed in H; [lia|rep_lia|rep_lia] end
  | match goal with H: Int.repr _ = Int.repr _ |- _ =>
      apply repr_inj_signed in H; [lia|rep_lia|rep_lia] end
  | match goal with H: Int.eq _ _ = true |- _ =>
      apply Int.same_if_eq in H; rewrite ?sub_repr in H;
      apply repr_inj_signed in H; [lia|rep_lia|rep_lia] end ]. }
Intros.
unfold interp_rep at 1. Intros.
rewrite Hcm, HC, cmds_split, cmd_node_eq, Ha, Hb. cbn [ostr]. rewrite (mstr_eq b). Intros.
forward.
forward_call (Ews, b, c_bodyp r, gv).
Intros bq.
sep_apply (derives_refl' _ _ (eq_sym (mstr_eq b (c_bodyp r)))).
replace (mstr b (c_bodyp r)) with (ostr (c_body r) (c_bodyp r)) by (rewrite Hb; reflexivity).
replace (mstr a (c_argp r)) with (ostr (c_arg r) (c_argp r)) by (rewrite Ha; reflexivity).
sep_apply (derives_refl' _ _ (eq_sym (cmd_node_eq r (hdp c_ptr C2 nullval)))).
sep_apply (derives_refl' _ _ (eq_sym (cmds_split C1 r C2))).
rewrite <- HC, <- Hcm.
sep_apply (interp_refold i st1 ltac:(auto) ltac:(auto)).
sep_apply (G_fold gv).
forward.
rewrite (mstr_eq b bq). Intros.
forward_call (gv, i, st1, Ews, b, bq).
all: try (rewrite Hcm; assumption).
Intros vret. destruct vret as [st2 rc]. simpl fst in *; simpl snd in *.
sep_apply (derives_refl' _ _ (eq_sym (mstr_eq b bq))).
sep_apply (mstr_free b bq). Intros.
forward_call (tarray tschar (Zlength b + 1), bq, gv).
{ rewrite if_false by (intro; subst; contradiction). cancel. }
forward_if (EX rc2: int,
  PROP ()
  LOCAL (temp _errcode (Vint rc2); temp _i i; gvars gv; lvar _errbuf (tarray tschar 1024) v_errbuf)
  SEP (mem_mgr gv; G gv; interp_rep i st2;
       data_at Ews (tarray (tptr tschar) argc) ptrs argv; args_pred args ptrs;
       data_at_ Tsh (tarray tschar 1024) v_errbuf))%assert.
{ forward. Exists (Int.repr 0). entailer!. }
{ forward. Exists rc. entailer!. }
Intros rc2.
assert (HFn2: exists f2 F2, i_frames st2 = f2 :: F2 /\ F2 <> [] /\ Zlength F2 = Zlength (i_frames st)).
{ destruct (i_frames st2) as [|f2 F2] eqn:HF2.
  - rewrite Zlength_nil in *. pose proof (Zlength_nonneg (i_frames st)). lia.
  - exists f2, F2. rewrite Zlength_cons in *. split; auto. split; [|lia].
    intro X. subst F2. rewrite Zlength_nil in *.
    destruct (i_frames st); [contradiction|]. rewrite Zlength_cons in *.
    pose proof (Zlength_nonneg l). lia. }
destruct HFn2 as (f2 & F2 & HF2 & HF2n & HF2l).
unfold interp_rep at 1. Intros. rewrite HF2. cbn [hdp].
forward_call (gv, i, Vint (Int.repr (i_level st2)), f2, F2,
              (hdp c_ptr (i_cmds st2) nullval, i_resultp st2)).
forward.
Exists (mkist (i_level st2) F2 (i_cmds st2) (i_result st2) (i_resultp st2)) rc2.
unfold interp_rep. entailer!.
all: simpl; try cancel; try congruence.
Qed.
