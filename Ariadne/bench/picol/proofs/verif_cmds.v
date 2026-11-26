(* picolCommandSet, picolCommandPuts *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import Picol.picol_full Picol.spec_picol Picol.picol_defs Picol.verif_interp
  Picol.verif_cmd_common Picol.verif_retcodes Picol.verif_vars.

Definition var_ctx (F1: list frame) (f: frame) (F2: list frame)
    (V1: list varrec) (r: varrec) (V2: list varrec) : mpred :=
  (lseg frame_node f_ptr F1 (f_ptr f) * lseg frame_node f_ptr F2 nullval *
   malloc_token Ews (tarray t_frame 1) (f_ptr f) *
   data_at Ews t_frame (hdp v_ptr (V1 ++ r :: V2) nullval, hdp f_ptr F2 nullval) (f_ptr f) *
   lseg var_node v_ptr V1 (v_ptr r) * lseg var_node v_ptr V2 nullval *
   malloc_token Ews (tarray t_var 1) (v_ptr r) * mstr (v_name r) (v_namep r))%logic.

Lemma frames_var_focus: forall F1 f F2 V1 r V2, f_vars f = V1 ++ r :: V2 ->
  frames_rep (F1 ++ f :: F2) =
  (var_ctx F1 f F2 V1 r V2 *
   data_at Ews t_var (v_namep r, (v_valp r, hdp v_ptr V2 nullval)) (v_ptr r) *
   malloc_token Ews (tarray tschar (Zlength (v_val r) + 1)) (v_valp r) *
   cstring Ews (v_val r) (v_valp r))%logic.
Proof.
  intros. rewrite frames_split, frame_node_eq, H, lseg_app, lseg_cons, var_node_eq. cbn [hdp].
  unfold var_ctx, mstr. apply pred_ext; cancel.
Qed.

Definition cmd_post (gv: globals) (i: val) (st: istate) (argc: Z) (argv: val)
    (ptrs: list val) (args: list (list byte)) (buf: val) : environ -> mpred :=
  (EX st': istate,
   PROP (cmds_ok gv (i_cmds st'); i_level st' = i_level st;
         Zlength (i_frames st') = Zlength (i_frames st))
   LOCAL (gvars gv; lvar _buf (tarray tschar 1024) buf)
   SEP (mem_mgr gv; G gv; interp_rep i st'; data_at_ Tsh (tarray tschar 1024) buf;
        data_at Ews (tarray (tptr tschar) argc) ptrs argv; args_pred args ptrs))%assert.

Ltac three_args args ptrs :=
  let a0 := fresh "a0" in let a1 := fresh "a1" in let a2 := fresh "a2" in
  let p0 := fresh "p0" in let p1 := fresh "p1" in let p2 := fresh "p2" in
  destruct args as [|a0 [|a1 [|a2 [|? ?]]]]; try solve [exfalso; list_solve];
  destruct ptrs as [|p0 [|p1 [|p2 [|? ?]]]]; try solve [exfalso; list_solve].

Ltac two_args args ptrs :=
  let a0 := fresh "a0" in let a1 := fresh "a1" in
  let p0 := fresh "p0" in let p1 := fresh "p1" in
  destruct args as [|a0 [|a1 [|? ?]]]; try solve [exfalso; list_solve];
  destruct ptrs as [|p0 [|p1 [|? ?]]]; try solve [exfalso; list_solve].

(* the arity-error tail: argv[0] is a cstring, picolArityErr sets the result *)
Ltac arity_tail gv i st args ptrs :=
  sep_apply (args_isptr 0 args ptrs ltac:(lia) ltac:(lia)); Intros;
  forward;
  rewrite (args_focus 0 args ptrs) by lia; Intros;
  forward_call (gv, i, st, Ews, Znth 0 args, Znth 0 ptrs);
  let vret := fresh "vret" in Intros vret; destruct vret as [?s ?q]; simpl fst in *; simpl snd in *;
  sep_apply (derives_refl' _ _ (eq_sym (args_focus 0 args ptrs ltac:(lia) ltac:(lia))));
  forward.

Lemma body_picolCommandSet: semax_body Vprog Gprog f_picolCommandSet picolCommandSet_spec.
Proof.
start_function.
pose proof (args_size_ge args).
assert (Hc: argc = 3 \/ argc = 2 \/ (argc <> 3 /\ argc <> 2)) by lia.
destruct Hc as [Hc|[Hc|[Hc1 Hc2]]].
- subst argc. three_args args ptrs. cbn [args_pred] in *. Intros.
  forward_if (cmd_post gv i st 3 argv [p0; p1; p2] [a0; a1; a2] v_buf).
  2:{ absurd_hyp. }
  { forward. forward.
    unfold G. Intros.
    forward_call (gv, i, st, Ews, a1, p1, Ews, a2, p2).
    Intros st1.
    forward.
    unfold interp_rep at 1. Intros.
    forward_call (gv, i, Vint (Int.repr (i_level st1)), hdp f_ptr (i_frames st1) nullval,
                  hdp c_ptr (i_cmds st1) nullval, i_result st1, i_resultp st1, Ews, a2, p2).
    Intros q.
    unfold cmd_post. Exists (set_res st1 a2 q).
    unfold interp_rep, set_res, G. cbn [i_level i_frames i_cmds i_result i_resultp args_pred].
    entailer!. }
  unfold cmd_post. Intros st'. forward. Exists st' (Int.repr 0). entailer!.
  all: cbn [args_pred]; cancel.
- subst argc. two_args args ptrs. cbn [args_pred] in *. Intros.
  forward_if (cmd_post gv i st 2 argv [p0; p1] [a0; a1] v_buf).
  { absurd_hyp. }
  forward_if.
  2:{ absurd_hyp. }
  forward.
  forward_call (i, st, Ews, a1, p1).
  Intros k.
  forward.
  destruct (find_var_split a1 (f_vars (Znth k (i_frames st))))
    as [[Hn _] | (V1 & r & V2 & HV & Hall & Hnm & Hfind)].
  + rewrite Hn.
    forward_if.
    2:{ absurd_hyp. }
    forward.
    unfold G. Intros. rewrite Gr_GL. Intros.
    take_lit gv lits 11 ___stringlit_13 v___stringlit_13.
    take_lit gv (sublist 0 11 lits ++ sublist (11+1) (Zlength lits) lits) 10
       ___stringlit_12 v___stringlit_12.
    forward_call (Tsh, v_buf, 1024, Ers, litb v___stringlit_13, gv ___stringlit_13, Ews, a1, p1,
                  Ers, litb v___stringlit_12, gv ___stringlit_12).
    Intros s. unfold strbuf. Intros rest.
    rewrite strbuf_split by auto.
    unfold interp_rep. Intros.
    forward_call (gv, i, Vint (Int.repr (i_level st)), hdp f_ptr (i_frames st) nullval,
                  hdp c_ptr (i_cmds st) nullval, i_result st, i_resultp st, Tsh, s, v_buf).
    Intros q.
    sep_apply (derives_refl' _ _ (eq_sym (strbuf_split Tsh s 1024 rest v_buf ltac:(auto) ltac:(auto) ltac:(auto)))).
    give_lit gv (sublist 0 11 lits ++ sublist (11+1) (Zlength lits) lits) 10
       ___stringlit_12 v___stringlit_12.
    give_lit gv lits 11 ___stringlit_13 v___stringlit_13.
    sep_apply (data_at_data_at_ Tsh (tarray tschar 1024)).
    forward.
    Exists (set_res st s q) (Int.repr 1).
    unfold interp_rep, set_res, G. rewrite Gr_GL. cbn [i_level i_frames i_cmds i_result i_resultp args_pred].
    entailer!.
  + rewrite Hfind.
    destruct (split_at (i_frames st) k ltac:(auto)) as (F1 & F2 & HFk & HF1).
    set (f := Znth k (i_frames st)) in *. clearbody f.
    unfold interp_rep. Intros.
    rewrite HFk, (frames_var_focus F1 f F2 V1 r V2 HV). Intros.
    forward_if.
    { nonnull_contra (v_ptr r). }
    forward.
    unfold G. Intros.
    forward_call (gv, i, Vint (Int.repr (i_level st)), hdp f_ptr (F1 ++ f :: F2) nullval,
                  hdp c_ptr (i_cmds st) nullval, i_result st, i_resultp st, Ews, v_val r, v_valp r).
    Intros q.
    unfold cmd_post. Exists (set_res st (v_val r) q).
    unfold interp_rep, set_res, G. cbn [i_level i_frames i_cmds i_result i_resultp args_pred].
    rewrite HFk, (frames_var_focus F1 f F2 V1 r V2 HV).
    entailer!.
  + unfold cmd_post. Intros st'. forward. Exists st' (Int.repr 0). entailer!.
  all: cbn [args_pred]; cancel.
- forward_if (cmd_post gv i st argc argv ptrs args v_buf).
  { absurd_hyp. }
  { forward_if.
    { absurd_hyp. }
    arity_tail gv i st args ptrs.
    Exists (set_res st s q) (Int.repr 1). entailer!. }
  unfold cmd_post. Intros st'. forward. Exists st' (Int.repr 0). entailer!.
  all: cbn [args_pred]; cancel.
Qed.

#[local] Transparent Gs.
Lemma Gs_eq: forall gv, Gs gv =
  (data_at Ers (tptr t_FILE) (gv ___stdin_FILE) (gv _stdin) *
   data_at Ers (tptr t_FILE) (gv ___stdout_FILE) (gv _stdout))%logic.
Proof. reflexivity. Qed.
#[local] Opaque Gs.

Ltac same_pre_if := match goal with |- semax _ ?Pre _ _ => forward_if Pre end.

Ltac puts_out gv p a :=
  forward_call (Ews, p, a, gv ___stdout_FILE, false, gv);
  [ entailer!; unfold std_stream; auto | ].

Lemma body_picolCommandPuts: semax_body Vprog Gprog f_picolCommandPuts picolCommandPuts_spec.
Proof.
start_function.
pose proof (args_size_ge args).
unfold G. Intros. rewrite Gr_GL, Gs_eq. Intros.
assert (Hc: argc = 3 \/ argc = 2 \/ (argc <> 3 /\ argc <> 2)) by lia.
destruct Hc as [Hc|[Hc|[Hc1 Hc2]]].
- subst argc. three_args args ptrs. cbn [args_pred] in *. Intros.
  take_lit gv lits 12 ___stringlit_14 v___stringlit_14.
  forward_if (EX r: int,
    PROP (if Int.eq_dec r Int.zero then a1 = litb v___stringlit_14 else a1 <> litb v___stringlit_14)
    LOCAL (temp _t'1 (Vint (if Int.eq_dec r Int.zero then Int.one else Int.zero));
           temp _i i; temp _argc (Vint (Int.repr 3)); temp _argv argv; gvars gv)
    SEP (mem_mgr gv; Gx gv; interp_rep i st;
         data_at Ers (tptr t_FILE) (gv ___stdin_FILE) (gv _stdin);
         data_at Ers (tptr t_FILE) (gv ___stdout_FILE) (gv _stdout);
         GL gv (sublist 0 12 lits ++ sublist (12 + 1) (Zlength lits) lits);
         cstring Ers (litb v___stringlit_14) (gv ___stringlit_14);
         data_at Ews (tarray (tptr tschar) 3) [p0; p1; p2] argv;
         cstring Ews a0 p0; cstring Ews a1 p1; cstring Ews a2 p2))%assert.
  { forward.
    forward_call (Ews, Ers, p1, a1, gv ___stringlit_14, litb v___stringlit_14).
    Intros r.
    forward.
    Exists r. entailer!.
    destruct (Int.eq_dec r Int.zero) as [E|E].
    - subst r. reflexivity.
    - rewrite Int.eq_false by auto. reflexivity. }
  { absurd_hyp. }
  Intros r.
  forward.
  destruct (Int.eq_dec r Int.zero) as [E|E].
  + forward_if (temp _t'4 (Vint Int.zero)).
    { forward. entailer!. }
    { absurd_hyp. }
    same_pre_if.
    { absurd_hyp. }
    { forward. entailer!. }
    forward_if (temp _t'5 (Vint (Int.repr 2))).
    { forward. entailer!. }
    { absurd_hyp. }
    forward. forward.
    puts_out gv p2 a2.
    same_pre_if.
    { absurd_hyp. }
    { forward. entailer!. }
    forward.
    give_lit gv lits 12 ___stringlit_14 v___stringlit_14.
    Exists st (Int.repr 0). unfold G. rewrite Gr_GL, Gs_eq. cbn [args_pred]. entailer!.
  + forward_if (temp _t'4 (Vint Int.one)).
    { forward. entailer!. }
    { absurd_hyp. }
    forward_if.
    2:{ absurd_hyp. }
    give_lit gv lits 12 ___stringlit_14 v___stringlit_14.
    forward.
    forward_call (gv, i, st, Ews, a0, p0).
    { unfold G. rewrite Gr_GL, Gs_eq. cancel. }
    Intros vret. destruct vret as [s q]. simpl fst in *; simpl snd in *.
    forward.
    Exists (set_res st s q) (Int.repr 1). cbn [args_pred]. entailer!.
- subst argc. two_args args ptrs. cbn [args_pred] in *. Intros.
  forward_if (temp _t'1 (Vint Int.zero)).
  { absurd_hyp. }
  { forward. entailer!. }
  forward.
  forward_if (temp _t'4 (Vint Int.zero)).
  { absurd_hyp. }
  { forward. entailer!. }
  same_pre_if.
  { absurd_hyp. }
  { forward. entailer!. }
  forward_if (temp _t'5 (Vint (Int.repr 1))).
  { absurd_hyp. }
  { forward. entailer!. }
  forward. forward.
  puts_out gv p1 a1.
  same_pre_if.
  { take_lit gv lits 13 ___stringlit_15 v___stringlit_15.
    forward.
    forward_call (Ers, gv ___stringlit_15, litb v___stringlit_15, gv ___stdout_FILE, false, gv).
    { entailer!. unfold std_stream; auto. }
    give_lit gv lits 13 ___stringlit_15 v___stringlit_15.
    entailer!. }
  { absurd_hyp. }
  forward.
  Exists st (Int.repr 0). unfold G. rewrite Gr_GL, Gs_eq. cbn [args_pred]. entailer!.
- forward_if (temp _t'1 (Vint Int.zero)).
  { absurd_hyp. }
  { forward. entailer!. }
  forward.
  forward_if (temp _t'4 (Vint Int.one)).
  { forward. entailer!. }
  { absurd_hyp. }
  forward_if.
  2:{ absurd_hyp. }
  sep_apply (args_isptr 0 args ptrs ltac:(lia) ltac:(lia)). Intros.
  forward.
  rewrite (args_focus 0 args ptrs) by lia. Intros.
  forward_call (gv, i, st, Ews, Znth 0 args, Znth 0 ptrs).
  { unfold G. rewrite Gr_GL, Gs_eq. cancel. }
  Intros vret. destruct vret as [s q]. simpl fst in *; simpl snd in *.
  sep_apply (derives_refl' _ _ (eq_sym (args_focus 0 args ptrs ltac:(lia) ltac:(lia)))).
  forward.
  Exists (set_res st s q) (Int.repr 1). entailer!.
Qed.
