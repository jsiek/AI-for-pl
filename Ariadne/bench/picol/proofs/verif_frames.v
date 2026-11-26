(* picolDropCallFrame, picolFreeInterp, picolCallProcFail *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import Picol.picol_full Picol.spec_picol Picol.picol_defs Picol.verif_interp.

Lemma node_free: forall (t: type) (v: reptype t) p,
  (malloc_token Ews (tarray t 1) p * data_at Ews t v p) |--
  (if eq_dec p nullval then emp
   else malloc_token Ews (tarray t 1) p * data_at_ Ews (tarray t 1) p).
Proof.
  intros. destruct (eq_dec p nullval).
  - subst. saturate_local.
    match goal with H: field_compatible _ _ nullval |- _ => destruct H; contradiction end.
  - sep_apply (arr1_free t v p). cancel.
Qed.

Lemma body_picolDropCallFrame: semax_body Vprog Gprog f_picolDropCallFrame picolDropCallFrame_spec.
Proof.
start_function.
unfold frames_rep. rewrite lseg_cons, frame_node_eq. Intros.
forward.
sep_apply (vars_hd (f_vars f) nullval ltac:(simpl; auto)). Intros.
forward.
forward_while (EX V: list varrec,
  PROP ()
  LOCAL (temp _v (hdp v_ptr V nullval); temp _cf (f_ptr f); temp _i i; gvars gv)
  SEP (mem_mgr gv; data_at Ews t_interp (lvl, (f_ptr f, rest)) i;
       malloc_token Ews (tarray t_frame 1) (f_ptr f);
       data_at Ews t_frame (hdp v_ptr (f_vars f) nullval, hdp f_ptr F nullval) (f_ptr f);
       lseg var_node v_ptr V nullval; lseg frame_node f_ptr F nullval))%assert.
- Exists (f_vars f). entailer!.
- destruct V as [|r V]; [entailer! | rewrite lseg_cons, var_node_eq; entailer!].
- destruct V as [|r V]. { simpl hdp in HRE. contradiction HRE; reflexivity. }
  rewrite lseg_cons, var_node_eq. simpl hdp. Intros.
  sep_apply (vars_hd V nullval ltac:(simpl; auto)). Intros.
  forward. forward.
  sep_apply (mstr_free' (v_name r) (v_namep r)).
  forward_call (tarray tschar (Zlength (v_name r) + 1), v_namep r, gv).
  forward.
  sep_apply (mstr_free' (v_val r) (v_valp r)).
  forward_call (tarray tschar (Zlength (v_val r) + 1), v_valp r, gv).
  sep_apply (node_free t_var (v_namep r, (v_valp r, hdp v_ptr V nullval)) (v_ptr r)).
  forward_call (tarray t_var 1, v_ptr r, gv).
  forward.
  Exists V. entailer!.
- destruct V as [|r V].
  2:{ rewrite lseg_cons, var_node_eq. Intros. simpl hdp in HRE.
      assert_PROP (isptr (v_ptr r)) by entailer!. rewrite HRE in *. contradiction. }
  sep_apply (frames_hd F nullval ltac:(simpl; auto)). Intros.
  forward. forward.
  sep_apply (node_free t_frame (hdp v_ptr (f_vars f) nullval, hdp f_ptr F nullval) (f_ptr f)).
  forward_call (tarray t_frame 1, f_ptr f, gv).
  entailer!.
Qed.

Lemma body_picolFreeInterp: semax_body Vprog Gprog f_picolFreeInterp picolFreeInterp_spec.
Proof.
start_function.
unfold interp_rep. Intros.
forward_loop (EX F: list frame, PROP () LOCAL (temp _i i; gvars gv)
   SEP (mem_mgr gv; malloc_token Ews (tarray t_interp 1) i;
        data_at Ews t_interp (Vint (Int.repr (i_level st)), (hdp f_ptr F nullval,
           (hdp c_ptr (i_cmds st) nullval, i_resultp st))) i;
        frames_rep F; cmds_rep (i_cmds st); mstr (i_result st) (i_resultp st)))%assert
 break: (PROP () LOCAL (temp _i i; gvars gv)
   SEP (mem_mgr gv; malloc_token Ews (tarray t_interp 1) i;
        data_at Ews t_interp (Vint (Int.repr (i_level st)), (nullval,
           (hdp c_ptr (i_cmds st) nullval, i_resultp st))) i;
        cmds_rep (i_cmds st); mstr (i_result st) (i_resultp st))).
- Exists (i_frames st). entailer!.
- Intros F. unfold frames_rep.
  sep_apply (frames_hd F nullval ltac:(simpl; auto)). Intros.
  destruct F as [|f F]; simpl hdp in *.
  + forward. forward_if.
    * simpl in *; contradiction.
    * forward. entailer!.
  + forward. forward_if.
    * forward_call (gv, i, Vint (Int.repr (i_level st)), f, F,
                  (hdp c_ptr (i_cmds st) nullval, i_resultp st)).
      Exists F. entailer!.
    * rewrite lseg_cons, frame_node_eq. Intros.
      assert_PROP (isptr (f_ptr f)) by entailer!.
      destruct f; simpl in *; subst; contradiction.
- forward_loop (EX C: list cmdrec, PROP () LOCAL (temp _i i; gvars gv)
   SEP (mem_mgr gv; malloc_token Ews (tarray t_interp 1) i;
        data_at Ews t_interp (Vint (Int.repr (i_level st)), (nullval,
           (hdp c_ptr C nullval, i_resultp st))) i;
        cmds_rep C; mstr (i_result st) (i_resultp st)))%assert
   break: (PROP () LOCAL (temp _i i; gvars gv)
   SEP (mem_mgr gv; malloc_token Ews (tarray t_interp 1) i;
        data_at Ews t_interp (Vint (Int.repr (i_level st)), (nullval,
           (nullval, i_resultp st))) i;
        mstr (i_result st) (i_resultp st))).
  + Exists (i_cmds st). entailer!.
  + Intros C. unfold cmds_rep.
    sep_apply (cmds_hd C nullval ltac:(simpl; auto)). Intros.
    destruct C as [|c C]; simpl hdp in *.
    { forward. forward_if.
      * simpl in *; contradiction.
      * forward. entailer!. }
    forward.
    forward_if.
    * rewrite lseg_cons, cmd_node_eq. simpl hdp. Intros.
      sep_apply (cmds_hd C nullval ltac:(simpl; auto)). Intros.
      forward. forward. forward. forward.
      sep_apply (mstr_free' (c_name c) (c_namep c)).
      forward_call (tarray tschar (Zlength (c_name c) + 1), c_namep c, gv).
      forward.
      sep_apply (ostr_free (c_arg c) (c_argp c)).
      forward_call (tarray tschar (Zlength (match c_arg c with Some s => s | None => [] end) + 1),
                    c_argp c, gv).
      forward.
      sep_apply (ostr_free (c_body c) (c_bodyp c)).
      forward_call (tarray tschar (Zlength (match c_body c with Some s => s | None => [] end) + 1),
                    c_bodyp c, gv).
      sep_apply (node_free t_cmd (c_namep c, (c_func c, (hdp c_ptr C nullval, (c_argp c, c_bodyp c))))
                   (c_ptr c)).
      forward_call (tarray t_cmd 1, c_ptr c, gv).
      Exists C. entailer!.
    * rewrite lseg_cons, cmd_node_eq. Intros.
      assert_PROP (isptr (c_ptr c)) by entailer!.
      destruct c; simpl in *; subst; contradiction.
  + forward.
    sep_apply (mstr_free' (i_result st) (i_resultp st)).
    forward_call (tarray tschar (Zlength (i_result st) + 1), i_resultp st, gv).
    sep_apply (node_free t_interp (Vint (Int.repr (i_level st)), (nullval, (nullval, i_resultp st))) i).
    forward_call (tarray t_interp 1, i, gv).
    entailer!.
Qed.

Lemma body_picolCallProcFail: semax_body Vprog Gprog f_picolCallProcFail picolCallProcFail_spec.
Proof.
start_function.
unfold interp_rep. match goal with Hf: i_frames st = _ |- _ => rewrite Hf end. simpl hdp. Intros.
forward_call (gv, i, Vint (Int.repr (i_level st)), f_ptr f, hdp c_ptr (i_cmds st) nullval,
              i_result st, i_resultp st, sh, s, bp).
Intros q.
unfold obuf.
forward_call (tarray tschar n, tp, gv).
forward_call (gv, i, Vint (Int.repr (i_level st)), f, F, (hdp c_ptr (i_cmds st) nullval, q)).
forward.
Exists q. unfold interp_rep. simpl. entailer!.
Qed.
