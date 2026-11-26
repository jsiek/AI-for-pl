Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import Picol.picol_full Picol.spec_picol Picol.picol_defs.

Lemma xr1: forall (t: type) p,
  data_at Ews (tarray t 1) (sublist 0 (Z.min 0 1) [] ++ Zrepeat (default_val t) (1 - Z.min 0 1)) p
  = data_at_ Ews t p.
Proof.
  intros. unfold data_at_, field_at_. fold (data_at Ews t (default_val t) p).
  apply data_at_singleton_array_eq. reflexivity.
Qed.

Lemma arr1_free: forall (t: type) v p,
  data_at Ews t v p |-- data_at_ Ews (tarray t 1) p.
Proof.
  intros. rewrite <- (data_at_singleton_array_eq Ews t v [v] p) by reflexivity.
  apply data_at_data_at_.
Qed.

Lemma mstr_free: forall s p,
  mstr s p |-- !! (isptr p) && (malloc_token Ews (tarray tschar (Zlength s + 1)) p *
                     data_at_ Ews (tarray tschar (Zlength s + 1)) p).
Proof.
  intros. unfold mstr, cstring. entailer!.
Qed.

Lemma mstr_free': forall s p,
  mstr s p |-- (if eq_dec p nullval then emp else
               malloc_token Ews (tarray tschar (Zlength s + 1)) p *
               data_at_ Ews (tarray tschar (Zlength s + 1)) p).
Proof.
  intros. sep_apply mstr_free. Intros. rewrite if_false. auto.
  intro; subst; contradiction.
Qed.

Lemma ostr_free: forall o p,
  ostr o p |-- (if eq_dec p nullval then emp else
               malloc_token Ews (tarray tschar (Zlength (match o with Some s => s | None => [] end) + 1)) p *
               data_at_ Ews (tarray tschar (Zlength (match o with Some s => s | None => [] end) + 1)) p).
Proof.
  intros. destruct o; simpl.
  - apply mstr_free'.
  - entailer!; rewrite if_true; auto.
Qed.

Lemma mstr_local_facts: forall s p, mstr s p |-- !! isptr p.
Proof. intros. unfold mstr, cstring. entailer!. Qed.

Lemma ostr_local_facts: forall o p, ostr o p |-- !! is_pointer_or_null p.
Proof. intros. destruct o; simpl; [unfold mstr, cstring|]; entailer!. Qed.

Lemma mstr_valid_pointer: forall s p, mstr s p |-- valid_pointer p.
Proof. intros. unfold mstr. apply sepcon_valid_pointer2. apply cstring_valid_pointer. apply readable_nonidentity. auto. Qed.

#[export] Hint Resolve mstr_local_facts ostr_local_facts : saturate_local.
#[export] Hint Resolve mstr_valid_pointer : valid_pointer.

Lemma find_cmd_app:forall nm C1 C2,
  Forall (fun c => c_name c <> nm) C1 -> find_cmd nm (C1 ++ C2) = find_cmd nm C2.
Proof.
  induction C1; intros; simpl; auto. inv H.
  destruct (list_eq_dec Byte.eq_dec (c_name a) nm); [contradiction|]. auto.
Qed.

Lemma lseg_snoc: forall {A} node (ptr: A -> val) l a tail,
  lseg node ptr (l ++ [a]) tail = (lseg node ptr l (ptr a) * node a tail)%logic.
Proof.
  intros. rewrite lseg_app. simpl. rewrite sepcon_emp. auto.
Qed.

Lemma cmd_node_eq: forall c nxt, cmd_node c nxt =
  (malloc_token Ews (tarray t_cmd 1) (c_ptr c) *
  data_at Ews t_cmd (c_namep c, (c_func c, (nxt, (c_argp c, c_bodyp c)))) (c_ptr c) *
  mstr (c_name c) (c_namep c) * ostr (c_arg c) (c_argp c) * ostr (c_body c) (c_bodyp c))%logic.
Proof. reflexivity. Qed.

Lemma var_node_eq: forall r nxt, var_node r nxt =
  (malloc_token Ews (tarray t_var 1) (v_ptr r) *
  data_at Ews t_var (v_namep r, (v_valp r, nxt)) (v_ptr r) *
  mstr (v_name r) (v_namep r) * mstr (v_val r) (v_valp r))%logic.
Proof. reflexivity. Qed.

Lemma frame_node_eq: forall f parent, frame_node f parent =
  (malloc_token Ews (tarray t_frame 1) (f_ptr f) *
  data_at Ews t_frame (hdp v_ptr (f_vars f) nullval, parent) (f_ptr f) *
  lseg var_node v_ptr (f_vars f) nullval)%logic.
Proof. reflexivity. Qed.

Lemma mstr_eq: forall s p, mstr s p =
  (malloc_token Ews (tarray tschar (Zlength s + 1)) p * cstring Ews s p)%logic.
Proof. reflexivity. Qed.

Lemma lseg_cons: forall {A} node (ptr: A -> val) a l t,
  lseg node ptr (a :: l) t = (node a (hdp ptr l t) * lseg node ptr l t)%logic.
Proof. reflexivity. Qed.

Ltac rw_cmds := match goal with Hc: i_cmds _ = _ |- _ => rewrite Hc end.

Lemma cmds_hd: forall C t, is_pointer_or_null t ->
  lseg cmd_node c_ptr C t |-- !! is_pointer_or_null (hdp c_ptr C t).
Proof. intros. destruct C; simpl. entailer!. unfold cmd_node. entailer!. Qed.

Lemma frames_hd: forall F t, is_pointer_or_null t ->
  lseg frame_node f_ptr F t |-- !! is_pointer_or_null (hdp f_ptr F t).
Proof. intros. destruct F; simpl. entailer!. unfold frame_node. entailer!. Qed.

Lemma vars_hd: forall V t, is_pointer_or_null t ->
  lseg var_node v_ptr V t |-- !! is_pointer_or_null (hdp v_ptr V t).
Proof. intros. destruct V; simpl. entailer!. unfold var_node. entailer!. Qed.

Lemma frames_valid: forall f F t, lseg frame_node f_ptr (f :: F) t |-- valid_pointer (f_ptr f).
Proof.
  intros. rewrite lseg_cons, frame_node_eq.
  apply sepcon_valid_pointer1. apply sepcon_valid_pointer1. apply sepcon_valid_pointer2.
  apply data_at_valid_ptr; [apply readable_nonidentity; auto | simpl; rep_lia].
Qed.

Lemma cmds_valid: forall c C t, lseg cmd_node c_ptr (c :: C) t |-- valid_pointer (c_ptr c).
Proof.
  intros. rewrite lseg_cons, cmd_node_eq.
  apply sepcon_valid_pointer1. apply sepcon_valid_pointer1. apply sepcon_valid_pointer1.
  apply sepcon_valid_pointer1. apply sepcon_valid_pointer2.
  apply data_at_valid_ptr; [apply readable_nonidentity; auto | simpl; rep_lia].
Qed.

Lemma vars_valid: forall r V t, lseg var_node v_ptr (r :: V) t |-- valid_pointer (v_ptr r).
Proof.
  intros. rewrite lseg_cons, var_node_eq.
  apply sepcon_valid_pointer1. apply sepcon_valid_pointer1. apply sepcon_valid_pointer1.
  apply sepcon_valid_pointer2.
  apply data_at_valid_ptr; [apply readable_nonidentity; auto | simpl; rep_lia].
Qed.

#[export] Hint Resolve frames_valid cmds_valid vars_valid : valid_pointer.

Lemma body_picolInitInterp: semax_body Vprog Gprog f_picolInitInterp picolInitInterp_spec.
Proof.
start_function.
unfold G. Intros.
forward_call (existT (fun t => list (reptype t)) t_interp [], nullval, 0, 1, gv).
{ rewrite if_true by auto. cancel. }
{ simpl projT1. change (sizeof t_interp) with 32. rep_lia. }
Intros i. simpl projT1 in *; simpl projT2 in *. rewrite xr1.
forward.
forward_call (existT (fun t => list (reptype t)) t_frame [], nullval, 0, 1, gv).
{ rewrite if_true by auto. cancel. }
{ simpl projT1. change (sizeof t_frame) with 16. rep_lia. }
Intros cf. simpl projT1 in *; simpl projT2 in *. rewrite xr1.
forward.
unfold Gr, lit. Intros.
forward_call (Ers, litb v___stringlit_2, gv ___stringlit_2, gv).
Intros rp.
forward. forward. forward. forward. forward. forward. forward.
Exists i (mkist 0 [mkframe cf []] [] (litb v___stringlit_2) rp).
unfold interp_rep, frames_rep, cmds_rep, G, Gr, lit. simpl. unfold frame_node. simpl.
entailer!.
Qed.

Lemma body_picolSetResult: semax_body Vprog Gprog f_picolSetResult picolSetResult_spec.
Proof.
start_function.
sep_apply (mstr_free r rp). Intros.
forward.
forward_call (tarray tschar (Zlength r + 1), rp, gv).
{ rewrite if_false by (intro; subst; contradiction). cancel. }
forward_call (sh, s, sp, gv).
Intros q.
forward.
Exists q. entailer!.
Qed.

Lemma body_picolGetCommand: semax_body Vprog Gprog f_picolGetCommand picolGetCommand_spec.
Proof.
start_function.
unfold interp_rep, cmds_rep. Intros.
sep_apply (cmds_hd (i_cmds st) nullval ltac:(simpl; auto)). Intros.
forward.
forward_while (EX C1: list cmdrec, EX C2: list cmdrec,
  PROP (i_cmds st = C1 ++ C2; Forall (fun c => c_name c <> nm) C1)
  LOCAL (temp _c (hdp c_ptr C2 nullval); temp _i i; temp _name np)
  SEP (malloc_token Ews (tarray t_interp 1) i;
       data_at Ews t_interp (Vint (Int.repr (i_level st)),
         (hdp f_ptr (i_frames st) nullval, (hdp c_ptr (i_cmds st) nullval, i_resultp st))) i;
       frames_rep (i_frames st);
       lseg cmd_node c_ptr C1 (hdp c_ptr C2 nullval); lseg cmd_node c_ptr C2 nullval;
       mstr (i_result st) (i_resultp st); cstring sh nm np))%assert.
- Exists (@nil cmdrec) (i_cmds st). entailer!.
- destruct C2 as [|c C2].
  + entailer!.
  + rewrite lseg_cons, cmd_node_eq. entailer!.
- destruct C2 as [|c C2].
  { simpl hdp in HRE. contradiction HRE; reflexivity. }
  rewrite lseg_cons, cmd_node_eq, (mstr_eq (c_name c)). simpl hdp. Intros.
  forward.
  forward_call (Ews, sh, c_namep c, c_name c, np, nm).
  Intros r.
  forward_if.
  + assert (Hn: c_name c = nm).
    { destruct (Int.eq_dec r Int.zero) as [|Hne]; auto. exfalso; apply Hne.
      match goal with Hx: r = _ |- _ => rewrite Hx; reflexivity end. }
    forward.
    unfold interp_rep, cmds_rep. rw_cmds. rewrite lseg_app, lseg_cons, cmd_node_eq, (mstr_eq (c_name c)).
    rewrite find_cmd_app by auto. simpl find_cmd.
    destruct (list_eq_dec Byte.eq_dec _ _) as [_|Hne]; [|exfalso; apply Hne; auto].
    entailer!.
  + assert (Hn: c_name c <> nm).
    { destruct (Int.eq_dec r Int.zero) as [He|]; [|auto]. exfalso.
      match goal with Hx: r <> _ |- _ => apply Hx; rewrite He; reflexivity end. }
    sep_apply (cmds_hd C2 nullval ltac:(simpl; auto)). Intros.
    forward.
    apply (exp_right (C1 ++ [c], C2)). simpl fst; simpl snd.
    rewrite lseg_snoc, cmd_node_eq, (mstr_eq (c_name c)).
    entailer!.
    split. rw_cmds. rewrite <- app_assoc. auto.
    apply Forall_app. split; auto.
- destruct C2 as [|c C2].
  2:{ rewrite lseg_cons, cmd_node_eq. Intros. simpl hdp in HRE.
      assert_PROP (isptr (c_ptr c)) by entailer!. rewrite HRE in *. contradiction. }
  forward.
  unfold interp_rep, cmds_rep. rw_cmds. rewrite lseg_app. rewrite find_cmd_app by auto.
  rewrite app_nil_r in *. simpl. entailer!.
Qed.
