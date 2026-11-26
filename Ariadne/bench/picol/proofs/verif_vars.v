(* picolGetVar, picolSetVar, picolRegisterCommand *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import Picol.picol_full Picol.spec_picol Picol.picol_defs Picol.verif_interp.

Lemma frames_split: forall F1 f F2,
  frames_rep (F1 ++ f :: F2) =
  (lseg frame_node f_ptr F1 (f_ptr f) * frame_node f (hdp f_ptr F2 nullval) *
   lseg frame_node f_ptr F2 nullval)%logic.
Proof. intros. unfold frames_rep. rewrite lseg_app. simpl. rewrite sepcon_assoc. auto. Qed.

Lemma cmds_split: forall C1 c C2,
  cmds_rep (C1 ++ c :: C2) =
  (lseg cmd_node c_ptr C1 (c_ptr c) * cmd_node c (hdp c_ptr C2 nullval) *
   lseg cmd_node c_ptr C2 nullval)%logic.
Proof. intros. unfold cmds_rep. rewrite lseg_app. simpl. rewrite sepcon_assoc. auto. Qed.

Lemma cstring_fold: forall sh s p, ~ In Byte.zero s ->
  data_at sh (tarray tschar (Zlength s + 1)) (map Vbyte (s ++ [Byte.zero])) p |-- cstring sh s p.
Proof. intros. unfold cstring. entailer!. Qed.

Lemma find_var_app: forall nm V1 V2, Forall (fun r => v_name r <> nm) V1 ->
  find_var nm (V1 ++ V2) = find_var nm V2.
Proof.
  induction V1; intros; simpl; auto. inv H.
  destruct (list_eq_dec Byte.eq_dec (v_name a) nm); [contradiction|]. auto.
Qed.

Lemma Znth_mid: forall {A} {d: Inhabitant A} (F1: list A) f F2, Znth (Zlength F1) (F1 ++ f :: F2) = f.
Proof. intros. rewrite app_Znth2 by lia. rewrite Z.sub_diag. apply Znth_0_cons. Qed.

Lemma find_var_split: forall nm V,
  (find_var nm V = nullval /\ Forall (fun r => v_name r <> nm) V) \/
  (exists V1 r V2, V = V1 ++ r :: V2 /\ Forall (fun r => v_name r <> nm) V1 /\
     v_name r = nm /\ find_var nm V = v_ptr r).
Proof.
  induction V as [|a V IH]; simpl.
  - left; auto.
  - destruct (list_eq_dec Byte.eq_dec (v_name a) nm).
    + right. exists [], a, V. auto.
    + destruct IH as [[? ?]|(V1 & r & V2 & ? & ? & ? & ?)].
      * left; auto.
      * right. exists (a :: V1), r, V2. subst. auto.
Qed.

Lemma find_cmd_split: forall nm C,
  (find_cmd nm C = nullval /\ Forall (fun c => c_name c <> nm) C) \/
  (exists C1 c C2, C = C1 ++ c :: C2 /\ Forall (fun c => c_name c <> nm) C1 /\
     c_name c = nm /\ find_cmd nm C = c_ptr c).
Proof.
  induction C as [|a C IH]; simpl.
  - left; auto.
  - destruct (list_eq_dec Byte.eq_dec (c_name a) nm).
    + right. exists [], a, C. auto.
    + destruct IH as [[? ?]|(C1 & r & C2 & ? & ? & ? & ?)].
      * left; auto.
      * right. exists (a :: C1), r, C2. subst. auto.
Qed.

Lemma list_mid: forall {A} {d: Inhabitant A} (F: list A) k, 0 <= k < Zlength F ->
  F = sublist 0 k F ++ Znth k F :: sublist (k+1) (Zlength F) F.
Proof.
  intros. rewrite <- (sublist_same 0 (Zlength F) F) at 1 by auto.
  rewrite (sublist_split 0 k (Zlength F)) by lia.
  rewrite (sublist_split k (k+1) (Zlength F)) by lia.
  rewrite sublist_len_1 by lia. auto.
Qed.

Ltac strcmp_res :=
  match goal with
  | Hr: if Int.eq_dec ?r Int.zero then _ else _, He: ?r = Int.repr 0 |- _ =>
      subst r; destruct (Int.eq_dec (Int.repr 0) Int.zero) as [_|Hne];
      [|exfalso; apply Hne; reflexivity]
  | Hr: if Int.eq_dec ?r Int.zero then _ else _, He: ?r <> Int.repr 0 |- _ =>
      destruct (Int.eq_dec r Int.zero) as [Hz|_]; [exfalso; apply He; rewrite Hz; reflexivity|]
  end.

Lemma body_picolGetVar: semax_body Vprog Gprog f_picolGetVar picolGetVar_spec.
Proof.
start_function.
unfold interp_rep, frames_rep. Intros.
destruct (i_frames st) as [|f0 F0] eqn:HF; [contradiction|].
sep_apply (frames_hd (f0 :: F0) nullval ltac:(simpl; auto)). Intros.
simpl hdp in *.
forward.
unfold cstring. Intros.
assert_PROP (Zlength nm + 1 > 0) by (entailer!; list_solve).
forward. forward.
sep_apply (cstring_fold sh nm np ltac:(auto)).
forward_if (EX F1: list frame, EX f: frame, EX F2: list frame,
  PROP (f0 :: F0 = F1 ++ f :: F2)
  LOCAL (temp _cf (f_ptr f); temp _i i; temp _name np)
  SEP (malloc_token Ews (tarray t_interp 1) i;
       data_at Ews t_interp (Vint (Int.repr (i_level st)),
         (f_ptr f0, (hdp c_ptr (i_cmds st) nullval, i_resultp st))) i;
       lseg frame_node f_ptr F1 (f_ptr f); lseg frame_node f_ptr (f :: F2) nullval;
       cmds_rep (i_cmds st); mstr (i_result st) (i_resultp st); cstring sh nm np))%assert.
- forward_loop (EX F1: list frame, EX f: frame, EX F2: list frame,
    PROP (f0 :: F0 = F1 ++ f :: F2)
    LOCAL (temp _cf (f_ptr f); temp _i i; temp _name np)
    SEP (malloc_token Ews (tarray t_interp 1) i;
         data_at Ews t_interp (Vint (Int.repr (i_level st)),
           (f_ptr f0, (hdp c_ptr (i_cmds st) nullval, i_resultp st))) i;
         lseg frame_node f_ptr F1 (f_ptr f); lseg frame_node f_ptr (f :: F2) nullval;
         cmds_rep (i_cmds st); mstr (i_result st) (i_resultp st); cstring sh nm np))%assert
   break: (EX F1: list frame, EX f: frame, EX F2: list frame,
    PROP (f0 :: F0 = F1 ++ f :: F2)
    LOCAL (temp _cf (f_ptr f); temp _i i; temp _name np)
    SEP (malloc_token Ews (tarray t_interp 1) i;
         data_at Ews t_interp (Vint (Int.repr (i_level st)),
           (f_ptr f0, (hdp c_ptr (i_cmds st) nullval, i_resultp st))) i;
         lseg frame_node f_ptr F1 (f_ptr f); lseg frame_node f_ptr (f :: F2) nullval;
         cmds_rep (i_cmds st); mstr (i_result st) (i_resultp st); cstring sh nm np))%assert.
  + Exists (@nil frame) f0 F0. entailer!.
  + Intros F1 f F2. rewrite lseg_cons, frame_node_eq. Intros.
    sep_apply (frames_hd F2 nullval ltac:(simpl; auto)). Intros.
    forward.
    destruct F2 as [|f2 F2]; cbn [hdp] in *.
    * forward_if.
      { simpl in *; contradiction. }
      forward. Exists F1 f (@nil frame). rewrite lseg_cons, frame_node_eq. cbn [hdp]. entailer!.
    * forward_if.
      { forward. Exists (F1 ++ [f]) f2 F2. rewrite lseg_snoc, frame_node_eq. entailer!.
        rewrite <- app_assoc. auto. }
      { rewrite lseg_cons, frame_node_eq. Intros. assert_PROP (isptr (f_ptr f2)) by entailer!.
        destruct f2; simpl in *; subst; contradiction. }
- forward. Exists (@nil frame) f0 F0. entailer!.
- Intros F1 f F2.
  rewrite lseg_cons, frame_node_eq. Intros.
  sep_apply (vars_hd (f_vars f) nullval ltac:(simpl; auto)). Intros.
  forward.
  forward_while (EX V1: list varrec, EX V2: list varrec,
    PROP (f_vars f = V1 ++ V2; Forall (fun r => v_name r <> nm) V1)
    LOCAL (temp _v (hdp v_ptr V2 nullval); temp _i i; temp _name np)
    SEP (malloc_token Ews (tarray t_interp 1) i;
         data_at Ews t_interp (Vint (Int.repr (i_level st)),
           (f_ptr f0, (hdp c_ptr (i_cmds st) nullval, i_resultp st))) i;
         lseg frame_node f_ptr F1 (f_ptr f);
         malloc_token Ews (tarray t_frame 1) (f_ptr f);
         data_at Ews t_frame (hdp v_ptr (f_vars f) nullval, hdp f_ptr F2 nullval) (f_ptr f);
         lseg var_node v_ptr V1 (hdp v_ptr V2 nullval); lseg var_node v_ptr V2 nullval;
         lseg frame_node f_ptr F2 nullval;
         cmds_rep (i_cmds st); mstr (i_result st) (i_resultp st); cstring sh nm np))%assert.
  + Exists (@nil varrec) (f_vars f). entailer!.
  + destruct V2 as [|r V2]; [entailer! | rewrite lseg_cons, var_node_eq; entailer!].
  + destruct V2 as [|r V2]. { simpl hdp in HRE. contradiction. }
    rewrite lseg_cons, var_node_eq, (mstr_eq (v_name r)). cbn [hdp] in *. Intros.
    sep_apply (vars_hd V2 nullval ltac:(simpl; auto)). Intros.
    forward.
    forward_call (Ews, sh, v_namep r, v_name r, np, nm).
    Intros res.
    forward_if.
    * strcmp_res.
      forward.
      Exists (Zlength F1).
      unfold interp_rep, frames_rep. rewrite HF. cbn [hdp].
      match goal with H: f0 :: F0 = _ |- _ => rewrite H end.
      rewrite Znth_mid.
      match goal with H: f_vars f = _ |- _ => rewrite H end.
      rewrite find_var_app by auto. simpl find_var.
      match goal with |- context [list_eq_dec ?e ?a ?b] =>
        destruct (list_eq_dec e a b); [|congruence] end.
      rewrite lseg_app, lseg_cons, frame_node_eq. cbn [hdp].
      match goal with H: f_vars f = _ |- _ => rewrite H end.
      rewrite lseg_app, lseg_cons, var_node_eq, (mstr_eq (v_name r)). cbn [hdp].
      entailer!.
      list_solve.
    * strcmp_res.
      forward.
      Exists (V1 ++ [r], V2). simpl fst; simpl snd.
      rewrite lseg_snoc, var_node_eq, (mstr_eq (v_name r)).
      entailer!.
      split. match goal with H: f_vars f = _ |- _ => rewrite H end. rewrite <- app_assoc. auto.
      apply Forall_app. split; auto.
  + destruct V2 as [|r V2].
    2:{ rewrite lseg_cons, var_node_eq. Intros. simpl hdp in HRE.
        assert_PROP (isptr (v_ptr r)) by entailer!. destruct r; simpl in *; subst; contradiction. }
    forward.
    Exists (Zlength F1).
    unfold interp_rep, frames_rep. rewrite HF. cbn [hdp].
    match goal with H: f0 :: F0 = _ |- _ => rewrite H end.
    rewrite Znth_mid.
    match goal with H: f_vars f = _ |- _ => rewrite H end.
    rewrite find_var_app by auto.
    rewrite lseg_app, lseg_cons, frame_node_eq. cbn [hdp].
    match goal with H: f_vars f = _ |- _ => rewrite H end.
    rewrite !app_nil_r.
    entailer!.
    list_solve.
Qed.

Lemma hdp_mid: forall {A} (ptr: A -> val) l1 a b l2 t, ptr a = ptr b ->
  hdp ptr (l1 ++ a :: l2) t = hdp ptr (l1 ++ b :: l2) t.
Proof. intros. destruct l1; simpl; auto. Qed.

Lemma split_at: forall {A} {d: Inhabitant A} (F: list A) k, 0 <= k < Zlength F ->
  exists F1 F2, F = F1 ++ Znth k F :: F2 /\ Zlength F1 = k.
Proof.
  intros. exists (sublist 0 k F), (sublist (k+1) (Zlength F) F).
  split. apply list_mid; auto. list_solve.
Qed.

Lemma cstring_unfold: forall sh s p, cstring sh s p |--
  !! (~ In Byte.zero s) && data_at sh (tarray tschar (Zlength s + 1)) (map Vbyte (s ++ [Byte.zero])) p.
Proof. intros. unfold cstring. entailer!. Qed.

Lemma cmds_ok_remove: forall gv C1 c C2, cmds_ok gv (C1 ++ c :: C2) -> cmds_ok gv (C1 ++ C2).
Proof.
  intros. unfold cmds_ok in *. apply Forall_app in H. destruct H as [? H']. inv H'.
  apply Forall_app. auto.
Qed.

Ltac absurd_branch :=
  first [ match goal with H: _ <> _ |- _ => solve [exfalso; apply H; reflexivity] end
        | match goal with H: typed_true _ _ |- _ => solve [inv H] end
        | match goal with H: typed_false _ _ |- _ => solve [inv H] end
        | match goal with H: @eq int _ _ |- _ => solve [discriminate H] end
        | match goal with H: isptr ?p, E: ?p = nullval |- _ => rewrite E in H; simpl in H; contradiction end ].

Ltac nonnull_contra p :=
  assert_PROP (isptr p) by entailer!;
  match goal with H: _ = nullval, Hp: isptr _ |- _ =>
    first [ rewrite H in Hp | simpl in H; rewrite H in Hp ]; simpl in Hp; contradiction end.

(* walk from the current frame to the global one; Q, R: the other locals and SEP items *)
Ltac walk_frames f0 F0 Q R :=
  forward_if (EX F1: list frame, EX f: frame, EX F2: list frame,
    PROPx [f0 :: F0 = F1 ++ f :: F2]
    (LOCALx (temp _cf (f_ptr f) :: Q)
    (SEPx (lseg frame_node f_ptr F1 (f_ptr f) :: lseg frame_node f_ptr (f :: F2) nullval :: R))))%assert;
  [ forward_loop (EX F1: list frame, EX f: frame, EX F2: list frame,
      PROPx [f0 :: F0 = F1 ++ f :: F2]
      (LOCALx (temp _cf (f_ptr f) :: Q)
      (SEPx (lseg frame_node f_ptr F1 (f_ptr f) :: lseg frame_node f_ptr (f :: F2) nullval :: R))))%assert
     break: (EX F1: list frame, EX f: frame, EX F2: list frame,
      PROPx [f0 :: F0 = F1 ++ f :: F2]
      (LOCALx (temp _cf (f_ptr f) :: Q)
      (SEPx (lseg frame_node f_ptr F1 (f_ptr f) :: lseg frame_node f_ptr (f :: F2) nullval :: R))))%assert;
    [ Exists (@nil frame) f0 F0; entailer!
    | let F1 := fresh "F1" in let f := fresh "f" in let F2 := fresh "F2" in
      Intros F1 f F2; rewrite lseg_cons, frame_node_eq; Intros;
      sep_apply (frames_hd F2 nullval ltac:(simpl; auto)); Intros;
      forward;
      let f2 := fresh "f2" in let F3 := fresh "F3" in
      destruct F2 as [|f2 F3]; cbn [hdp] in *;
      [ forward_if;
        [ simpl in *; contradiction
        | forward; Exists F1 f (@nil frame); rewrite lseg_cons, frame_node_eq; cbn [hdp]; entailer! ]
      | forward_if;
        [ forward; Exists (F1 ++ [f]) f2 F3; rewrite lseg_snoc, frame_node_eq; entailer!;
          rewrite <- app_assoc; auto
        | rewrite lseg_cons, frame_node_eq; Intros; assert_PROP (isptr (f_ptr f2)) by entailer!;
          destruct f2; simpl in *; subst; contradiction ] ] ]
  | forward; Exists (@nil frame) f0 F0; entailer!
  | ].

Lemma body_picolSetVar: semax_body Vprog Gprog f_picolSetVar picolSetVar_spec.
Proof.
start_function.
forward_call (i, st, sh1, nm, np).
Intros k.
destruct (find_var_split nm (f_vars (Znth k (i_frames st))))
  as [[Hn Hall] | (V1 & r & V2 & HV & Hall & Hnm & Hfind)].
2:{
  rewrite Hfind.
  destruct (split_at (i_frames st) k ltac:(auto)) as (F1 & F2 & HFk & HF1).
  set (f := Znth k (i_frames st)) in *. clearbody f.
  unfold interp_rep, frames_rep. Intros.
  rewrite HFk. rewrite lseg_app. cbn [hdp]. rewrite lseg_cons, frame_node_eq.
  rewrite HV. rewrite lseg_app, lseg_cons, var_node_eq. cbn [hdp]. Intros.
  forward_if.
  + forward.
    sep_apply (mstr_free' (v_val r) (v_valp r)).
    forward_call (tarray tschar (Zlength (v_val r) + 1), v_valp r, gv).
    forward_call (sh2, x, xp, gv).
    Intros q.
    forward.
    set (r' := mkvar (v_ptr r) (v_name r) (v_namep r) x q).
    Exists (mkist (i_level st) (F1 ++ mkframe (f_ptr f) (V1 ++ r' :: V2) :: F2)
                  (i_cmds st) (i_result st) (i_resultp st)).
    unfold interp_rep, frames_rep. cbn [i_level i_frames i_cmds i_result i_resultp].
    rewrite (hdp_mid f_ptr F1 (mkframe (f_ptr f) (V1 ++ r' :: V2)) f F2) by reflexivity.
    rewrite lseg_app. cbn [hdp]. rewrite lseg_cons, frame_node_eq. cbn [f_ptr f_vars].
    rewrite (hdp_mid v_ptr V1 r' r V2) by reflexivity.
    rewrite lseg_app, lseg_cons, var_node_eq. cbn [hdp]. subst r'.
    cbn [v_ptr v_name v_namep v_val v_valp].
    entailer!.
    split; [rewrite HFk; list_solve | intro X; destruct F1; inv X].
  + assert_PROP (isptr (v_ptr r)) by entailer!.
    match goal with H: _ = nullval |- _ => destruct r; simpl in H; rewrite H in * end.
    simpl in *; contradiction. }
rewrite Hn.
forward_if.
{ simpl in *; contradiction. }
forward_call (existT (fun t => list (reptype t)) t_var [], nullval, 0, 1, gv).
{ rewrite if_true by auto. cancel. }
{ simpl projT1. change (sizeof t_var) with 24. rep_lia. }
Intros v. simpl projT1 in *; simpl projT2 in *. rewrite xr1.
forward_call (sh1, nm, np, gv). Intros nq.
forward.
forward_call (sh2, x, xp, gv). Intros xq.
forward.
unfold interp_rep, frames_rep. Intros.
destruct (i_frames st) as [|f0 F0] eqn:HF; [contradiction|].
sep_apply (frames_hd (f0 :: F0) nullval ltac:(simpl; auto)). Intros.
simpl hdp in *.
forward.
sep_apply (cstring_unfold sh1 nm np). Intros.
assert_PROP (Zlength nm + 1 > 0) by (entailer!; list_solve).
forward. forward.
sep_apply (cstring_fold sh1 nm np ltac:(auto)).
walk_frames f0 F0 [temp _v v; temp _i i; gvars gv]
  [malloc_token Ews (tarray t_interp 1) i;
   data_at Ews t_interp (Vint (Int.repr (i_level st)),
     (f_ptr f0, (hdp c_ptr (i_cmds st) nullval, i_resultp st))) i;
   cmds_rep (i_cmds st); mstr (i_result st) (i_resultp st);
   cstring sh1 nm np; cstring sh2 x xp; mem_mgr gv; Gx gv;
   malloc_token Ews (tarray t_var 1) v; data_at Ews t_var (nq, (xq, Vundef)) v;
   mstr nm nq; mstr x xq].
Intros F1 f F2.
rewrite lseg_cons, frame_node_eq. Intros.
sep_apply (vars_hd (f_vars f) nullval ltac:(simpl; auto)). Intros.
forward. forward. forward.
set (r := mkvar v nm nq x xq).
Exists (mkist (i_level st) (F1 ++ mkframe (f_ptr f) (r :: f_vars f) :: F2)
              (i_cmds st) (i_result st) (i_resultp st)).
unfold interp_rep, frames_rep. cbn [i_level i_frames i_cmds i_result i_resultp].
rewrite (hdp_mid f_ptr F1 (mkframe (f_ptr f) (r :: f_vars f)) f F2) by reflexivity.
match goal with H: f0 :: F0 = _ |- _ => rewrite <- H end. cbn [hdp].
rewrite lseg_app. cbn [hdp]. rewrite lseg_cons, frame_node_eq. cbn [f_ptr f_vars hdp].
rewrite lseg_cons, var_node_eq. subst r. cbn [v_ptr v_name v_namep v_val v_valp].
entailer!.
try rewrite HF.
match goal with H: f0 :: F0 = _ |- _ => rewrite H end.
split; [list_solve | intro X; destruct F1; inv X].
Qed.

Lemma body_picolRegisterCommand: semax_body Vprog Gprog f_picolRegisterCommand picolRegisterCommand_spec.
Proof.
start_function.
forward_call (i, st, sh, nm, np).
destruct (find_cmd_split nm (i_cmds st))
  as [[Hn Hall] | (C1 & c & C2 & HC & Hall & Hnm & Hfind)].
- rewrite Hn.
  forward.
  forward_if (EX c: val, PROP ()
    LOCAL (temp _c c; temp _existing (Vint Int.zero); temp _i i; temp _name np; temp _f f; gvars gv)
    SEP (mem_mgr gv; Gx gv; interp_rep i st; cstring sh nm np;
         malloc_token Ews (tarray t_cmd 1) c;
         data_at Ews t_cmd (nullval, (Vundef, (Vundef, (nullval, nullval)))) c))%assert.
  { forward_call (existT (fun t => list (reptype t)) t_cmd [], nullval, 0, 1, gv).
    { rewrite if_true by auto. cancel. }
    { simpl projT1. change (sizeof t_cmd) with 40. rep_lia. }
    Intros c. simpl projT1 in *; simpl projT2 in *. rewrite xr1.
    forward. forward. forward.
    Exists c. entailer!. }
  { absurd_branch. }
  Intros c.
  forward.
  forward_if (EX q: val, PROP ()
    LOCAL (temp _c c; temp _existing (Vint Int.zero); temp _i i; temp _name np; temp _f f; gvars gv)
    SEP (mem_mgr gv; Gx gv; interp_rep i st; cstring sh nm np;
         malloc_token Ews (tarray t_cmd 1) c;
         data_at Ews t_cmd (q, (Vundef, (Vundef, (nullval, nullval)))) c; mstr nm q))%assert.
  { forward_call (sh, nm, np, gv). Intros q.
    forward. Exists q. entailer!. }
  { absurd_branch. }
  Intros q.
  forward.
  forward_if.
  2:{ absurd_branch. }
  unfold interp_rep, cmds_rep. Intros.
  sep_apply (cmds_hd (i_cmds st) nullval ltac:(simpl; auto)). Intros.
  forward. forward. forward.
  Exists (mkist (i_level st) (i_frames st) (mkcmd c nm q f None nullval None nullval :: i_cmds st)
                (i_result st) (i_resultp st))
         (@nil cmdrec) (mkcmd c nm q f None nullval None nullval) (i_cmds st).
  unfold interp_rep, cmds_rep. cbn [i_level i_frames i_cmds i_result i_resultp].
  rewrite lseg_cons, cmd_node_eq. cbn [hdp c_ptr c_name c_namep c_func c_arg c_argp c_body c_bodyp ostr app].
  entailer!.
- rewrite Hfind.
  assert (Hok: cmds_ok gv (C1 ++ C2)) by (apply (cmds_ok_remove gv C1 c C2); rewrite <- HC; auto).
  unfold interp_rep, cmds_rep. Intros.
  rewrite HC. rewrite lseg_app. cbn [hdp]. rewrite lseg_cons, cmd_node_eq. Intros.
  assert_PROP (isptr (c_ptr c)) by entailer!.
  forward.
  assert (Hex: forall p, isptr p ->
    force_val (sem_binary_operation' Cop.One (tptr (Tstruct _picolCmd noattr)) (tptr tvoid) p
                 (eval_cast tint (tptr tvoid) (Vint (Int.repr 0)))) = Vint Int.one)
    by (intros p Hp; destruct p; try contradiction; reflexivity).
  rewrite (Hex (c_ptr c)) by auto.
  forward_if (PROP ()
    LOCAL (temp _c (c_ptr c); temp _existing (Vint Int.one); temp _i i; temp _name np; temp _f f; gvars gv)
    SEP (malloc_token Ews (tarray t_interp 1) i;
         data_at Ews t_interp (Vint (Int.repr (i_level st)), (hdp f_ptr (i_frames st) nullval,
            (hdp c_ptr (C1 ++ c :: C2) nullval, i_resultp st))) i;
         frames_rep (i_frames st); lseg cmd_node c_ptr C1 (c_ptr c);
         malloc_token Ews (tarray t_cmd 1) (c_ptr c);
         data_at Ews t_cmd (c_namep c, (c_func c, (hdp c_ptr C2 nullval, (nullval, nullval)))) (c_ptr c);
         mstr (c_name c) (c_namep c); lseg cmd_node c_ptr C2 nullval;
         mstr (i_result st) (i_resultp st); mem_mgr gv; Gx gv; cstring sh nm np)).
  { absurd_branch. }
  { forward.
    sep_apply (ostr_free (c_arg c) (c_argp c)).
    forward_call (tarray tschar (Zlength (match c_arg c with Some s => s | None => [] end) + 1),
                  c_argp c, gv).
    forward.
    sep_apply (ostr_free (c_body c) (c_bodyp c)).
    forward_call (tarray tschar (Zlength (match c_body c with Some s => s | None => [] end) + 1),
                  c_bodyp c, gv).
    forward. forward.
    entailer!. }
  forward.
  match goal with |- semax _ ?Pre _ _ => forward_if Pre end.
  { nonnull_contra (c_namep c). }
  { forward. entailer!. }
  forward.
  forward_if.
  { absurd_branch. }
  forward.
  set (c' := mkcmd (c_ptr c) (c_name c) (c_namep c) f None nullval None nullval).
  Exists (mkist (i_level st) (i_frames st) (C1 ++ c' :: C2) (i_result st) (i_resultp st)) C1 c' C2.
  unfold interp_rep, cmds_rep. cbn [i_level i_frames i_cmds i_result i_resultp].
  rewrite (hdp_mid c_ptr C1 c' c C2) by reflexivity.
  rewrite lseg_app. cbn [hdp]. rewrite lseg_cons, cmd_node_eq. subst c'.
  cbn [c_ptr c_name c_namep c_func c_arg c_argp c_body c_bodyp ostr].
  entailer!.
Qed.
