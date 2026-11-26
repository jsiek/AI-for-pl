(* main *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import Picol.picol_full Picol.spec_picol Picol.picol_defs.

Lemma tsh_split: forall t v p,
  data_at Tsh t v p = (data_at Ews t v p * data_at (Share.comp Ews) t v p)%logic.
Proof. intros. symmetry. apply data_at_share_join. apply join_comp_Tsh. Qed.

Lemma to_cstring: forall s n p, n = Zlength s + 1 -> ~ In Byte.zero s ->
  data_at Tsh (tarray tschar n) (map Vbyte (s ++ [Byte.zero])) p |--
  cstring Ews s p * data_at (Share.comp Ews) (tarray tschar n) (map Vbyte (s ++ [Byte.zero])) p.
Proof.
  intros. subst n. rewrite tsh_split. unfold cstring. entailer!.
Qed.

Lemma from_cstring: forall s n p, n = Zlength s + 1 ->
  cstring Ews s p * data_at (Share.comp Ews) (tarray tschar n) (map Vbyte (s ++ [Byte.zero])) p |--
  data_at_ Tsh (tarray tschar n) p.
Proof.
  intros. subst n. unfold cstring. Intros. rewrite <- tsh_split. apply data_at_data_at_.
Qed.

Lemma from_ptrs: forall n v p,
  data_at Ews (tarray (tptr tschar) n) v p * data_at (Share.comp Ews) (tarray (tptr tschar) n) v p |--
  data_at_ Tsh (tarray (tptr tschar) n) p.
Proof. intros. rewrite <- tsh_split. apply data_at_data_at_. Qed.

Definition picol_bytes : list byte := map Byte.repr [112; 105; 99; 111; 108].
Definition script_bytes : list byte := map Byte.repr [115; 99; 114; 105; 112; 116; 46; 116; 99; 108].

Lemma picol_nz: ~ In Byte.zero picol_bytes.
Proof. unfold picol_bytes. simpl. intuition; discriminate. Qed.
Lemma script_nz: ~ In Byte.zero script_bytes.
Proof. unfold script_bytes. simpl. intuition; discriminate. Qed.

(* keep globvars2pred folded: picol_main's spec takes it as it is *)
Local Ltac expand_main_pre ::=
  match goal with |- semax _ (main_pre_old _ _ _ * _)%logic _ _ =>
    rewrite main_pre_start_old, (sepcon_comm (PROPx _ _)), insert_SEP end.

Lemma body_main: semax_body Vprog Gprog f_main main_spec.
Proof.
start_function.
sep_apply (create_mem_mgr gv).
repeat forward.
match goal with |- context [data_at Tsh (tarray tschar 6) ?L v_a0] =>
  replace L with (map Vbyte (picol_bytes ++ [Byte.zero])) by reflexivity end.
match goal with |- context [data_at Tsh (tarray tschar 6) ?L v_b0] =>
  replace L with (map Vbyte (picol_bytes ++ [Byte.zero])) by reflexivity end.
match goal with |- context [data_at Tsh (tarray tschar 11) ?L v_b1] =>
  replace L with (map Vbyte (script_bytes ++ [Byte.zero])) by reflexivity end.
match goal with |- context [data_at Tsh (tarray (tptr tschar) 2) ?L v_repl] =>
  replace L with ([v_a0] ++ [nullval]) by reflexivity end.
match goal with |- context [data_at Tsh (tarray (tptr tschar) 3) ?L v_file] =>
  replace L with ([v_b0; v_b1] ++ [nullval]) by reflexivity end.
sep_apply (to_cstring picol_bytes 6 v_a0 eq_refl picol_nz).
sep_apply (to_cstring picol_bytes 6 v_b0 eq_refl picol_nz).
sep_apply (to_cstring script_bytes 11 v_b1 eq_refl script_nz).
rewrite (tsh_split (tarray (tptr tschar) 2)), (tsh_split (tarray (tptr tschar) 3)).
Intros.
forward_call (gv, 1, v_repl, [picol_bytes], [v_a0]).
all: try solve [simpl; cancel | repeat split; reflexivity | rep_lia | list_solve].
forward_call (gv, 2, v_file, [picol_bytes; script_bytes], [v_b0; v_b1]).
all: try solve [cbn [args_pred]; cancel | repeat split; reflexivity | rep_lia | list_solve].
Intros r2.
forward.
Exists r2.
simpl args_pred.
sep_apply (from_cstring picol_bytes 6 v_a0 eq_refl).
sep_apply (from_cstring picol_bytes 6 v_b0 eq_refl).
sep_apply (from_cstring script_bytes 11 v_b1 eq_refl).
sep_apply (from_ptrs (1 + 1) ([v_a0] ++ [nullval]) v_repl).
sep_apply (from_ptrs (2 + 1) ([v_b0; v_b1] ++ [nullval]) v_file).
entailer!.
Qed.
