(* Token buffers for picolEval: argv's strings live in buffers that may be
   longer than the string (after unescaping). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import Picol.picol_full Picol.spec_picol Picol.picol_defs Picol.verif_cmd_common
  Picol.verif_strutil.

Record tok := mktok { tk_s: list byte; tk_n: Z; tk_p: val }.
#[export] Instance Inh_tok : Inhabitant tok := mktok [] 1 nullval.

Definition tbuf (x: tok) : mpred :=
  (malloc_token Ews (tarray tschar (tk_n x)) (tk_p x) * strbuf Ews (tk_s x) (tk_n x) (tk_p x))%logic.

Definition tbufs (L: list tok) : mpred := fold_right_sepcon (map tbuf L).

Definition ttail (x: tok) : mpred :=
  (malloc_token Ews (tarray tschar (tk_n x)) (tk_p x) *
   EX rest: list val,
    !! (Zlength (tk_s x) < tk_n x /\ Zlength rest = tk_n x - Zlength (tk_s x) - 1) &&
    data_at Ews (tarray tschar (tk_n x - (Zlength (tk_s x) + 1))) rest
      (field_address0 (tarray tschar (tk_n x)) (SUB (Zlength (tk_s x) + 1)) (tk_p x)))%logic.

Definition ttails (L: list tok) : mpred := fold_right_sepcon (map ttail L).

Lemma tbuf_split: forall x, tbuf x = (cstring Ews (tk_s x) (tk_p x) * ttail x)%logic.
Proof.
  intros. unfold tbuf, ttail, strbuf. apply pred_ext.
  - Intros rest. rewrite strbuf_split by auto. Exists rest. entailer!.
  - Intros rest. Exists rest. unfold cstring. Intros.
    rewrite strbuf_split by auto. unfold cstring. entailer!.
Qed.

Lemma tbufs_split: forall L,
  tbufs L = (args_pred (map tk_s L) (map tk_p L) * ttails L)%logic.
Proof.
  induction L as [|x L IH]; simpl.
  - unfold tbufs, ttails; simpl. rewrite emp_sepcon. auto.
  - unfold tbufs, ttails in *; simpl. rewrite IH, tbuf_split. apply pred_ext; cancel.
Qed.

Lemma tbufs_app: forall L1 L2, tbufs (L1 ++ L2) = (tbufs L1 * tbufs L2)%logic.
Proof. intros. unfold tbufs. rewrite map_app. apply fold_right_sepcon_app. Qed.

Lemma tbufs_nil: tbufs [] = emp.
Proof. reflexivity. Qed.

Lemma tbufs_one: forall x, tbufs [x] = tbuf x.
Proof. intros. unfold tbufs. simpl. rewrite sepcon_emp. auto. Qed.

Lemma tbufs_cons: forall x L, tbufs (x :: L) = (tbuf x * tbufs L)%logic.
Proof. reflexivity. Qed.

Lemma tbufs_sub: forall L j, 0 <= j < Zlength L ->
  tbufs (sublist j (Zlength L) L) = (tbuf (Znth j L) * tbufs (sublist (j + 1) (Zlength L) L))%logic.
Proof.
  intros. rewrite (sublist_split j (j+1) (Zlength L)) by lia.
  rewrite tbufs_app, sublist_len_1 by lia. rewrite tbufs_one. auto.
Qed.

Lemma mstr_tbuf: forall w p, mstr w p |-- tbuf (mktok w (Zlength w + 1) p).
Proof.
  intros. unfold mstr, tbuf, strbuf, cstring. simpl. Intros. Exists (@nil val).
  rewrite app_nil_r. entailer!; repeat split; try lia; try list_solve; auto.
Qed.

Lemma tbuf_free: forall x, tbuf x |--
  (malloc_token Ews (tarray tschar (tk_n x)) (tk_p x) * data_at_ Ews (tarray tschar (tk_n x)) (tk_p x))%logic.
Proof. intros. unfold tbuf, strbuf. Intros rest. cancel. Qed.

Lemma tbuf_isptr: forall x, tbuf x |-- !! isptr (tk_p x).
Proof. intros. unfold tbuf, strbuf. Intros rest. entailer!. Qed.

Lemma tbufs_isptr: forall L j, 0 <= j < Zlength L -> tbufs L |-- !! isptr (Znth j L).(tk_p).
Proof.
  intros. rewrite <- (sublist_same 0 (Zlength L) L) at 1 by auto.
  rewrite (sublist_split 0 j (Zlength L)) by lia. rewrite tbufs_app.
  rewrite tbufs_sub by lia. sep_apply (tbuf_isptr (Znth j L)). entailer!.
Qed.

Lemma args_size_map_app: forall (L1 L2: list tok),
  args_size (map tk_s (L1 ++ L2)) = args_size (map tk_s L1) + args_size (map tk_s L2).
Proof. intros. rewrite map_app. apply args_size_app. Qed.
