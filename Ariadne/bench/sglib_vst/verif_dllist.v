Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import SglibVST.dllist SglibVST.spec_dllist.

Local Open Scope logic.

(* ================================================================== *)
(* Helper lemmas                                                      *)
(* ================================================================== *)

Lemma nodesN_split: forall sh s vs a b lo,
  nodesN sh s vs lo (a+b)%nat =
  nodesN sh s vs lo a * nodesN sh s vs (lo + Z.of_nat a) b.
Proof.
  induction a; intros; simpl.
  - rewrite emp_sepcon. f_equal. lia.
  - rewrite IHa. rewrite sepcon_assoc.
    replace (lo + 1 + Z.of_nat a) with (lo + Z.of_nat (S a)) by lia.
    reflexivity.
Qed.

Lemma nodes_split: forall sh s vs lo m hi, lo <= m <= hi ->
  nodes sh s vs lo hi = nodes sh s vs lo m * nodes sh s vs m hi.
Proof.
  intros. unfold nodes.
  replace (Z.to_nat (hi-lo)) with (Z.to_nat (m-lo) + Z.to_nat (hi-m))%nat by lia.
  rewrite nodesN_split. f_equal. f_equal. lia.
Qed.

Lemma nodes_empty: forall sh s vs lo hi, hi <= lo -> nodes sh s vs lo hi = emp.
Proof.
  intros. unfold nodes. replace (Z.to_nat (hi-lo)) with O by lia. reflexivity.
Qed.

Lemma nodes_one: forall sh s vs i,
  nodes sh s vs i (i+1) = data_at sh t_dl (Znth i vs) (Znth i s).
Proof.
  intros. unfold nodes. replace (Z.to_nat (i+1-i)) with 1%nat by lia.
  simpl. apply sepcon_emp.
Qed.

Lemma nodes_focus: forall sh s vs lo i hi, lo <= i < hi ->
  nodes sh s vs lo hi =
  nodes sh s vs lo i * data_at sh t_dl (Znth i vs) (Znth i s) *
  nodes sh s vs (i+1) hi.
Proof.
  intros. rewrite (nodes_split sh s vs lo i hi) by lia.
  rewrite (nodes_split sh s vs i (i+1) hi) by lia.
  rewrite nodes_one. rewrite sepcon_assoc. reflexivity.
Qed.

Lemma nodesN_ext: forall sh s vs s' vs' d n lo,
  (forall i, lo <= i < lo + Z.of_nat n ->
     Znth i s = Znth (i+d) s' /\ Znth i vs = Znth (i+d) vs') ->
  nodesN sh s vs lo n = nodesN sh s' vs' (lo+d) n.
Proof.
  induction n; intros; simpl; auto.
  destruct (H lo) as [H1 H2]; [lia|].
  rewrite H1, H2. f_equal.
  replace (lo + d + 1) with (lo + 1 + d) by lia.
  apply IHn. intros. apply H. lia.
Qed.

Lemma nodes_ext: forall sh s vs s' vs' d lo hi,
  (forall i, lo <= i < hi ->
     Znth i s = Znth (i+d) s' /\ Znth i vs = Znth (i+d) vs') ->
  nodes sh s vs lo hi = nodes sh s' vs' (lo+d) (hi+d).
Proof.
  intros. unfold nodes.
  replace (hi + d - (lo + d)) with (hi - lo) by lia.
  apply nodesN_ext. intros. apply H. lia.
Qed.

Lemma nodes_ext0: forall sh s vs s' vs' lo hi,
  (forall i, lo <= i < hi -> Znth i s = Znth i s' /\ Znth i vs = Znth i vs') ->
  nodes sh s vs lo hi = nodes sh s' vs' lo hi.
Proof.
  intros. rewrite (nodes_ext sh s vs s' vs' 0 lo hi).
  - rewrite !Z.add_0_r. auto.
  - intros. rewrite Z.add_0_r. auto.
Qed.

Lemma nodes_upd: forall sh s vs lo hi k v,
  (k < lo \/ hi <= k) ->
  nodes sh s (upd_Znth k vs v) lo hi = nodes sh s vs lo hi.
Proof.
  intros. apply nodes_ext0. intros. split; auto.
  assert (i <> k) by lia. clear H.
  destruct (zle 0 k); [destruct (zlt k (Zlength vs))|].
  - rewrite upd_Znth_diff' by lia. auto.
  - rewrite upd_Znth_out_of_range by lia. auto.
  - rewrite upd_Znth_out_of_range by lia. auto.
Qed.

Lemma nodesN_isptr: forall sh s vs n lo,
  nodesN sh s vs lo n |--
  !! (forall i, lo <= i < lo + Z.of_nat n -> isptr (Znth i s)).
Proof.
  induction n; intros; simpl.
  - apply prop_right. intros. lia.
  - sep_apply (IHn (lo+1)). Intros. entailer!.
    intros i Hi. destruct (zeq i lo).
    + subst. auto.
    + apply H. lia.
Qed.

Lemma nodes_isptr: forall sh s vs lo hi,
  nodes sh s vs lo hi |-- !! (forall i, lo <= i < hi -> isptr (Znth i s)).
Proof.
  intros. unfold nodes. eapply derives_trans; [apply nodesN_isptr|]. apply prop_derives.
  intros. apply H. lia.
Qed.

Lemma Znth_or_null_in: forall s i, 0 <= i < Zlength s -> Znth_or_null s i = Znth i s.
Proof.
  intros. unfold Znth_or_null. destruct (zle 0 i); [|lia]. destruct (zlt i (Zlength s)); [|lia]. auto.
Qed.

Lemma Znth_or_null_out: forall s i, (i < 0 \/ Zlength s <= i) -> Znth_or_null s i = nullval.
Proof.
  intros. unfold Znth_or_null. destruct (zle 0 i); auto. destruct (zlt i (Zlength s)); auto. lia.
Qed.

Lemma Zlength_ins: forall {A} {d: Inhabitant A} j (x: A) l,
  0 <= j <= Zlength l -> Zlength (ins j x l) = Zlength l + 1.
Proof. intros. unfold ins. list_solve. Qed.

Lemma Znth_ins: forall {A} {d: Inhabitant A} j (x: A) l i,
  0 <= j <= Zlength l -> 0 <= i <= Zlength l ->
  Znth i (ins j x l) = if zlt i j then Znth i l else if zeq i j then x else Znth (i-1) l.
Proof.
  intros. unfold ins.
  destruct (zlt i j); [|destruct (zeq i j)]; list_solve.
Qed.

Lemma Znth_or_null_ins: forall j x s k,
  0 <= j <= Zlength s ->
  Znth_or_null (ins j x s) k =
  if zlt k j then Znth_or_null s k else if zeq k j then x else Znth_or_null s (k-1).
Proof.
  intros.
  destruct (zlt k 0).
  { rewrite !Znth_or_null_out by lia. destruct (zlt k j); [|lia]. auto. }
  destruct (zle k (Zlength s)).
  - rewrite Znth_or_null_in by (rewrite Zlength_ins; lia).
    rewrite Znth_ins by lia.
    destruct (zlt k j). rewrite Znth_or_null_in by lia; auto.
    destruct (zeq k j); auto. rewrite Znth_or_null_in by lia; auto.
  - rewrite Znth_or_null_out by (rewrite Zlength_ins; lia).
    destruct (zlt k j); [lia|]. destruct (zeq k j); [lia|].
    rewrite Znth_or_null_out by lia. auto.
Qed.

Lemma map_ins: forall {A B} {da: Inhabitant A} {db: Inhabitant B} (f: A -> B) j x l,
  0 <= j <= Zlength l ->
  map f (ins j x l) = ins j (f x) (map f l).
Proof.
  intros. unfold ins. rewrite map_app. simpl.
  rewrite !sublist_map. rewrite Zlength_map. auto.
Qed.

Lemma nodes_ins: forall sh s vs j e x,
  0 <= j <= Zlength s -> Zlength vs = Zlength s ->
  nodes sh (ins j e s) (ins j x vs) 0 (Zlength s + 1) =
  nodes sh s vs 0 j * data_at sh t_dl x e * nodes sh s vs j (Zlength s).
Proof.
  intros.
  rewrite (nodes_focus sh (ins j e s) (ins j x vs) 0 j) by lia.
  assert (E1: Znth j (ins j e s) = e).
  { rewrite Znth_ins by lia. destruct (zlt j j); [lia|]. destruct (zeq j j); [auto|lia]. }
  assert (E2: Znth j (ins j x vs) = x).
  { rewrite Znth_ins by lia. destruct (zlt j j); [lia|]. destruct (zeq j j); [auto|lia]. }
  rewrite E1, E2.
  rewrite (nodes_ext0 sh (ins j e s) (ins j x vs) s vs 0 j).
  2:{ intros. rewrite !Znth_ins by lia. destruct (zlt i j); [auto|lia]. }
  rewrite (nodes_ext sh s vs (ins j e s) (ins j x vs) 1 j (Zlength s)).
  2:{ intros. rewrite !Znth_ins by lia. destruct (zlt (i+1) j); [lia|].
      destruct (zeq (i+1) j); [lia|]. replace (i+1-1) with i by lia. auto. }
  reflexivity.
Qed.

(* ================================================================== *)

Lemma prev_links_sub: forall s vs lo hi lo' hi',
  prev_links s vs lo hi -> lo <= lo' -> hi' <= hi -> prev_links s vs lo' hi'.
Proof. unfold prev_links; intros. apply H; lia. Qed.

Lemma next_links_sub: forall s vs lo hi lo' hi',
  next_links s vs lo hi -> lo <= lo' -> hi' <= hi -> next_links s vs lo' hi'.
Proof. unfold next_links; intros. apply H; lia. Qed.

Lemma cmp_payloads_sub: forall scp vs lo hi lo' hi',
  cmp_payloads scp vs lo hi -> lo <= lo' -> hi' <= hi -> cmp_payloads scp vs lo' hi'.
Proof.
  unfold cmp_payloads, int_payloads; intros. destruct H; [left; auto|right].
  intros. apply H; lia.
Qed.

Lemma Znth_or_null_pn: forall s i lo hi,
  (forall i, lo <= i < hi -> isptr (Znth i s)) ->
  (i < 0 \/ Zlength s <= i \/ lo <= i < hi) -> is_pointer_or_null (Znth_or_null s i).
Proof.
  intros.
  destruct (zlt i 0). { rewrite Znth_or_null_out by lia. simpl; auto. }
  destruct (zle (Zlength s) i). { rewrite Znth_or_null_out by lia. simpl; auto. }
  rewrite Znth_or_null_in by lia.
  assert (isptr (Znth i s)) by (apply H; lia).
  destruct (Znth i s); try contradiction; simpl; auto.
Qed.

Lemma iter_A: forall scp s b f k,
  -1 <= b < f -> f <= Zlength s -> 0 <= k <= b -> (scp = nullval -> k = b) ->
  isptr (Znth k s) ->
  iter_step scp s b f (k-1) f (Znth k s).
Proof.
  intros. split.
  - unfold step_any. split; [lia|]. split; [lia|]. split.
    + right. exists k. split; [lia|]. split; [lia|]. auto.
    + intro Hr. rewrite Hr in H3. contradiction.
  - intro Hs. specialize (H2 Hs). subst k. unfold step_exact. right; left.
    split; [lia|]. auto.
Qed.

Lemma iter_B: forall scp s b f k,
  -1 <= b < f -> f <= k < Zlength s -> (scp = nullval -> b = -1 /\ k = f) ->
  isptr (Znth k s) ->
  iter_step scp s b f (-1) (k+1) (Znth k s).
Proof.
  intros. split.
  - unfold step_any. split; [lia|]. split; [lia|]. split.
    + right. exists k. split; [lia|]. split; [lia|]. auto.
    + intro Hr. rewrite Hr in H2. contradiction.
  - intro Hs. destruct (H1 Hs) as [-> ->]. unfold step_exact. right; right.
    split; [lia|]. auto.
Qed.

Lemma iter_C: forall scp s b f,
  -1 <= b < f -> f <= Zlength s -> (scp = nullval -> b = -1 /\ f = Zlength s) ->
  iter_step scp s b f (-1) (Zlength s) nullval.
Proof.
  intros. split.
  - unfold step_any. split; [lia|]. split; [lia|]. split; auto.
  - intro Hs. destruct (H1 Hs) as [-> ->]. unfold step_exact. left.
    repeat split; auto.
Qed.

Lemma init_D: forall scp s b f b' f' r,
  -1 <= b < f -> f <= Zlength s ->
  ((s = [] /\ b = -1 /\ f = 0) \/ (0 <= b /\ f = b+1)) ->
  iter_step scp s b f b' f' r -> init_window scp s b' f' r.
Proof.
  intros scp s b f b' f' r Hb Hf Hc [[Hb' [Hf' [Hr Hrn]]] Hex].
  unfold init_window. split; [lia|]. split; [lia|]. split.
  { destruct Hr as [Hr|[c [? [? ?]]]]; [left; auto| right; exists c; split; [lia|auto]]. }
  split; auto.
  intro Hs. specialize (Hex Hs). unfold step_exact in Hex.
  destruct Hex as [[? [? [? [? ?]]]] | [[? [? [? ?]]] | [? [? [? ?]]]]].
  - left. destruct Hc as [[? [? ?]]|[? ?]]; [|lia].
    split; auto. split; auto. lia.
  - right. exists b. destruct Hc as [[? [? ?]]|[? ?]]; [lia|].
    split; [lia|]. split; auto. lia.
  - right. exists f. destruct Hc as [[? [? ?]]|[? ?]].
    { subst s. rewrite Zlength_nil in *; lia. }
    split; [lia|]. split; auto. lia.
Qed.

(* contents after add: node j gets prev = e, node j-1 gets next = e *)
Definition upd2 (vs: list node_v) (j: Z) (e: val) : list node_v :=
  upd_Znth (j-1)
    (upd_Znth j vs (pay (Znth j vs), (nxt (Znth j vs), e)))
    (pay (Znth (j-1) vs), (e, prv (Znth (j-1) vs))).

Lemma Zlength_upd2: forall vs j e, Zlength (upd2 vs j e) = Zlength vs.
Proof. intros. unfold upd2. list_solve. Qed.

Lemma Znth_upd2: forall vs j e i, 0 <= i < Zlength vs ->
  Znth i (upd2 vs j e) =
  if zeq i (j-1) then (pay (Znth i vs), (e, prv (Znth i vs)))
  else if zeq i j then (pay (Znth i vs), (nxt (Znth i vs), e))
  else Znth i vs.
Proof.
  intros. unfold upd2.
  destruct (zeq i (j-1)); [|destruct (zeq i j)].
  - subst i. list_solve.
  - subst i. list_solve.
  - list_solve.
Qed.

Lemma nodes_upd2: forall sh s vs j e lo hi,
  (hi <= j-1 \/ j < lo) ->
  nodes sh s (upd2 vs j e) lo hi = nodes sh s vs lo hi.
Proof.
  intros. unfold upd2. rewrite nodes_upd by lia. rewrite nodes_upd by lia. auto.
Qed.

Ltac if_cases :=
  repeat match goal with
  | |- context [if zlt ?a ?b then _ else _] => destruct (zlt a b)
  | |- context [if zeq ?a ?b then _ else _] => destruct (zeq a b)
  end.

Lemma add_whole: forall s vs j e ev,
  0 <= j <= Zlength s -> whole s vs ->
  whole (ins j e s) (ins j (ev, (Znth_or_null s j, Znth_or_null s (j-1))) (upd2 vs j e)) /\
  map pay (ins j (ev, (Znth_or_null s j, Znth_or_null s (j-1))) (upd2 vs j e)) =
  ins j ev (map pay vs).
Proof.
  intros s vs j e ev Hj [Hlen [Hp Hn]].
  assert (L2: Zlength (upd2 vs j e) = Zlength s) by (rewrite Zlength_upd2; lia).
  split; [split; [|split]|].
  - rewrite !Zlength_ins by lia. lia.
  - intros i Hi. rewrite Zlength_ins in Hi by lia.
    unfold prev_links, prv in *.
    rewrite Znth_ins by lia. rewrite Znth_or_null_ins by lia.
    if_cases; try lia; simpl; auto.
    + rewrite Znth_upd2 by lia. if_cases; try lia; simpl; apply Hp; lia.
    + subst. auto.
    + rewrite Znth_upd2 by lia. if_cases; try lia; simpl; auto.
    + rewrite Znth_upd2 by lia. if_cases; try lia; simpl; apply Hp; lia.
  - intros i Hi. rewrite Zlength_ins in Hi by lia.
    unfold next_links, nxt in *.
    rewrite Znth_ins by lia. rewrite Znth_or_null_ins by lia.
    if_cases; try lia; simpl; auto.
    all: try (rewrite Znth_upd2 by lia; if_cases; try lia; simpl).
    all: unfold nxt in *.
    all: first [ reflexivity | (apply Hn; lia) | (rewrite Hn by lia; f_equal; lia)
               | (subst; f_equal; lia) ].
  - rewrite map_ins by lia. simpl. f_equal.
    apply Znth_eq_ext. { rewrite !Zlength_map. lia. }
    intros i Hi. rewrite Zlength_map in Hi.
    rewrite !Znth_map by lia. rewrite Znth_upd2 by lia.
    if_cases; reflexivity.
Qed.

Section Proofs.
Variable Rc : globals -> val -> mpred.

Lemma body_get_first :
  semax_body Vprog (Gprog Rc) f_sglib_dllist_get_first get_first_spec.
Proof.
  start_function.
  rename H into Hat, H0 into Hlen, H1 into Hprev.
  destruct Hat as [[-> ->] | Hj].
  - rewrite Znth_or_null_out by (rewrite Zlength_nil; lia).
    forward.
    forward_if (PROP () LOCAL (temp __dll_ nullval)
                SEP (nodes sh [] vs 0 (Z.min (0 + 1) (Zlength (@nil val))))).
    + discriminate.
    + forward. entailer!.
    + forward. forward. Exists nullval. entailer!.
  - rewrite Znth_or_null_in by lia.
    replace (Z.min (j+1) (Zlength s)) with (j+1) in * by lia.
    assert_PROP (forall i, 0 <= i < j+1 -> isptr (Znth i s)) as Hptr.
    { sep_apply nodes_isptr. entailer!. }
    forward.
    forward_if (EX r:val, PROP (r = nullval \/ In r s) LOCAL (temp __dll_ r)
                SEP (nodes sh s vs 0 (j+1))).
    + rewrite (nodes_focus sh s vs 0 j (j+1)) by lia. entailer!.
    + forward_loop
        (EX k:Z, PROP (0<=k<=j) LOCAL (temp __dll_ (Znth k s)) SEP (nodes sh s vs 0 (j+1)))
      continue:
        (EX k:Z, PROP (1<=k<=j) LOCAL (temp __dll_ (Znth k s)) SEP (nodes sh s vs 0 (j+1)))
      break:
        (EX r:val, PROP (r = nullval \/ In r s) LOCAL (temp __dll_ r)
         SEP (nodes sh s vs 0 (j+1))).
      * Exists j. entailer!.
      * Intros k.
        assert (Hpk: prv (Znth k vs) = Znth_or_null s (k-1)) by (apply Hprev; lia).
        rewrite (nodes_focus sh s vs 0 k (j+1)) by lia. Intros.
        destruct (Znth k vs) as [pk [nk qk]] eqn:Ek. unfold prv in Hpk; simpl in Hpk.
        destruct (zeq k 0).
        -- subst k. rewrite Znth_or_null_out in Hpk by lia. subst qk.
           forward.
           forward_if.
           { first [discriminate | contradiction | congruence]. }
           forward. Exists (Znth 0 s).
           rewrite (nodes_focus sh s vs 0 0 (j+1)) by lia. rewrite Ek.
           entailer!. right. apply Znth_In. lia.
        -- rewrite Znth_or_null_in in Hpk by lia. subst qk.
           forward. { assert (isptr (Znth (k-1) s)) by (apply Hptr; lia). entailer!; try (apply isptr_is_pointer_or_null; auto). }
           forward_if.
           { rewrite (nodes_focus sh s vs 0 (k-1) k) by lia. entailer!. }
           { forward. Exists k.
             rewrite (nodes_focus sh s vs 0 k (j+1)) by lia. rewrite Ek.
             entailer!. }
           { assert (isptr (Znth (k-1) s)) by (apply Hptr; lia).
             destruct (Znth (k-1) s); try contradiction; discriminate. }
      * Intros k.
        assert (Hpk: prv (Znth k vs) = Znth_or_null s (k-1)) by (apply Hprev; lia).
        rewrite (nodes_focus sh s vs 0 k (j+1)) by lia. Intros.
        destruct (Znth k vs) as [pk [nk qk]] eqn:Ek. unfold prv in Hpk; simpl in Hpk.
        rewrite Znth_or_null_in in Hpk by lia. subst qk.
        forward. { assert (isptr (Znth (k-1) s)) by (apply Hptr; lia). entailer!; try (apply isptr_is_pointer_or_null; auto). } Exists (k-1).
        rewrite (nodes_focus sh s vs 0 k (j+1)) by lia. rewrite Ek.
        entailer!.
      * Intros r. Exists r. entailer!.
    + assert (isptr (Znth j s)) by (apply Hptr; lia).
      assert (Hn: Znth j s = nullval) by exact H. rewrite Hn in H0. contradiction.
    + Intros r. forward. forward. Exists r. entailer!. replace (Z.min (j+1) (Zlength s)) with (j+1) by lia. auto.
Qed.

Lemma body_get_last :
  semax_body Vprog (Gprog Rc) f_sglib_dllist_get_last get_last_spec.
Proof.
  start_function.
  rename H into Hat, H0 into Hlen, H1 into Hnext.
  destruct Hat as [[-> ->] | Hj].
  - rewrite Znth_or_null_out by (rewrite Zlength_nil; lia).
    forward.
    forward_if (PROP () LOCAL (temp __dll_ nullval)
                SEP (nodes sh [] vs 0 (Zlength (@nil val)))).
    + discriminate.
    + forward. entailer!.
    + forward. forward. Exists nullval. entailer!.
  - rewrite Znth_or_null_in by lia.
    assert_PROP (forall i, j <= i < Zlength s -> isptr (Znth i s)) as Hptr.
    { sep_apply nodes_isptr. entailer!. }
    forward.
    forward_if (EX r:val, PROP (r = nullval \/ In r s) LOCAL (temp __dll_ r)
                SEP (nodes sh s vs j (Zlength s))).
    + rewrite (nodes_focus sh s vs j j (Zlength s)) by lia. entailer!.
    + forward_loop
        (EX k:Z, PROP (j<=k<Zlength s) LOCAL (temp __dll_ (Znth k s))
         SEP (nodes sh s vs j (Zlength s)))
      continue:
        (EX k:Z, PROP (j<=k<Zlength s - 1) LOCAL (temp __dll_ (Znth k s))
         SEP (nodes sh s vs j (Zlength s)))
      break:
        (EX r:val, PROP (r = nullval \/ In r s) LOCAL (temp __dll_ r)
         SEP (nodes sh s vs j (Zlength s))).
      * Exists j. entailer!.
      * Intros k.
        assert (Hpk: nxt (Znth k vs) = Znth_or_null s (k+1)) by (apply Hnext; lia).
        rewrite (nodes_focus sh s vs j k (Zlength s)) by lia. Intros.
        destruct (Znth k vs) as [pk [nk qk]] eqn:Ek. unfold nxt in Hpk; simpl in Hpk.
        destruct (zeq k (Zlength s - 1)).
        -- rewrite Znth_or_null_out in Hpk by lia. subst nk.
           forward.
           forward_if.
           { first [discriminate | contradiction | congruence]. }
           forward. Exists (Znth k s).
           rewrite (nodes_focus sh s vs j k (Zlength s)) by lia. rewrite Ek.
           entailer!. right. apply Znth_In. lia.
        -- rewrite Znth_or_null_in in Hpk by lia. subst nk.
           forward. { assert (isptr (Znth (k+1) s)) by (apply Hptr; lia). entailer!; try (apply isptr_is_pointer_or_null; auto). }
           forward_if.
           { rewrite (nodes_focus sh s vs (k+1) (k+1) (Zlength s)) by lia. entailer!. }
           { forward. Exists k.
             rewrite (nodes_focus sh s vs j k (Zlength s)) by lia. rewrite Ek.
             entailer!. }
           { assert (isptr (Znth (k+1) s)) by (apply Hptr; lia).
             destruct (Znth (k+1) s); try contradiction; discriminate. }
      * Intros k.
        assert (Hpk: nxt (Znth k vs) = Znth_or_null s (k+1)) by (apply Hnext; lia).
        rewrite (nodes_focus sh s vs j k (Zlength s)) by lia. Intros.
        destruct (Znth k vs) as [pk [nk qk]] eqn:Ek. unfold nxt in Hpk; simpl in Hpk.
        rewrite Znth_or_null_in in Hpk by lia. subst nk.
        forward. { assert (isptr (Znth (k+1) s)) by (apply Hptr; lia). entailer!; try (apply isptr_is_pointer_or_null; auto). } Exists (k+1).
        rewrite (nodes_focus sh s vs j k (Zlength s)) by lia. rewrite Ek.
        entailer!.
      * Intros r. Exists r. entailer!.
    + assert (isptr (Znth j s)) by (apply Hptr; lia).
      assert (Hn: Znth j s = nullval) by exact H. rewrite Hn in H0. contradiction.
    + Intros r. forward. forward. Exists r. entailer!.
Qed.

Opaque Znth_or_null.

Ltac scp_tc Rc scp :=
  destruct (Val.eq scp nullval);
  [ subst; entailer!
  | unfold cmp_env; rewrite if_false by auto; Intros;
    sep_apply (func_ptr'_isptr (cmp_spec Rc scp) scp); Intros;
    entailer!; destruct scp; try contradiction; simpl; auto ].

Ltac scp_cmp_tc :=
  match goal with |- context [cmp_env ?Rc ?scp _ _ _] =>
  destruct (Val.eq scp nullval);
  [ subst; entailer!
  | unfold cmp_env; rewrite if_false by auto; entailer! ] end.

Lemma body_it_next :
  semax_body Vprog (Gprog Rc) f_sglib_dllist_it_next (it_next_spec Rc).
Proof.
  start_function.
  rename H into Hlen, H0 into Hb, H1 into Hf, H2 into Hprev, H3 into Hnext,
         H4 into Hcp0, H5 into Hcp1.
  unfold it_rep. Intros cur.
  assert_PROP (forall i, 0 <= i < b+1 -> isptr (Znth i s)) as Hp0.
  { sep_apply (nodes_isptr shl s vs 0 (b+1)). entailer!. }
  assert_PROP (forall i, f <= i < Zlength s -> isptr (Znth i s)) as Hp1.
  { sep_apply (nodes_isptr shl s vs f (Zlength s)). entailer!. }
  forward.
  { entailer!. apply (Znth_or_null_pn _ _ _ _ Hp0); lia. }
  forward.
  forward.
  { scp_tc Rc scp. }
  forward_if (EX k:Z, PROP (-1 <= k <= b; (scp = nullval -> k = b))
      LOCAL (temp _ce (Znth_or_null s k); gvars gv; temp _it it)
      SEP (data_at sh t_it (cur, (nullval, (Znth_or_null s f, (scp, eqp)))) it;
           nodes shl s vs 0 (b + 1); nodes shl s vs f (Zlength s);
           cmp_env Rc scp eqp sheq veq; cmp_state Rc gv scp))%assert.
  { scp_cmp_tc. }
  { (* with a comparator: search backwards *)
    unfold cmp_env, cmp_state. rewrite !if_false by auto. Intros.
    forward.
    forward.
    forward_loop
     (EX k:Z, PROP (-1 <= k <= b)
      LOCAL (temp _ce (Znth_or_null s k); temp _eq eqp; temp _scp scp;
             gvars gv; temp _it it)
      SEP (data_at sh t_it (cur, (nullval, (Znth_or_null s f, (scp, eqp)))) it;
           nodes shl s vs 0 (b + 1); nodes shl s vs f (Zlength s);
           func_ptr' (cmp_spec Rc scp) scp; data_at sheq t_dl veq eqp; Rc gv scp))%assert
    break:
     (EX k:Z, PROP (-1 <= k <= b; scp = nullval -> k = b)
      LOCAL (temp _ce (Znth_or_null s k); gvars gv; temp _it it)
      SEP (data_at sh t_it (cur, (nullval, (Znth_or_null s f, (scp, eqp)))) it;
           nodes shl s vs 0 (b + 1); nodes shl s vs f (Zlength s);
           cmp_env Rc scp eqp sheq veq; cmp_state Rc gv scp))%assert.
    - Exists b. entailer!.
    - Intros k.
      forward_if.
      + destruct (zlt k 0).
        * rewrite (Znth_or_null_out s k) by lia. entailer!.
        * rewrite (Znth_or_null_in s k) by lia.
          rewrite (nodes_focus shl s vs 0 k (b+1)) by lia. entailer!.
      + assert (Hk: 0 <= k).
        { destruct (zlt k 0); [|lia]. rewrite (Znth_or_null_out s k) in * by lia.
          exfalso; congruence. }
        rewrite (Znth_or_null_in s k) by lia.
        rewrite (nodes_focus shl s vs 0 k (b+1)) by lia. Intros.
        assert (Hint: int_val (pay (Znth k vs))).
        { destruct Hcp0 as [?|Hi]; [contradiction|apply Hi; lia]. }
        forward_call (gv, sheq, shl, eqp, Znth k s, veq, Znth k vs).
        Intros r.
        forward_if.
        * forward. Exists k. unfold cmp_env, cmp_state. rewrite !if_false by auto.
          rewrite (Znth_or_null_in s k) by lia.
          rewrite (nodes_focus shl s vs 0 k (b+1)) by lia.
          entailer!.
        * assert (Hpk: prv (Znth k vs) = Znth_or_null s (k-1)) by (apply Hprev; lia).
          destruct (Znth k vs) as [pk [nk qk]] eqn:Ek.
          unfold prv in Hpk; simpl in Hpk. subst qk.
          forward.
          { entailer!. apply (Znth_or_null_pn _ _ _ _ Hp0); lia. }
          Exists (k-1).
          rewrite (nodes_focus shl s vs 0 k (b+1)) by lia. rewrite Ek.
          entailer!.
      + forward. Exists k. unfold cmp_env, cmp_state. rewrite !if_false by auto.
        entailer!.
  }
  { forward. Exists b. entailer!. }
  Intros k.
  forward_if (EX b':Z, EX f':Z, EX r:val,
      PROP (iter_step scp s b f b' f' r)
      LOCAL (temp _ce r; temp _it it)
      SEP (data_at sh t_it (cur, (Znth_or_null s b', (Znth_or_null s f', (scp, eqp)))) it;
           nodes shl s vs 0 (b + 1); nodes shl s vs f (Zlength s);
           cmp_env Rc scp eqp sheq veq; cmp_state Rc gv scp))%assert.
  { destruct (zlt k 0).
    - rewrite (Znth_or_null_out s k) by lia. entailer!.
    - rewrite (Znth_or_null_in s k) by lia.
      rewrite (nodes_focus shl s vs 0 k (b+1)) by lia. entailer!. }
  { (* found at k, going backwards *)
    assert (Hk: 0 <= k).
    { destruct (zlt k 0); [|lia]. rewrite (Znth_or_null_out s k) in * by lia.
      exfalso; congruence. }
    rewrite (Znth_or_null_in s k) by lia.
    assert (Hpk: prv (Znth k vs) = Znth_or_null s (k-1)) by (apply Hprev; lia).
    rewrite (nodes_focus shl s vs 0 k (b+1)) by lia. Intros.
    destruct (Znth k vs) as [pk [nk qk]] eqn:Ek.
    unfold prv in Hpk; simpl in Hpk. subst qk.
    forward.
    { entailer!. apply (Znth_or_null_pn _ _ _ _ Hp0); lia. }
    forward.
    Exists (k-1) f (Znth k s).
    rewrite (nodes_focus shl s vs 0 k (b+1)) by lia. rewrite Ek.
    entailer!.
    apply iter_A; auto; try lia; apply Hp0; lia. }
  { (* nothing behind: go forwards *)
    assert (Hk: k = -1).
    { destruct (zlt k 0); [lia|].
      rewrite (Znth_or_null_in s k) in * by lia.
      assert (isptr (Znth k s)) by (apply Hp0; lia).
      match goal with Hn: Znth k s = nullval |- _ => rewrite Hn in *; contradiction end. }
    subst k.
    forward.
    { entailer!. apply (Znth_or_null_pn _ _ _ _ Hp1); lia. }
    forward.
    forward.
    { scp_tc Rc scp. }
    forward_if (EX k2:Z, PROP (f <= k2 <= Zlength s; scp = nullval -> k2 = f)
      LOCAL (temp _ce (Znth_or_null s k2); gvars gv; temp _it it)
      SEP (data_at sh t_it (cur, (nullval, (nullval, (scp, eqp)))) it;
           nodes shl s vs 0 (b + 1); nodes shl s vs f (Zlength s);
           cmp_env Rc scp eqp sheq veq; cmp_state Rc gv scp))%assert.
    { scp_cmp_tc. }
    { unfold cmp_env, cmp_state. rewrite !if_false by auto. Intros.
      forward.
      forward.
      forward_loop
       (EX k2:Z, PROP (f <= k2 <= Zlength s)
        LOCAL (temp _ce (Znth_or_null s k2); temp _eq eqp; temp _scp scp;
               gvars gv; temp _it it)
        SEP (data_at sh t_it (cur, (nullval, (nullval, (scp, eqp)))) it;
             nodes shl s vs 0 (b + 1); nodes shl s vs f (Zlength s);
             func_ptr' (cmp_spec Rc scp) scp; data_at sheq t_dl veq eqp; Rc gv scp))%assert
      break:
       (EX k2:Z, PROP (f <= k2 <= Zlength s; scp = nullval -> k2 = f)
        LOCAL (temp _ce (Znth_or_null s k2); gvars gv; temp _it it)
        SEP (data_at sh t_it (cur, (nullval, (nullval, (scp, eqp)))) it;
             nodes shl s vs 0 (b + 1); nodes shl s vs f (Zlength s);
             cmp_env Rc scp eqp sheq veq; cmp_state Rc gv scp))%assert.
      - Exists f. entailer!.
      - Intros k2.
        forward_if.
        + destruct (zlt k2 (Zlength s)).
          * rewrite (Znth_or_null_in s k2) by lia.
            rewrite (nodes_focus shl s vs f k2 (Zlength s)) by lia. entailer!.
          * rewrite (Znth_or_null_out s k2) by lia. entailer!.
        + assert (Hk: k2 < Zlength s).
          { destruct (zlt k2 (Zlength s)); [lia|].
            rewrite (Znth_or_null_out s k2) in * by lia.
            exfalso; congruence. }
          rewrite (Znth_or_null_in s k2) by lia.
          rewrite (nodes_focus shl s vs f k2 (Zlength s)) by lia. Intros.
          assert (Hint: int_val (pay (Znth k2 vs))).
          { destruct Hcp1 as [?|Hi]; [contradiction|apply Hi; lia]. }
          forward_call (gv, shl, sheq, Znth k2 s, eqp, Znth k2 vs, veq).
          Intros r.
          forward_if.
          * forward. Exists k2. unfold cmp_env, cmp_state. rewrite !if_false by auto.
            rewrite (Znth_or_null_in s k2) by lia.
            rewrite (nodes_focus shl s vs f k2 (Zlength s)) by lia.
            entailer!.
          * assert (Hpk: nxt (Znth k2 vs) = Znth_or_null s (k2+1)) by (apply Hnext; lia).
            destruct (Znth k2 vs) as [pk [nk qk]] eqn:Ek.
            unfold nxt in Hpk; simpl in Hpk. subst nk.
            forward.
            { entailer!. apply (Znth_or_null_pn _ _ _ _ Hp1); lia. }
            Exists (k2+1).
            rewrite (nodes_focus shl s vs f k2 (Zlength s)) by lia. rewrite Ek.
            entailer!.
        + forward. Exists k2. unfold cmp_env, cmp_state. rewrite !if_false by auto.
          entailer!.
    }
    { forward. Exists f. entailer!. }
    Intros k2.
    forward_if.
    { destruct (zlt k2 (Zlength s)).
      - rewrite (Znth_or_null_in s k2) by lia.
        rewrite (nodes_focus shl s vs f k2 (Zlength s)) by lia. entailer!.
      - rewrite (Znth_or_null_out s k2) by lia. entailer!. }
    { assert (Hk: k2 < Zlength s).
      { destruct (zlt k2 (Zlength s)); [lia|].
        rewrite (Znth_or_null_out s k2) in * by lia.
        exfalso; congruence. }
      rewrite (Znth_or_null_in s k2) by lia.
      assert (Hpk: nxt (Znth k2 vs) = Znth_or_null s (k2+1)) by (apply Hnext; lia).
      rewrite (nodes_focus shl s vs f k2 (Zlength s)) by lia. Intros.
      destruct (Znth k2 vs) as [pk [nk qk]] eqn:Ek.
      unfold nxt in Hpk; simpl in Hpk. subst nk.
      forward.
      { entailer!. apply (Znth_or_null_pn _ _ _ _ Hp1); lia. }
      forward.
      Exists (-1) (k2+1) (Znth k2 s).
      rewrite (nodes_focus shl s vs f k2 (Zlength s)) by lia. rewrite Ek.
      rewrite (Znth_or_null_out s (-1)) by lia.
      entailer!.
      apply iter_B; try lia.
      all: try (apply Hp1; lia).
      intro Hs; split; [| auto].
      match goal with Hx: scp = nullval -> -1 = b |- _ => rewrite <- (Hx Hs); auto end. }
    { assert (Hk: k2 = Zlength s).
      { destruct (zlt k2 (Zlength s)); [|lia].
        rewrite (Znth_or_null_in s k2) in * by lia.
        assert (isptr (Znth k2 s)) by (apply Hp1; lia).
        match goal with Hn: Znth k2 s = nullval |- _ => rewrite Hn in *; contradiction end. }
      subst k2.
      forward.
      Exists (-1) (Zlength s) nullval.
      rewrite (Znth_or_null_out s (-1)) by lia.
      rewrite (Znth_or_null_out s (Zlength s)) by lia.
      entailer!.
      apply iter_C; try lia.
      intro Hs; split.
      - match goal with Hx: scp = nullval -> -1 = b |- _ => rewrite <- (Hx Hs); auto end.
      - match goal with Hx: scp = nullval -> Zlength s = f |- _ => rewrite (Hx Hs); auto end. }
  }
  Intros b' f' r.
  forward.
  forward.
  Exists b' f' r. unfold it_rep. Exists r. entailer!.
Qed.


Lemma body_it_init_on_equal :
  semax_body Vprog (Gprog Rc) f_sglib_dllist_it_init_on_equal (it_init_on_equal_spec Rc).
Proof.
  start_function.
  rename H into Hat, H0 into Hlen, H1 into Hprev, H2 into Hnext, H3 into Hcp.
  assert_PROP (forall i, 0 <= i < Zlength s -> isptr (Znth i s)) as Hp.
  { sep_apply (nodes_isptr shl s vs 0 (Zlength s)). entailer!. }
  forward. forward. forward. forward.
  destruct Hat as [[-> ->] | Hj].
  - rewrite (Znth_or_null_out [] 0) by (rewrite Zlength_nil; lia).
    forward_if (PROP () LOCAL (temp _it it; gvars gv)
       SEP (data_at sh t_it (Vundef, (nullval, (nullval, (scp, eqp)))) it;
            nodes shl [] vs 0 (Zlength (@nil val));
            cmp_env Rc scp eqp sheq veq; cmp_state Rc gv scp))%assert.
    + exfalso; congruence.
    + forward. entailer!.
    + forward_call (gv, sh, it, shl, @nil val, vs, -1, 0, scp, eqp, sheq, veq).
      { unfold it_rep. Exists Vundef.
        rewrite (Znth_or_null_out [] (-1)) by (rewrite Zlength_nil; lia).
        rewrite (Znth_or_null_out [] 0) by (rewrite Zlength_nil; lia).
        replace (-1+1) with 0 by lia.
        rewrite (nodes_empty shl [] vs 0 0) by lia. cancel. }
      Intros vret. destruct vret as [[b' f'] r]. simpl fst in *. simpl snd in *.
      forward.
      Exists b' f' r.
      entailer!.
      apply (init_D scp [] (-1) 0 b' f' r); auto.
      all: try (left; repeat split; reflexivity).
      all: try list_solve.
  - rewrite (Znth_or_null_in s j) by lia.
    replace (Z.min (j+1) (Zlength s)) with (j+1) in Hprev by lia.
    assert (Hpj: nxt (Znth j vs) = Znth_or_null s (j+1)) by (apply Hnext; lia).
    forward_if (PROP () LOCAL (temp _it it; gvars gv)
       SEP (data_at sh t_it (Vundef, (Znth j s, (Znth_or_null s (j+1), (scp, eqp)))) it;
            nodes shl s vs 0 (Zlength s);
            cmp_env Rc scp eqp sheq veq; cmp_state Rc gv scp))%assert.
    + rewrite (nodes_focus shl s vs 0 j (Zlength s)) by lia. entailer!.
    + rewrite (nodes_focus shl s vs 0 j (Zlength s)) by lia. Intros.
      destruct (Znth j vs) as [pj [nj qj]] eqn:Ej. unfold nxt in Hpj; simpl in Hpj. subst nj.
      forward. { entailer!. apply (Znth_or_null_pn _ _ _ _ Hp); lia. }
      forward.
      rewrite (nodes_focus shl s vs 0 j (Zlength s)) by lia. rewrite Ej.
      entailer!.
    + assert (isptr (Znth j s)) by (apply Hp; lia).
      match goal with Hn: ?x = nullval |- _ =>
        change x with (Znth j s) in Hn; rewrite Hn in *; contradiction end.
    + rewrite (nodes_split shl s vs 0 (j+1) (Zlength s)) by lia.
      forward_call (gv, sh, it, shl, s, vs, j, j+1, scp, eqp, sheq, veq).
      { unfold it_rep. Exists Vundef. rewrite (Znth_or_null_in s j) by lia. cancel. }
      { repeat split; auto; try lia.
        all: try (eapply next_links_sub; eauto; lia).
        all: try (eapply cmp_payloads_sub; eauto; lia). }
      Intros vret. destruct vret as [[b' f'] r]. simpl fst in *. simpl snd in *.
      forward.
      Exists b' f' r.
      rewrite (nodes_split shl s vs 0 (j+1) (Zlength s)) by lia.
      entailer!.
      apply (init_D scp s j (j+1) b' f' r); auto; try lia.
Qed.

Lemma body_it_init :
  semax_body Vprog (Gprog Rc) f_sglib_dllist_it_init it_init_spec.
Proof.
  start_function.
  apply semax_pre with (EX gv: globals,
    PROP () LOCAL (gvars gv; temp _it it; temp _list (Znth_or_null s j))
    SEP (data_at_ sh t_it it; nodes shl s vs 0 (Zlength s);
         cmp_env Rc nullval nullval Share.top (Vundef, (Vundef, Vundef));
         cmp_state Rc gv nullval))%assert.
  { go_lowerx. apply exp_right with (globals_of_env rho).
    unfold cmp_env, cmp_state. rewrite !if_true by auto.
    entailer!. }
  Intros gv.
  forward_call (gv, sh, it, shl, s, vs, j, nullval, nullval, Share.top,
                (Vundef, (Vundef, Vundef))).
  { repeat split; auto. left; auto. }
  Intros vret. destruct vret as [[b f] r]. simpl fst in *. simpl snd in *.
  forward.
  Exists b f r.
  entailer!.
Qed.


Lemma body_add :
  semax_body Vprog (Gprog Rc) f_sglib_dllist_add add_spec.
Proof.
  start_function.
  rename H into Hat, H0 into Hwh.
  assert (Hwh' := Hwh). destruct Hwh' as [Hlen [Hprev Hnext]].
  assert (Hj: 0 <= j <= Zlength s).
  { destruct Hat as [[-> ->]|?]; [rewrite Zlength_nil; lia | lia]. }
  destruct (add_whole s vs j e ev Hj Hwh) as [Hw' Hm'].
  assert (L2: Zlength (upd2 vs j e) = Zlength s) by (rewrite Zlength_upd2; lia).
  assert_PROP (forall i, 0 <= i < Zlength s -> isptr (Znth i s)) as Hp.
  { sep_apply (nodes_isptr sh s vs 0 (Zlength s)). entailer!. }
  forward.
  { entailer!. apply (Znth_or_null_pn _ _ _ _ Hp); lia. }
  forward_if (EX p: val,
    PROP () LOCAL (temp _list lp; temp _elem e)
    SEP (data_at shl (tptr t_dl) p lp;
         nodes sh (ins j e s)
           (ins j (ev, (Znth_or_null s j, Znth_or_null s (j-1))) (upd2 vs j e))
           0 (Zlength s + 1)))%assert.
  - destruct Hat as [[-> ->]|Hj'].
    + rewrite (Znth_or_null_out [] 0) by list_solve. entailer!.
    + rewrite (Znth_or_null_in s j) by lia.
      rewrite (nodes_focus sh s vs 0 j (Zlength s)) by lia. entailer!.
  - (* empty list *)
    destruct Hat as [[-> ->]|Hj'].
    2:{ rewrite (Znth_or_null_in s j) in * by lia.
        assert (isptr (Znth j s)) by (apply Hp; lia).
        match goal with Hn: ?x = nullval |- _ =>
          change x with (Znth j s) in Hn; rewrite Hn in *; contradiction end. }
    forward. forward. forward. forward. forward. forward.
    Exists e.
    rewrite (nodes_ins sh [] (upd2 vs 0 e) 0 e) by (rewrite ?L2; list_solve).
    rewrite (Znth_or_null_out [] 0) by list_solve.
    rewrite (Znth_or_null_out [] (0-1)) by list_solve.
    rewrite !nodes_empty by list_solve.
    entailer!.
  - (* nonempty list *)
    destruct Hat as [[-> ->]|Hj'].
    { rewrite (Znth_or_null_out [] 0) in * by list_solve. exfalso; congruence. }
    rewrite (Znth_or_null_in s j) by lia.
    assert (Hpj: prv (Znth j vs) = Znth_or_null s (j-1)) by (apply Hprev; lia).
    assert (Hnj: nxt (Znth j vs) = Znth_or_null s (j+1)) by (apply Hnext; lia).
    rewrite (nodes_focus sh s vs 0 j (Zlength s)) by lia. Intros.
    destruct (Znth j vs) as [pj [nj qj]] eqn:Ej.
    unfold prv, nxt in Hpj, Hnj; simpl in Hpj, Hnj. subst qj nj.
    forward. forward. forward. forward.
    { entailer!. apply (Znth_or_null_pn _ _ _ _ Hp); lia. }
    forward. forward. forward. forward.
    destruct (zeq j 0).
    + rewrite (Znth_or_null_out s (j-1)) by lia.
      forward_if.
      { exfalso; congruence. }
      forward.
      Exists (Znth j s).
      rewrite (nodes_ins sh s (upd2 vs j e) j e) by lia.
      rewrite (Znth_or_null_in s j) by lia.
      rewrite (Znth_or_null_out s (j-1)) by lia.
      rewrite (nodes_focus sh s (upd2 vs j e) j j (Zlength s)) by lia.
      rewrite Znth_upd2 by lia. rewrite Ej.
      destruct (zeq j (j-1)); [lia|]. destruct (zeq j j); [|lia].
      rewrite (nodes_upd2 sh s vs j e (j+1) (Zlength s)) by lia.
      rewrite !nodes_empty by lia.
      cbn [pay nxt prv fst snd]. entailer!.
    + rewrite (Znth_or_null_in s (j-1)) by lia.
      assert (Hnq: nxt (Znth (j-1) vs) = Znth_or_null s (j-1+1)) by (apply Hnext; lia).
      replace (j-1+1) with j in Hnq by lia.
      rewrite (Znth_or_null_in s j) in Hnq by lia.
      rewrite (nodes_focus sh s vs 0 (j-1) j) by lia. Intros.
      destruct (Znth (j-1) vs) as [pq [nq qq]] eqn:Eq.
      unfold nxt in Hnq; simpl in Hnq. subst nq.
      forward_if.
      { forward. forward.
        Exists (Znth j s).
        rewrite (nodes_ins sh s (upd2 vs j e) j e) by lia.
        rewrite (Znth_or_null_in s j) by lia.
        rewrite (Znth_or_null_in s (j-1)) by lia.
        rewrite (nodes_focus sh s (upd2 vs j e) j j (Zlength s)) by lia.
        rewrite (nodes_focus sh s (upd2 vs j e) 0 (j-1) j) by lia.
        rewrite !Znth_upd2 by lia. rewrite Ej, Eq.
        destruct (zeq j (j-1)); [lia|]. destruct (zeq j j); [|lia].
        destruct (zeq (j-1) (j-1)); [|lia].
        rewrite (nodes_upd2 sh s vs j e (j+1) (Zlength s)) by lia.
        rewrite (nodes_upd2 sh s vs j e 0 (j-1)) by lia.
        replace (j-1+1) with j by lia.
        rewrite (nodes_empty sh s vs j j) by lia. rewrite (nodes_empty sh s (upd2 vs j e) j j) by lia.
        cbn [pay nxt prv fst snd]. entailer!. }
      { assert (isptr (Znth (j-1) s)) by (apply Hp; lia).
        match goal with Hn: ?x = nullval |- _ =>
          change x with (Znth (j-1) s) in Hn; rewrite Hn in *; contradiction end. }
  - Intros p.
    forward.
    Exists (ins j (ev, (Znth_or_null s j, Znth_or_null s (j-1))) (upd2 vs j e)).
    entailer!.
Qed.

End Proofs.
