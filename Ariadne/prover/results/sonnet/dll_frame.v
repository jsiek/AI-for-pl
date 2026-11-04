intros t t1 t2 t3 a a1 l U H.
revert U.
induction H as [M P pv | M P pv h s Hn Hp Hm Hv H IH]; intros U.
- constructor.
- assert (Hl := length_pos s).
  assert (U0 := U 0%Z).
  assert (Hn0 := nth_cons 0%Z h s).
  cbv zeta in U0. rewrite length_cons in U0.
  destruct Hn0 as [Hn0 _]; [lia|].
  rewrite (Hn0 eq_refl) in U0.
  destruct (U0) as [[E1 E2] V]; [lia|lia|].
  constructor.
  + exact Hn.
  + rewrite E2. exact Hp.
  + exact Hm.
  + exact V.
  + rewrite E1. apply IH.
    intros i. cbv zeta. intros Hi0 Hi1.
    assert (Ui := U (i+1)%Z).
    assert (Hni := nth_cons (i+1)%Z h s).
    cbv zeta in Ui. rewrite length_cons in Ui.
    destruct Hni as [_ Hni]; [lia|].
    rewrite (Hni ltac:(lia)) in Ui.
    replace (i+1-1)%Z with i in Ui by lia.
    apply Ui; lia.
