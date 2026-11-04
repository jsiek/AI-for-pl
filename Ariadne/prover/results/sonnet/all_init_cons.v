unfold P_all_init.
split.
- intros [H1 H2] i Hi0 Hi1.
  rewrite length_cons in Hi1.
  pose proof (length_pos l) as Hl.
  destruct (nth_cons i a l) as [E1 E2]; [lia|].
  destruct (Z.eq_dec i 0) as [->|Hne].
  + rewrite (E1 eq_refl). exact H1.
  + rewrite (E2 Hne). apply H2; lia.
- intros H. split.
  + pose proof (length_pos l) as Hl.
    specialize (H 0%Z ltac:(lia) ltac:(rewrite length_cons; lia)).
    destruct (nth_cons 0%Z a l) as [E1 E2]; [lia|].
    rewrite (E1 eq_refl) in H. exact H.
  + intros i Hi0 Hi1.
    pose proof (length_pos l) as Hl.
    specialize (H (i+1)%Z ltac:(lia) ltac:(rewrite length_cons; lia)).
    destruct (nth_cons (i+1)%Z a l) as [E1 E2]; [lia|].
    rewrite (E2 ltac:(lia)) in H.
    replace (i+1-1)%Z with i in H by lia. exact H.
