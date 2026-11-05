intros t a h l.
pose proof (length_cons a l) as LC.
pose proof (length_pos l) as LP.
split.
- intros [Ha Hl] i H0 H1.
  destruct (nth_cons i a l) as [E1 E2]; [lia|].
  destruct (Z.eq_dec i 0) as [Hz|Hz].
  + rewrite (E1 Hz). exact Ha.
  + rewrite (E2 Hz). apply Hl; lia.
- intros H. split.
  + specialize (H 0%Z (Z.le_refl _) ltac:(lia)).
    destruct (nth_cons 0%Z a l) as [E1 E2]; [lia|].
    rewrite (E1 eq_refl) in H. exact H.
  + intros i H0 H1.
    specialize (H (i+1)%Z ltac:(lia) ltac:(lia)).
    destruct (nth_cons (i+1)%Z a l) as [E1 E2]; [lia|].
    rewrite (E2 ltac:(lia)) in H.
    replace (i+1-1)%Z with i in H by lia. exact H.
