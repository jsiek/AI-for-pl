intros a l a1.
unfold P_mem.
pose proof (length_pos l) as Hl.
pose proof (length_cons a l) as Hc.
split.
- intros [H|[i [[H1 H2] H3]]].
  + exists 0%Z. rewrite nth_zero. split; [split; [auto|lia]|lia].
  + exists (i+1)%Z.
    destruct (nth_cons (i+1) a l) as [N1 N2]; [lia|].
    rewrite (N2 ltac:(lia)).
    replace (i+1-1)%Z with i by lia.
    split; [split; [auto|lia]|lia].
- intros [i [[H1 H2] H3]].
  destruct (nth_cons i a l) as [N1 N2]; [lia|].
  destruct (Z.eq_dec i 0) as [E|E].
  + left. rewrite E, nth_zero in H1. auto.
  + right. exists (i-1)%Z. rewrite (N2 E) in H1.
    split; [split; [auto|lia]|lia].
