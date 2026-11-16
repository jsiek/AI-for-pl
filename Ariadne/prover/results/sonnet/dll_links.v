intros t t1 a i a1 l x a2 Hi Hx H.
subst x a2. revert i Hi Hx.
induction H as [M P prev | M P prev h s Hn Hp Hm Hv H IH]; intros i Hi Hx.
- pose proof (@length_nil addr) as Hl. rewrite Hl in Hx. lia.
- pose proof (length_cons h s) as Hc. pose proof (length_pos s) as Hs.
  rewrite Hc in Hx.
  destruct (Z.eq_dec i 0) as [E|E].
  + subst i. destruct (nth_cons 0%Z h s) as [N1 N2]; [lia|].
    rewrite (N1 eq_refl).
    repeat split.
    * intro Q. apply Hn. symmetry. exact Q.
    * intro Le. 
      destruct (nth_cons 1%Z h s) as [M1 M2]; [lia|].
      replace (1%Z + 0)%Z with 1%Z by lia.
      rewrite (M2 ltac:(lia)). replace (1 - 1)%Z with 0%Z by lia.
      destruct s as [|h' s'].
      -- exfalso. rewrite length_cons, (@length_nil addr) in Le. lia.
      -- inversion H as [|M0 P0 pr hh ss Hn0 Hp0 Hm0 Hv0 H0 E1 E2]; subst.
         destruct (nth_cons 0%Z (P (shift h 1)) s') as [K1 K2]; [pose proof (length_pos s'); lia|].
         rewrite (K1 eq_refl). reflexivity.
    * intro Le. destruct s as [|h' s'].
      -- inversion H; subst. reflexivity.
      -- exfalso. apply Le. pose proof (length_pos s'). rewrite length_cons, length_cons. lia.
    * intros _. exact Hp.
    * intro Q. exfalso. apply Q. reflexivity.
  + destruct (nth_cons i h s) as [N1 N2]; [lia|].
    rewrite (N2 E).
    destruct (IH (i - 1)%Z ltac:(lia) ltac:(lia)) as [[A [B C]] [D F]].
    repeat split.
    * exact A.
    * intro Le. rewrite B by lia.
      destruct (nth_cons (1 + i)%Z h s) as [M1 M2]; [lia|].
      rewrite (M2 ltac:(lia)). f_equal. lia.
    * intro Le. apply C. lia.
    * intro Q. exfalso. apply E. exact Q.
    * intros _.
      destruct (Z.eq_dec (i - 1) 0) as [E2|E2].
      -- rewrite (D E2).
         destruct (nth_cons ((-1%Z)%Z + i)%Z h s) as [M1 M2]; [lia|].
         rewrite (M1 ltac:(lia)). reflexivity.
      -- rewrite (F E2).
         destruct (nth_cons ((-1%Z)%Z + i)%Z h s) as [M1 M2]; [lia|].
         rewrite (M2 ltac:(lia)). f_equal. lia.
