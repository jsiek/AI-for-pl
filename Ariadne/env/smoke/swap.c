/* M0 smoke test: RTE + contract goals (SMT) and one lemma that needs
   induction (Coq). */

/*@ logic integer sum(integer n) = n <= 0 ? 0 : sum(n - 1) + n;

    lemma sum_nonneg: \forall integer n; sum(n) >= 0;
*/

/*@ requires \valid(p) && \valid(q) && \separated(p, q);
    assigns *p, *q;
    ensures *p == \old(*q) && *q == \old(*p);
*/
void swap(int *p, int *q) {
  int t = *p;
  *p = *q;
  *q = t;
}
