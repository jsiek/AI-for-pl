/* M0 guardrail probe: a non-terminating recursive ACSL definition.  If
   WP exports it as an axiom, it is inconsistent (bad(0) = bad(0) + 1),
   so the lemma below would become provable. */

/*@ logic integer bad(integer n) = bad(n) + 1;

    lemma oops: bad(0) == 0;
*/
