/* Unit tests of the twins on well-formed and corrupt heaps (run under
   ASan + UBSan by check.sh): every call must return, with the value the
   ACSL definition gives, and must not read freed memory. */
#include <stdio.h>
#include <stdlib.h>
#include "b1_types.h"
#include "rac_twins.h"

dllist *ariadne_alloc_dllist(void);
void ariadne_free_dllist(dllist *p);

/* Typed views of the builtins (which take and return long). */
typedef long seq;
static seq reach(dllist *h) { return rac_reach(h); }
static seq cons(dllist *h, seq t) { return rac_cons(h, t); }
static int dll(dllist *p, dllist *h, seq s) {
  return rac_dll(p, h, s);
}
static dllist *head(dllist *x) { return (dllist *)rac_head(x); }
static dllist *prev(dllist *x) { return (dllist *)rac_prev(x); }
static dllist *nth(seq s, long k) { return (dllist *)rac_nth(s, k); }

static int failures;
#define CHECK(c) \
  do { if (!(c)) { failures++; printf("FAIL line %d: %s\n", __LINE__, #c); } } while (0)

/* A well-formed list of n nodes; nodes[k] is node k. */
static dllist *build(int n, dllist **nodes) {
  for (int k = 0; k < n; k++) {
    nodes[k] = ariadne_alloc_dllist();
    nodes[k]->i = k;
  }
  for (int k = 0; k < n; k++) {
    nodes[k]->ptr_to_previous = k ? nodes[k - 1] : NULL;
    nodes[k]->ptr_to_next = k + 1 < n ? nodes[k + 1] : NULL;
  }
  return n ? nodes[0] : NULL;
}

int main(void) {
  dllist *v[8];
  for (int n = 0; n <= 5; n++) {
    dllist *h = build(n, v);
    seq s = reach(h);
    CHECK(rac_length(s) == n);
    CHECK(dll(NULL, h, s));
    CHECK(!dll(NULL, h, cons(h, s)));        /* wrong list */
    if (n) {
      CHECK(head(v[n - 1]) == h);                /* W4 */
      CHECK(prev(v[n - 1]) == (n > 1 ? v[n - 2] : NULL));
      CHECK(nth(s, n - 1) == v[n - 1]);
      CHECK(dll(v[0], v[0]->ptr_to_next, rac_tail(s)));  /* the rest */
      CHECK(!dll(v[0], h, s));                   /* wrong prev */
    }
    for (int k = 0; k < n; k++)
      ariadne_free_dllist(v[k]);
    rac_reset();
  }
  /* cycle: last->next = first; the walk must stop and fail */
  dllist *h = build(4, v);
  v[3]->ptr_to_next = v[0];
  CHECK(!dll(NULL, h, reach(h)));
  CHECK(rac_length(reach(h)) == 0);
  /* cycle through the back links: rac_head must stop */
  v[3]->ptr_to_next = NULL;
  v[0]->ptr_to_previous = v[3];
  CHECK(head(v[2]) == NULL);
  v[0]->ptr_to_previous = NULL;
  /* broken back link */
  v[2]->ptr_to_previous = v[0];
  CHECK(!dll(NULL, h, reach(h)));
  v[2]->ptr_to_previous = v[1];
  /* a repeated node in an explicit list */
  CHECK(!dll(NULL, v[3], cons(v[3], cons(v[3], 0))));
  /* a freed node in the middle: no witness, and no read of freed memory */
  CHECK(dll(NULL, h, reach(h)));
  ariadne_free_dllist(v[2]);
  CHECK(rac_dead((char *)v[2]) && rac_heap((char *)v[2]));
  CHECK(!dll(NULL, h, reach(h)));
  CHECK(head(v[3]) == NULL);
  CHECK(prev(v[2]) == NULL);
  CHECK(!rac_heap((char *)&failures));
  for (int k = 0; k < 4; k++)
    if (k != 2)
      ariadne_free_dllist(v[k]);
  rac_reset();
  printf("twin unit tests: %s\n", failures ? "FAIL" : "ok");
  return failures != 0;
}
