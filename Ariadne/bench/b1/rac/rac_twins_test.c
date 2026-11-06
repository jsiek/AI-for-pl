/* Unit tests of the generated twins (gen_twins.py on b1.c) on
   well-formed and corrupt heaps (run under ASan + UBSan by check.sh):
   every call must return, with the value the ACSL definition gives, and
   must not read freed memory. */
#include <stdio.h>
#include <stdlib.h>
#include "b1_types.h"
#include "rac_twins.h"

dllist *ariadne_alloc_dllist(void);
void ariadne_free_dllist(dllist *p);

/* Typed views of the builtins (which take and return long). */
typedef long seq;
static seq reach(dllist *h) { return rac_dll_s_of_h(h); }
static seq cons(dllist *h, seq t) { return rac_cons(h, t); }
static int dll(dllist *p, dllist *h, seq s) {
  return rac_dll(p, h, s);
}
static dllist *head(dllist *x) { return (dllist *)rac_dll_h_of_member(x); }
static dllist *prev(dllist *x) { return (dllist *)rac_dll_prev_of_h(x); }
static dllist *first(seq s) { return (dllist *)rac_dll_h_of_s(s); }
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
      CHECK(head(v[n - 1]) == h);                /* h from a member */
      CHECK(prev(v[n - 1]) == (n > 1 ? v[n - 2] : NULL));
      CHECK(nth(s, n - 1) == v[n - 1]);
      CHECK(dll(v[0], v[0]->ptr_to_next, rac_tail(s)));  /* the rest */
      CHECK(first(s) == h);
      if (n > 1)
        CHECK((dllist *)rac_dll_prev_of_s(rac_tail(s)) == v[0]);
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
  /* cycle through the back links: the member walk must stop */
  v[3]->ptr_to_next = NULL;
  v[0]->ptr_to_previous = v[3];
  CHECK(head(v[2]) == NULL);
  v[0]->ptr_to_previous = NULL;
  /* broken back link */
  v[2]->ptr_to_previous = v[0];
  CHECK(!dll(NULL, h, reach(h)));
  /* the iterator's witness from v[2] (member walk, then forward): the
     walk skips v[1], the list it gives fails dll, so iter_at fails */
  CHECK(head(v[2]) == h && !dll(NULL, h, reach(head(v[2]))));
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

  /* rac_index (the iterator's witnesses b and f) */
  h = build(4, v);
  seq s4 = reach(h);
  CHECK(rac_index(s4, v[0]) == 0 && rac_index(s4, v[3]) == 3);
  CHECK(rac_index(s4, &failures) == -1);
  CHECK(rac_index(0, v[0]) == -1);
  /* a back-link cycle not through the head, and a self loop: the member
     walk stops on the repeated node (not only by fuel) */
  v[1]->ptr_to_previous = v[3];
  CHECK(head(v[2]) == NULL);
  v[1]->ptr_to_previous = v[1];
  CHECK(head(v[2]) == NULL && head(v[1]) == NULL);
  v[1]->ptr_to_previous = v[0];
  CHECK(head(v[3]) == h);
  /* freed nodes kept (the E-ACSL builds, RAC_KEEP_FREED): as in the
     ghost model, the shape still holds and the walks go through them
     (the memory is not released here: the block is only marked dead);
     liveness is the registry's (rac_dead) */
  rac_reg_free(v[0]);
  rac_reg_free(v[1]);
  CHECK(!dll(NULL, h, reach(h)) && head(v[3]) == NULL);  /* not kept */
  rac_keep_freed = 1;
  CHECK(dll(NULL, h, reach(h)) && head(v[3]) == h);
  CHECK(rac_length(reach(head(v[2]))) == 4);
  CHECK(rac_dead((char *)v[0]) && !rac_dead((char *)v[2]));
  rac_keep_freed = 0;
  free(v[0]);
  free(v[1]);
  ariadne_free_dllist(v[2]);
  ariadne_free_dllist(v[3]);
  rac_reset();
  printf("twin unit tests: %s\n", failures ? "FAIL" : "ok");
  return failures != 0;
}
