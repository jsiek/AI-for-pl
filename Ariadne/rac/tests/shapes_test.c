/* Unit tests of the twins gen_twins.py generates from shapes.c, under
   ASan + UBSan (tests/check.sh): on well-formed lists and trees each twin
   gives the ACSL value; on cycles, sharing, broken links and freed nodes
   every call returns (false, or no witness) without reading freed
   memory. */
#include <stdio.h>
#include <stdlib.h>
#include "shapes.h"
#include "shapes_twins.h"

static int failures;
#define CHECK(c) \
  do { if (!(c)) { failures++; printf("FAIL line %d: %s\n", __LINE__, #c); } } while (0)

static node *alloc(int key) {
  node *p = malloc(sizeof *p);
  if (!p)
    abort();
  p->key = key;
  p->next = p->left = p->right = NULL;
  rac_reg_alloc(p, sizeof *p);
  return p;
}

static void release(node *p) {
  rac_reg_free(p);
  free(p);
}

typedef long seq;
static seq nil = 0;
static seq cons(node *h, seq t) { return rac_cons(h, t); }
static node *nth(seq s, long k) { return (node *)rac_nth(s, k); }
static seq seg(node *a, node *b) { return rac_lseg_s_of_from_to(a, b); }

/* ---- lseg ------------------------------------------------------------ */

static void test_lseg(void) {
  node *v[6];
  for (int n = 0; n <= 5; n++) {
    for (int k = 0; k < n; k++)
      v[k] = alloc(k);
    for (int k = 0; k + 1 < n; k++)
      v[k]->next = v[k + 1];
    node *h = n ? v[0] : NULL;
    seq s = seg(h, NULL);
    CHECK(rac_length(s) == n);
    CHECK(rac_lseg(h, NULL, s));
    CHECK(!rac_lseg(h, NULL, cons(h, s)));          /* wrong list */
    CHECK(rac_lseg(h, h, nil));                      /* empty segment */
    CHECK((node *)rac_lseg_to_of_from_s(h, s) == NULL);
    CHECK((node *)rac_lseg_from_of_to_s(NULL, s) == h);
    for (int k = 0; k < n; k++)
      CHECK(nth(s, k) == v[k]);
    if (n >= 3) {
      seq s2 = seg(v[0], v[2]);                      /* a proper segment */
      CHECK(rac_length(s2) == 2 && rac_lseg(v[0], v[2], s2));
      CHECK(!rac_lseg(v[0], v[2], s));
      CHECK(!rac_lseg(v[0], NULL, s2));
    }
    for (int k = 0; k < n; k++)
      release(v[k]);
    rac_reset();
  }
  /* a cycle: no segment to NULL, but the cycle minus one node is a
     segment back to its first node */
  for (int k = 0; k < 4; k++)
    v[k] = alloc(k);
  for (int k = 0; k < 4; k++)
    v[k]->next = v[(k + 1) % 4];
  seq bad = seg(v[0], NULL);
  CHECK(rac_length(bad) == 0 && bad != nil);         /* no witness */
  CHECK(!rac_lseg(v[0], NULL, bad));
  CHECK(!rac_lseg(v[0], NULL, nil));
  seq around = seg(v[1], v[0]);
  CHECK(rac_length(around) == 3 && rac_lseg(v[1], v[0], around));
  /* a repeated node in an explicit list */
  CHECK(!rac_lseg(v[0], v[2], cons(v[0], cons(v[0], nil))));
  /* a freed node in the middle */
  v[3]->next = NULL;
  CHECK(rac_lseg(v[0], NULL, seg(v[0], NULL)));
  release(v[2]);
  CHECK(rac_length(seg(v[0], NULL)) == 0);
  CHECK(!rac_lseg(v[0], NULL, cons(v[0], cons(v[1], cons(v[2],
                                                cons(v[3], nil))))));
  CHECK(rac_lseg(v[0], v[2], seg(v[0], v[2])));      /* stops before it */
  release(v[0]);
  release(v[1]);
  release(v[3]);
  rac_reset();
  /* longer than the depth bound: rejected (README, "Step bound"), and
     neither a hang nor a stack overflow */
  enum { LONG = 30000 };
  node **w = malloc(LONG * sizeof *w);
  for (int k = 0; k < LONG; k++)
    w[k] = alloc(k);
  for (int k = 0; k + 1 < LONG; k++)
    w[k]->next = w[k + 1];
  CHECK(rac_length(seg(w[0], NULL)) == 0);
  CHECK(rac_length(seg(w[LONG - 1000], NULL)) == 1000);
  for (int k = 0; k < LONG; k++)
    release(w[k]);
  free(w);
  rac_reset();
}

/* ---- tree, bst -------------------------------------------------------- */

static node *insert(node *t, int key, node **all, int *n) {
  if (!t) {
    all[*n] = alloc(key);
    return all[(*n)++];
  }
  if (key < t->key)
    t->left = insert(t->left, key, all, n);
  else
    t->right = insert(t->right, key, all, n);
  return t;
}

static void test_tree(void) {
  static const int keys[] = {50, 30, 70, 20, 40, 60, 80, 35};
  node *all[16];
  for (int m = 0; m <= 8; m++) {
    int n = 0;
    node *t = NULL;
    for (int k = 0; k < m; k++)
      t = insert(t, keys[k], all, &n);
    seq s = rac_tree_s_of_t(t);
    CHECK(rac_length(s) == m);
    CHECK(rac_tree(t, s));
    CHECK(m == 0 || nth(s, 0) == t);                 /* preorder */
    CHECK(rac_bst(t, 0, 100));
    CHECK(m < 4 || !rac_bst(t, 21, 100));            /* 20 is below 21 */
    if (m >= 2) {
      CHECK(!rac_tree(t, rac_tail(s)));              /* wrong list */
      int tmp = t->key;                              /* break the order */
      t->key = all[1]->key - 1;
      CHECK(!rac_bst(t, 0, 100));
      t->key = tmp;
    }
    for (int k = 0; k < n; k++)
      release(all[k]);
    rac_reset();
  }
  /* sharing: both children are the same node */
  node *r = alloc(1), *c = alloc(2);
  r->left = r->right = c;
  CHECK(rac_length(rac_tree_s_of_t(r)) == 3);        /* candidate ... */
  CHECK(!rac_tree(r, rac_tree_s_of_t(r)));           /* ... rejected */
  /* a cycle: a child points back to the root */
  r->right = NULL;
  c->left = r;
  CHECK(rac_length(rac_tree_s_of_t(r)) == 0);
  CHECK(!rac_tree(r, rac_tree_s_of_t(r)));
  CHECK(!rac_bst(r, 0, 100));                        /* bst has no list:
                                                        the step bound */
  /* a DAG with full sharing, 40 levels: 2^40 paths, stopped by the step
     bound */
  release(r);
  release(c);
  rac_reset();
  node *d[41];
  d[40] = NULL;
  for (int k = 39; k >= 0; k--) {
    d[k] = alloc(k);
    d[k]->left = d[k]->right = d[k + 1];
  }
  CHECK(rac_length(rac_tree_s_of_t(d[0])) == 0);
  CHECK(!rac_bst(d[0], -1000, 1000));
  /* a freed node */
  for (int k = 0; k < 40; k++)
    d[k]->right = NULL;
  CHECK(rac_tree(d[0], rac_tree_s_of_t(d[0])));      /* a path: a tree */
  release(d[20]);
  CHECK(rac_length(rac_tree_s_of_t(d[0])) == 0);
  CHECK(!rac_bst(d[0], -1000, 1000));
  CHECK(rac_length(rac_tree_s_of_t(d[21])) == 19);
  for (int k = 0; k < 40; k++)
    if (k != 20)
      release(d[k]);
  rac_reset();
}

int main(void) {
  test_lseg();
  test_tree();
  printf("shapes twin unit tests: %s\n", failures ? "FAIL" : "ok");
  return failures != 0;
}
