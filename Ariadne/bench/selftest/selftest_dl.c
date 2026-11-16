/* sglib's self-test as a client of B1's public contracts (plan Q12).

   ../sglib/selftest.c is included unmodified.  Its doubly linked list
   instantiation is SGLIB_DEFINE_DL_LIST_FUNCTIONS(DoubleLinkedList,
   myListCmp, previous, next), where DoubleLinkedList is a typedef of
   struct MyIntList.  B1's public spec template is instantiated at the
   same parameters below, after the functions it specifies: Frama-C
   merges a contract on a later prototype into the function's
   definition, so E-ACSL checks every call.

   Only the public part of the template is used (SGLIB_DL_LIST_SPEC and
   the SGLIB_DL_LIST_CONTRACT_* macros); there are no proof annotations
   to check here.  The six specified functions are the ones B1 verifies;
   the other sglib functions the test calls have no contract.

   Ours, around the included file: selftest.c's malloc/free go through
   st_malloc/st_free, which keep the allocation registry that gives the
   liveness model (heap, dead) its runtime meaning (../../rac/rac_rt.c,
   as B1's allocators do), and main runs double_linked_list_test once
   with a fixed seed instead of selftest.c's main (argument 1: the seed;
   argument 2: `zero`, `probe` or `probefull`, the diagnostics of
   rac.sh). */

#include <stddef.h>
#include <stdlib.h>
#include "ariadne_alloc.h"
#include "sglib_dl_list_spec.h"
#include "rac_rt.h"

void *st_malloc(size_t n);
void st_free(void *p);

#define malloc(n) st_malloc(n)
#define free(p) st_free(p)
#define main sglib_selftest_main
#include "selftest.c"
#undef main
#undef malloc
#undef free

/*@ // The fields myListCmp reads (template parameter cmp_reads).
    predicate st_cmp_reads{L}(DoubleLinkedList *p) = \initialized(&p->n);
    SGLIB_DL_LIST_SPEC(DoubleLinkedList, previous, next, st_cmp_reads)
*/

/*@ SGLIB_DL_LIST_CONTRACT_COMPARATOR(DoubleLinkedList, st_cmp_reads,
                                      e1, e2) */
int myListCmp(struct MyIntList *e1, struct MyIntList *e2);

/*@ SGLIB_DL_LIST_CONTRACT_ADD(DoubleLinkedList, previous, next) */
void sglib_DoubleLinkedList_add(DoubleLinkedList **list,
                                DoubleLinkedList *elem);

/*@ SGLIB_DL_LIST_CONTRACT_GET_FIRST(DoubleLinkedList, previous, next) */
DoubleLinkedList *sglib_DoubleLinkedList_get_first(DoubleLinkedList *list);

/*@ SGLIB_DL_LIST_CONTRACT_GET_LAST(DoubleLinkedList, previous, next) */
DoubleLinkedList *sglib_DoubleLinkedList_get_last(DoubleLinkedList *list);

/*@ SGLIB_DL_LIST_CONTRACT_IT_INIT_ON_EQUAL(DoubleLinkedList, previous,
                                            next, st_cmp_reads,
                                            (1, myListCmp)) */
DoubleLinkedList *sglib_DoubleLinkedList_it_init_on_equal(
    struct sglib_DoubleLinkedList_iterator *it, DoubleLinkedList *list,
    int (*subcomparator)(DoubleLinkedList *, DoubleLinkedList *),
    DoubleLinkedList *equalto);

/*@ SGLIB_DL_LIST_CONTRACT_IT_INIT(DoubleLinkedList, previous, next) */
DoubleLinkedList *sglib_DoubleLinkedList_it_init(
    struct sglib_DoubleLinkedList_iterator *it, DoubleLinkedList *list);

/*@ SGLIB_DL_LIST_CONTRACT_IT_NEXT(DoubleLinkedList, previous, next,
                                    (1, myListCmp)) */
DoubleLinkedList *sglib_DoubleLinkedList_it_next(
    struct sglib_DoubleLinkedList_iterator *it);

/* malloc/free with the allocation registry.  A node's padding is written,
   so that \initialized of a whole node means "every field written", as
   in WP's model (no padding), like B1's allocator; the fields stay
   uninitialised, except in the diagnostic run (second argument `zero`),
   where every byte of a node is written (zero) here, so that all_init
   holds of every node and the other failures show. */
static int st_zero_nodes;

/* ST_WP_ONLY: the WP run on the comparator (rac.sh) leaves the allocator
   bodies out, since -ariadne refuses raw malloc/free calls. */
#ifndef ST_WP_ONLY

void *st_malloc(size_t n) {
  void *p = malloc(n);
  if (p) {
    if (n == sizeof(struct MyIntList) && st_zero_nodes)
      memset(p, 0, n);
    else if (n == sizeof(struct MyIntList)) {
      struct MyIntList *q = p;
      for (size_t k = offsetof(struct MyIntList, n) + sizeof q->n;
           k < offsetof(struct MyIntList, next); k++)
        ((char *)p)[k] = 0;
      for (size_t k = offsetof(struct MyIntList, color) + sizeof q->color;
           k < offsetof(struct MyIntList, left_ptr); k++)
        ((char *)p)[k] = 0;
    }
    rac_reg_alloc(p, n);
  }
  return p;
}

void st_free(void *p) {
  if (p) {
    rac_reg_free(p);
#ifdef RAC_KEEP_FREED   /* E-ACSL build: as ../b1/rac/rac_alloc.c */
    rac_keep_freed = 1;
#else
    free(p);
#endif
  }
}

#endif

/* Random operation sequences over the specified API (rac.sh, mode
   `ops`): several lists, `add` at any node, get_first / get_last from any
   node, iteration from any node with and without myListCmp (partial or
   complete), reverse (no contract: a state change between checked calls)
   and frees, the whole list at once while iterating (as B1's driver
   does).  Every call meets the contracts' preconditions by construction;
   the contracts are what E-ACSL checks.  The lists are kept as arrays of
   their nodes (membership only: any node is a valid start). */
#define ST_LISTS 3
#define ST_MAXN 48

static unsigned long st_rng;
static unsigned st_rand(unsigned n) {
  st_rng = st_rng * 6364136223846793005UL + 1442695040888963407UL;
  return (unsigned)(st_rng >> 33) % n;
}

static DoubleLinkedList *st_any(DoubleLinkedList **nodes, int len) {
  return len ? nodes[st_rand(len)] : NULL;
}

static void st_free_all(DoubleLinkedList **nodes, int *len) {
  struct sglib_DoubleLinkedList_iterator it;
  DoubleLinkedList *l;
  for (l = sglib_DoubleLinkedList_it_init(&it, st_any(nodes, *len));
       l != NULL; l = sglib_DoubleLinkedList_it_next(&it))
    st_free(l);
  *len = 0;
}

static unsigned long st_ops(unsigned seed, int nops) {
  static DoubleLinkedList *nodes[ST_LISTS][ST_MAXN];
  int len[ST_LISTS] = {0};
  struct sglib_DoubleLinkedList_iterator it;
  DoubleLinkedList te, *l, *h;
  unsigned long sum = 0;
  st_rng = seed;
  for (int op = 0; op < nops; op++) {
    int k = (int)st_rand(ST_LISTS);
    switch (st_rand(9)) {
    case 0: case 1: case 2:   /* add before any node (or to an empty list) */
      if (len[k] < ST_MAXN) {
        DoubleLinkedList *e = st_malloc(sizeof(struct MyIntList));
        if (!e)
          break;
        e->n = st_rand(6);
        h = st_any(nodes[k], len[k]);
        sglib_DoubleLinkedList_add(&h, e);
        nodes[k][len[k]++] = e;
      }
      break;
    case 3:
      l = sglib_DoubleLinkedList_get_first(st_any(nodes[k], len[k]));
      sum += l ? l->n : 0;
      break;
    case 4:
      l = sglib_DoubleLinkedList_get_last(st_any(nodes[k], len[k]));
      sum += l ? l->n : 0;
      break;
    case 5: {                 /* iterate from any node, maybe partly */
      int steps = (int)st_rand(len[k] + 2);
      for (l = sglib_DoubleLinkedList_it_init(&it, st_any(nodes[k], len[k]));
           l != NULL && steps-- > 0; l = sglib_DoubleLinkedList_it_next(&it))
        sum += l->n;
      break;
    }
    case 6: {                 /* iterate over the nodes equal to te */
      te.n = st_rand(6);
      int with_cmp = st_rand(2);
      for (l = sglib_DoubleLinkedList_it_init_on_equal(
               &it, st_any(nodes[k], len[k]), with_cmp ? myListCmp : NULL,
               with_cmp ? &te : NULL);
           l != NULL; l = sglib_DoubleLinkedList_it_next(&it))
        sum += l->n;
      break;
    }
    case 7:                   /* reverse: a state change, not specified */
      if (len[k]) {
        h = st_any(nodes[k], len[k]);
        sglib_DoubleLinkedList_reverse(&h);
      }
      break;
    case 8:                   /* free the whole list while iterating */
      if (st_rand(3) == 0)
        st_free_all(nodes[k], &len[k]);
      break;
    }
  }
  for (int k = 0; k < ST_LISTS; k++)
    st_free_all(nodes[k], &len[k]);
  return sum;
}

int main(int argc, char **argv) {
  srandom(argc > 1 ? (unsigned)atoi(argv[1]) : 1);
  st_zero_nodes = argc > 2 && strcmp(argv[2], "zero") == 0;
  if (argc > 2 && strcmp(argv[2], "ops") == 0) {
    unsigned long sum = st_ops((unsigned)(argc > 1 ? atoi(argv[1]) : 1),
                               argc > 3 ? atoi(argv[3]) : 400);
    printf("ops: done (checksum %lu)\n", sum);
    return 0;
  }
  /* Probes (rac.sh): one add of a fresh node to an empty list, with only
     n written, as the self-test does (`probe`), or every field
     (`probefull`). */
  if (argc > 2 && strncmp(argv[2], "probe", 5) == 0) {
    DoubleLinkedList *l = NULL, *e = st_malloc(sizeof(struct MyIntList));
    e->n = 1;
    if (strcmp(argv[2], "probefull") == 0) {
      e->color = 0;
      e->left_ptr = e->right_ptr = NULL;
    }
    fprintf(stderr, "probe: add 1\n");
    sglib_DoubleLinkedList_add(&l, e);
    fprintf(stderr, "probe: done\n");
    return 0;
  }
  double_linked_list_test();
  return 0;
}
