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
                                            next) */
DoubleLinkedList *sglib_DoubleLinkedList_it_init_on_equal(
    struct sglib_DoubleLinkedList_iterator *it, DoubleLinkedList *list,
    int (*subcomparator)(DoubleLinkedList *, DoubleLinkedList *),
    DoubleLinkedList *equalto);

/*@ SGLIB_DL_LIST_CONTRACT_IT_INIT(DoubleLinkedList, previous, next) */
DoubleLinkedList *sglib_DoubleLinkedList_it_init(
    struct sglib_DoubleLinkedList_iterator *it, DoubleLinkedList *list);

/*@ SGLIB_DL_LIST_CONTRACT_IT_NEXT(DoubleLinkedList, previous, next) */
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
    free(p);
  }
}

#endif

int main(int argc, char **argv) {
  srandom(argc > 1 ? (unsigned)atoi(argv[1]) : 1);
  st_zero_nodes = argc > 2 && strcmp(argv[2], "zero") == 0;
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
