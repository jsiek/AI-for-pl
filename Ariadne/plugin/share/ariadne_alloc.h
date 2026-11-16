/* Ariadne ghost liveness model (plan §10, fallback 1; m1a/README.md).

   Trusted specification: part of the frozen, human-reviewed spec.
   The ariadne plugin (-ariadne) adds
     - `assert live: !dead(__heap, \base_addr(&lv));` before every memory
       access that RTE checks, and
     - `admit stack: !heap(\base_addr(&x));` for every address-taken
       variable x,
   and rejects any remaining call to malloc/calloc/realloc/free.

   Declare one allocator pair per allocated type T:

     /@ ARIADNE_ALLOC @/ T *ariadne_alloc_T(void);
     /@ ARIADNE_FREE  @/ void ariadne_free_T(T *p);

   (with the usual comment delimiters).  The contracts mention only
   \result, p and __heap, so the same text serves every type. */

#ifndef ARIADNE_ALLOC_H
#define ARIADNE_ALLOC_H

//@ ghost int __heap;

/*@ axiomatic Ariadne_liveness {
      // b is the base of a block returned by an ariadne allocator.
      predicate heap(char *b);
      // block b is freed in heap version v.
      predicate dead(integer v, char *b);
      // Only heap blocks can be dead.  Consistent: dead = \false is a model.
      axiom dead_heap: \forall integer v, char *b; dead(v, b) ==> heap(b);
    }
*/

#define ARIADNE_ALLOC \
  assigns __heap; \
  ensures fresh_or_null: \result == \null || \
    (\valid(\result) && \offset(\result) == 0 \
     && heap(\base_addr(\result)) && !dead(__heap, \base_addr(\result))); \
  ensures distinct: \result == \null || \forall char *b; \
    heap(b) && !dead(\old(__heap), b) ==> b != \base_addr(\result); \
  ensures frame: \forall char *b; \result == \null || \
    b != \base_addr(\result) ==> (dead(__heap, b) <==> dead(\old(__heap), b));

#define ARIADNE_FREE \
  requires freeable: p == \null || \
    (heap(\base_addr(p)) && \offset(p) == 0 && !dead(__heap, \base_addr(p))); \
  assigns __heap; \
  ensures freed: p != \null ==> dead(__heap, \base_addr(p)); \
  ensures frame: \forall char *b; b != \base_addr(p) ==> \
    (dead(__heap, b) <==> dead(\old(__heap), b));

#endif
