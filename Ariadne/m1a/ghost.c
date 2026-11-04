/* M1a, fallback 1 prototype: a ghost liveness model, no change to WP.

   - __heap is a ghost version counter; every malloc/free bumps it.
   - heap(b): block base b was returned by an allocator (stays true).
   - dead(v, b): block b is freed in heap version v.
   - Typed allocators (malloc_int, malloc_node) instead of malloc + cast,
     because WP's Typed model does not carry \valid through the
     void* -> T* cast.
   - Instrumentation (done by hand here; by a pass later): before every
     dereference of p, `assert live: !dead(__heap, \base_addr(p));`.

   good_* / bad_* / vacuous_* have the same meaning as in alloc.c. */

#include <stddef.h>

struct node { int v; struct node *next; };

//@ ghost int __heap;

/*@ axiomatic Liveness {
      predicate heap(char *b);
      predicate dead(integer v, char *b);
      // Only heap blocks can be dead.  Consistent: dead = \false is a model.
      axiom dead_heap: \forall integer v, char *b; dead(v, b) ==> heap(b);
    }
*/

/*@ assigns __heap;
    ensures fresh_or_null: \result == \null ||
      (\valid(\result) && \offset(\result) == 0
       && heap(\base_addr(\result)) && !dead(__heap, \base_addr(\result)));
    ensures distinct: \result == \null || \forall char *b;
      heap(b) && !dead(\old(__heap), b) ==> b != \base_addr(\result);
    ensures frame: \forall char *b; \result == \null ||
      b != \base_addr(\result) ==> (dead(__heap, b) <==> dead(\old(__heap), b));
    ensures null_frame: \result == \null ==>
      \forall char *b; dead(__heap, b) <==> dead(\old(__heap), b);
*/
int *malloc_int(void);

/*@ assigns __heap;
    ensures fresh_or_null: \result == \null ||
      (\valid(\result) && \offset(\result) == 0
       && heap(\base_addr(\result)) && !dead(__heap, \base_addr(\result)));
    ensures distinct: \result == \null || \forall char *b;
      heap(b) && !dead(\old(__heap), b) ==> b != \base_addr(\result);
    ensures frame: \forall char *b; \result == \null ||
      b != \base_addr(\result) ==> (dead(__heap, b) <==> dead(\old(__heap), b));
    ensures null_frame: \result == \null ==>
      \forall char *b; dead(__heap, b) <==> dead(\old(__heap), b);
*/
struct node *malloc_node(void);

/*@ requires freeable: p == \null ||
      (heap(\base_addr(p)) && \offset(p) == 0 && !dead(__heap, \base_addr(p)));
    assigns __heap;
    ensures freed: p != \null ==> dead(__heap, \base_addr(p));
    ensures frame: \forall char *b; b != \base_addr(p) ==>
      (dead(__heap, b) <==> dead(\old(__heap), b));
*/
void free_int(int *p);

/*@ requires freeable: p == \null ||
      (heap(\base_addr(p)) && \offset(p) == 0 && !dead(__heap, \base_addr(p)));
    assigns __heap;
    ensures freed: p != \null ==> dead(__heap, \base_addr(p));
    ensures frame: \forall char *b; b != \base_addr(p) ==>
      (dead(__heap, b) <==> dead(\old(__heap), b));
*/
void free_node(struct node *p);

int good_malloc_write_free(void) {
  int *p = malloc_int();
  if (!p) return 0;
  //@ assert live: !dead(__heap, \base_addr(p));
  *p = 1;
  //@ assert live: !dead(__heap, \base_addr(p));
  int r = *p;
  free_int(p);
  return r;
}

int good_two_blocks_free_one(void) {
  int *p = malloc_int();
  if (!p) return 0;
  int *q = malloc_int();
  if (!q) { free_int(p); return 0; }
  //@ assert live: !dead(__heap, \base_addr(q));
  *q = 2;
  free_int(p);
  //@ assert live: !dead(__heap, \base_addr(q));
  int r = *q;            /* q is still live */
  free_int(q);
  return r;
}

int good_stack_pointer(void) {
  int x = 0;
  //@ admit stack: !heap(\base_addr(&x));
  int *p = &x;
  //@ assert live: !dead(__heap, \base_addr(p));
  *p = 1;
  return x;
}

int good_stack_pointer_after_free(void) {
  int x = 0;
  //@ admit stack: !heap(\base_addr(&x));
  int *h = malloc_int();
  free_int(h);
  int *p = &x;
  //@ assert live: !dead(__heap, \base_addr(p));
  *p = 1;
  return x;
}

int bad_use_after_free(void) {
  int *p = malloc_int();
  if (!p) return 0;
  //@ assert live: !dead(__heap, \base_addr(p));
  *p = 1;
  free_int(p);
  //@ assert live_BAD: !dead(__heap, \base_addr(p));
  return *p;             /* caught by the live assert above */
}

int bad_alias_after_free(void) {
  int *p = malloc_int();
  if (!p) return 0;
  int *q = p;
  free_int(p);
  //@ assert live_BAD: !dead(__heap, \base_addr(q));
  return *q;             /* caught by the live assert above */
}

int bad_double_free(void) {
  int *p = malloc_int();
  if (!p) return 0;
  free_int(p);
  free_int(p);           /* BAD: freeable precondition */
  return 0;
}

int bad_free_stack(void) {
  int x = 0;
  free_int(&x);          /* BAD: freeable precondition */
  return x;
}

int bad_list_link_after_free(void) {
  struct node *a = malloc_node();
  if (!a) return 0;
  struct node *b = malloc_node();
  if (!b) { free_node(a); return 0; }
  //@ assert live: !dead(__heap, \base_addr(b));
  b->v = 7;
  //@ assert live: !dead(__heap, \base_addr(a));
  a->next = b;
  free_node(b);
  //@ assert live: !dead(__heap, \base_addr(a));
  struct node *c = a->next;
  //@ assert live_BAD: !dead(__heap, \base_addr(c));
  int r = c->v;          /* caught by the live assert above */
  free_node(a);
  return r;
}

int vacuous_after_malloc(void) {
  int *p = malloc_int();
  if (!p) return 0;
  //@ assert vacuity: \false;
  free_int(p);
  return 0;
}

int vacuous_after_free(void) {
  int *p = malloc_int();
  if (!p) return 0;
  free_int(p);
  //@ assert vacuity: \false;
  return 0;
}

int vacuous_after_stack_admit(void) {
  int x = 0;
  //@ admit stack: !heap(\base_addr(&x));
  int *h = malloc_int();
  free_int(h);
  //@ assert vacuity: \false;
  return x;
}
