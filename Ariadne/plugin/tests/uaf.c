/* Plugin test: the m1a/ghost.c cases with no hand-written instrumentation.
   Every `live` assert and `stack` admit comes from -ariadne.

   good_*     every goal proved;
   bad_*      a goal on the line marked BAD fails, all others proved;
   vacuous_*  the `assert vacuity: \false` is not proved. */

#include "ariadne_alloc.h"

struct node { int v; struct node *next; };

/*@ ARIADNE_ALLOC */ int *ariadne_alloc_int(void);
/*@ ARIADNE_FREE */ void ariadne_free_int(int *p);
/*@ ARIADNE_ALLOC */ struct node *ariadne_alloc_node(void);
/*@ ARIADNE_FREE */ void ariadne_free_node(struct node *p);

int global_counter;

int good_malloc_write_free(void) {
  int *p = ariadne_alloc_int();
  if (!p) return 0;
  *p = 1;
  int r = *p;
  ariadne_free_int(p);
  return r;
}

int good_two_blocks_free_one(void) {
  int *p = ariadne_alloc_int();
  if (!p) return 0;
  int *q = ariadne_alloc_int();
  if (!q) { ariadne_free_int(p); return 0; }
  *q = 2;
  ariadne_free_int(p);
  int r = *q;
  ariadne_free_int(q);
  return r;
}

int good_stack_pointer_after_free(void) {
  int x = 0;
  int *h = ariadne_alloc_int();
  ariadne_free_int(h);
  int *p = &x;
  *p = 1;
  return x;
}

int good_global_pointer(void) {
  int *p = &global_counter;
  int *h = ariadne_alloc_int();
  ariadne_free_int(h);
  *p = 1;
  return global_counter;
}

int good_nested_block_local(int c) {
  int r = 0;
  if (c) {
    int y = 3;
    int *p = &y;
    r = *p;
  }
  return r;
}

/*@ requires \valid(out);
    requires !dead(__heap, \base_addr(out));
    assigns *out;
*/
void write_through(int *out) {
  *out = 5;
}

int good_formal_and_call(void) {
  int x = 0;
  write_through(&x);
  return x;
}

int good_local_array(void) {
  int a[3] = { 0, 1, 2 };
  int *p = a;
  int *h = ariadne_alloc_int();
  ariadne_free_int(h);
  return p[1];
}

int good_field_address(void) {
  struct node s;
  s.v = 0;
  int *p = &s.v;
  *p = 4;
  return s.v;
}

int bad_use_after_free(void) {
  int *p = ariadne_alloc_int();
  if (!p) return 0;
  *p = 1;
  ariadne_free_int(p);
  return *p;                       /* BAD: read of freed block */
}

int bad_alias_after_free(void) {
  int *p = ariadne_alloc_int();
  if (!p) return 0;
  int *q = p;
  ariadne_free_int(p);
  return *q;                       /* BAD: read through alias */
}

int bad_double_free(void) {
  int *p = ariadne_alloc_int();
  if (!p) return 0;
  ariadne_free_int(p);
  ariadne_free_int(p);             /* BAD: freeable precondition */
  return 0;
}

int bad_free_stack(void) {
  int x = 0;
  ariadne_free_int(&x);            /* BAD: freeable precondition */
  return x;
}

int bad_free_interior(void) {
  int *p = ariadne_alloc_int();
  if (!p) return 0;
  ariadne_free_int(p + 1);         /* BAD: freeable precondition */
  return 0;
}

int bad_list_link_after_free(void) {
  struct node *a = ariadne_alloc_node();
  if (!a) return 0;
  struct node *b = ariadne_alloc_node();
  if (!b) { ariadne_free_node(a); return 0; }
  b->v = 7;
  a->next = b;
  ariadne_free_node(b);
  int r = a->next->v;              /* BAD: freed node via a link */
  ariadne_free_node(a);
  return r;
}

int bad_pass_freed_to_callee(void) {
  int *p = ariadne_alloc_int();
  if (!p) return 0;
  ariadne_free_int(p);
  write_through(p);                /* BAD: callee requires live block */
  return 0;
}

int vacuous_after_alloc(void) {
  int *p = ariadne_alloc_int();
  if (!p) return 0;
  //@ assert vacuity: \false;
  ariadne_free_int(p);
  return 0;
}

int vacuous_after_free_with_stack(void) {
  int x = 0;
  int *p = &x;
  int *h = ariadne_alloc_int();
  ariadne_free_int(h);
  *p = 1;
  //@ assert vacuity: \false;
  return x;
}
