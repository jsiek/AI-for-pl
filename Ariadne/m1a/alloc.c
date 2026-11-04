/* M1a: does WP (Typed model) with the Frama-C libc specs catch
   use-after-free, bad free, and double free?

   good_*  every goal should be proved.
   bad_*   exactly the goal marked BAD should stay unproved; everything
           else should be proved.
   vacuous_* an `assert \false` that must NOT be proved; if it is, the
           specs are inconsistent and every other result is meaningless. */

#include <stdlib.h>

struct node { int v; struct node *next; };

int good_malloc_write_free(void) {
  int *p = malloc(sizeof(int));
  if (!p) return 0;
  *p = 1;
  int r = *p;
  free(p);
  return r;
}

int good_free_null(void) {
  free(NULL);
  return 0;
}

int good_free_through_alias(void) {
  int *p = malloc(sizeof(int));
  if (!p) return 0;
  int *q = p;
  free(q);
  return 0;
}

int good_two_blocks_free_one(void) {
  int *p = malloc(sizeof(int));
  if (!p) return 0;
  int *q = malloc(sizeof(int));
  if (!q) { free(p); return 0; }
  *q = 2;
  free(p);
  int r = *q;            /* q is still live */
  free(q);
  return r;
}

int bad_use_after_free(void) {
  int *p = malloc(sizeof(int));
  if (!p) return 0;
  *p = 1;
  free(p);
  return *p;             /* BAD: read of freed block */
}

int bad_write_after_free(void) {
  int *p = malloc(sizeof(int));
  if (!p) return 0;
  free(p);
  *p = 1;                /* BAD: write to freed block */
  return 0;
}

int bad_alias_after_free(void) {
  int *p = malloc(sizeof(int));
  if (!p) return 0;
  int *q = p;
  free(p);
  return *q;             /* BAD: read through alias of freed block */
}

int bad_double_free(void) {
  int *p = malloc(sizeof(int));
  if (!p) return 0;
  free(p);
  free(p);               /* BAD: freeable precondition */
  return 0;
}

int bad_free_stack(void) {
  int x = 0;
  free(&x);              /* BAD: freeable precondition */
  return x;
}

int bad_free_interior(void) {
  int *p = malloc(2 * sizeof(int));
  if (!p) return 0;
  free(p + 1);           /* BAD: freeable precondition (not the base) */
  return 0;
}

int bad_list_link_after_free(void) {
  struct node *a = malloc(sizeof(struct node));
  if (!a) return 0;
  struct node *b = malloc(sizeof(struct node));
  if (!b) { free(a); return 0; }
  b->v = 7;
  a->next = b;
  free(b);
  int r = a->next->v;    /* BAD: freed node reached through a link */
  free(a);
  return r;
}

int vacuous_after_malloc(void) {
  int *p = malloc(sizeof(int));
  if (!p) return 0;
  //@ assert vacuity: \false;
  free(p);
  return 0;
}

int vacuous_after_free(void) {
  int *p = malloc(sizeof(int));
  if (!p) return 0;
  free(p);
  //@ assert vacuity: \false;
  return 0;
}
