/* VST smoke test, bad cases: each function has one memory error, on
   the line marked BAD.  Mirrors the bad_* cases of
   Ariadne/m1a/alloc.c. */
#include <stdlib.h>

struct cell {
  int value;
  struct cell *next;
};

int use_after_free(void) {
  struct cell *p = (struct cell *) malloc(sizeof(struct cell));
  if (!p) return 0;
  p->value = 1;
  p->next = NULL;
  free(p);
  return p->value;               /* BAD: read after free */
}

int write_after_free_alias(void) {
  struct cell *p = (struct cell *) malloc(sizeof(struct cell));
  struct cell *q;
  if (!p) return 0;
  q = p;
  free(p);
  q->value = 2;                  /* BAD: write through alias */
  return 0;
}

int double_free(void) {
  struct cell *p = (struct cell *) malloc(sizeof(struct cell));
  if (!p) return 0;
  free(p);
  free(p);                       /* BAD: double free */
  return 0;
}
