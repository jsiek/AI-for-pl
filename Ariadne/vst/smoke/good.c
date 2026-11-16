/* VST smoke test, good case: allocate a list cell, write, read, free.
   Mirrors the good_* cases of Ariadne/m1a/alloc.c. */
#include <stdlib.h>

struct cell {
  int value;
  struct cell *next;
};

int use_cell(void) {
  struct cell *p = (struct cell *) malloc(sizeof(struct cell));
  if (!p) return 0;
  p->value = 1;
  p->next = NULL;
  int r = p->value;
  free(p);
  return r;
}

int main(void) {
  return use_cell();
}
