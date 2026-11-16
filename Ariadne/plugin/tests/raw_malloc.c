/* Plugin test: -ariadne must refuse raw allocation calls, including the
   initializer form `T *p = malloc(...)` that CIL keeps as Local_init. */

#include <stdlib.h>
#include "ariadne_alloc.h"

int raw(void) {
  int *p = malloc(sizeof(int));
  if (!p) return 0;
  *p = 1;
  free(p);
  return 0;
}

void *(*alloc_ptr)(unsigned long) = malloc;

int through_pointer(void) {
  void (*release)(void *) = free;
  int *p = alloc_ptr(sizeof(int));
  release(p);
  return 0;
}
