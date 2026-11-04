/* The ariadne allocators for runtime checking: real malloc/free, plus
   the allocation registry (rac_twins.c) that gives heap / dead their
   meaning, plus fault injection: allocation number rac_fail_at (counting
   from 0 within one b1 run) returns NULL.

   In the E-ACSL build this file is #included into b1_rac.c, so E-ACSL
   tracks the blocks (malloc/free in instrumented code); in the sanitizer
   builds it is compiled on its own. */
#include <stdlib.h>
#ifndef RAC_IN_B1          /* b1_rac.c already has the types */
#include "b1_types.h"
#endif
#include "rac_twins.h"

long rac_alloc_count = 0;
long rac_fail_at = -1;

dllist *ariadne_alloc_dllist(void) {
  if (rac_alloc_count++ == rac_fail_at)
    return NULL;
  dllist *p = malloc(sizeof(dllist));
  if (p)
    rac_reg_alloc(p);
  return p;
}

void ariadne_free_dllist(dllist *p) {
  if (p) {
    rac_reg_free(p);
    free(p);
  }
}
