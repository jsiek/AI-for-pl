/* Runtime-checking replacement for ../../../plugin/share/ariadne_alloc.h
   (gen_rac.py substitutes it for that #include in b1_rac.c).

   The ghost liveness model becomes an allocation registry kept by the
   allocators (rac_alloc.c) and queried by the twins rac_heap / rac_dead
   (README, "Liveness").  The allocator contracts keep their executable
   clauses; `distinct` and both `frame` clauses quantify over every
   address (\forall char *b) and are left out, as is `freed`, whose
   \base_addr(p) is evaluated on a freed pointer. */
#ifndef RAC_H
#define RAC_H

#include "rac_twins.h"

//@ ghost int __heap;

#define ARIADNE_ALLOC \
  ensures fresh_or_null: \result == \null || \
    (\valid(\result) && \offset(\result) == 0 \
     && heap(\base_addr(\result)) && !dead(__heap, \base_addr(\result)));

#define ARIADNE_FREE \
  requires freeable: p == \null || \
    (\valid(p) && \offset(p) == 0 && heap(\base_addr(p)) \
     && !dead(__heap, \base_addr(p)));

#endif
