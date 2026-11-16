/* Input to gen.sh: the sglib instantiation used by benchmark B1, taken
   from sglib's samples/dllist.c (type, comparator, link field names). */

#include "sglib.h"

typedef struct dllist {
  int i;
  struct dllist *ptr_to_next;
  struct dllist *ptr_to_previous;
} dllist;

#define DLLIST_COMPARATOR(e1, e2) ((e1->i > e2->i) - (e1->i < e2->i))

SGLIB_DEFINE_DL_LIST_PROTOTYPES(dllist, DLLIST_COMPARATOR, ptr_to_previous,
                                ptr_to_next);
SGLIB_DEFINE_DL_LIST_FUNCTIONS(dllist, DLLIST_COMPARATOR, ptr_to_previous,
                               ptr_to_next);
