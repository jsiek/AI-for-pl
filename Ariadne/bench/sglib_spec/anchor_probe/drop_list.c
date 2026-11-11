/* Mutant `droplist` of sglib_dllist_add (plan Q11, add's in_old_list,
   owner 2026-11-10): an add that drops the caller's list and makes elem
   a list of its own.  It meets add's public contract of 2026-11-08
   (spec_2026-11-08/): elem is in *some* whole live list, it is a head,
   and it writes only what `assigns` allows.  It does not meet the
   contract with in_old_list (../sglib_dl_list_spec.h).  run.sh checks
   both with WP, with no private annotations. */
#include <stddef.h>
#include "ariadne_alloc.h"
#include "sglib_dl_list_spec.h"

typedef struct dllist {
  int i;
  struct dllist *ptr_to_next;
  struct dllist *ptr_to_previous;
} dllist;
struct sglib_dllist_iterator {
  dllist *currentelem;
  dllist *prevelem;
  dllist *nextelem;
  int (*subcomparator)(dllist *, dllist *);
  dllist *equalto;
};

/*@ predicate dllist_cmp_reads{L}(dllist *p) = \initialized(&p->i);
    SGLIB_DL_LIST_SPEC(dllist, ptr_to_previous, ptr_to_next,
                       dllist_cmp_reads)
    // B1's lemmas (proved in ../../b1; assumed here)
    SGLIB_DL_LIST_LEMMAS(dllist, ptr_to_previous, ptr_to_next)
*/

/*@ SGLIB_DL_LIST_CONTRACT_ADD(dllist, ptr_to_previous, ptr_to_next) */
void sglib_dllist_add(dllist **list, dllist *elem) {
  elem->ptr_to_next = NULL;
  elem->ptr_to_previous = NULL;
  *list = elem;
  //@ assert single: live_dll(\null, elem, \Cons(elem, \Nil));
  //@ assert node0: elem == \nth(\Cons(elem, \Nil), 0);
}
