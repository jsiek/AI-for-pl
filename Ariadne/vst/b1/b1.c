/* Benchmark B1a for VST: the same sglib code as ../../bench/b1/b1.c.
   The type definitions and the four sglib functions B1a uses are
   copied verbatim from ../../bench/b1/b1_gen.c (sglib's macros expanded
   by ../../bench/b1/gen.sh); the other generated functions are not
   called, so they are left out (VST's whole-program theorem needs every
   function in the file verified).  The driver is the same as in the
   Frama-C version, but with real malloc/free: VST models them itself,
   no ghost allocators are needed.  main runs it on a fixed input. */

#include <stddef.h>
#include <stdlib.h>

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
dllist *sglib_dllist_it_next(struct sglib_dllist_iterator *it);
void sglib_dllist_add(dllist **list, dllist *elem) {
  {
    {
      if ((*list) == NULL) {
        {
          (*list) = (elem);
          (*list)->ptr_to_next = (*list)->ptr_to_previous = NULL;
        };
      } else {
        (elem)->ptr_to_next = (*list);
        (elem)->ptr_to_previous = (*list)->ptr_to_previous;
        (*list)->ptr_to_previous = (elem);
        if ((elem)->ptr_to_previous != NULL)
          (elem)->ptr_to_previous->ptr_to_next = (elem);
      }
    }
    (*list) = (elem);
  };
}
dllist *sglib_dllist_it_init_on_equal(struct sglib_dllist_iterator *it,
                                      dllist *list,
                                      int (*subcomparator)(dllist *, dllist *),
                                      dllist *equalto) {
  it->subcomparator = subcomparator;
  it->equalto = equalto;
  it->prevelem = list;
  it->nextelem = list;
  if (list != NULL)
    it->nextelem = list->ptr_to_next;
  return (sglib_dllist_it_next(it));
}
dllist *sglib_dllist_it_init(struct sglib_dllist_iterator *it, dllist *list) {
  return (sglib_dllist_it_init_on_equal(it, list, NULL, NULL));
}
dllist *sglib_dllist_it_next(struct sglib_dllist_iterator *it) {
  dllist *ce, *eq;
  int (*scp)(dllist *, dllist *);
  ce = it->prevelem;
  it->prevelem = NULL;
  if (it->subcomparator != NULL) {
    eq = it->equalto;
    scp = it->subcomparator;
    while (ce != NULL && scp(eq, ce) != 0)
      ce = ce->ptr_to_previous;
  }
  if (ce != NULL) {
    it->prevelem = ce->ptr_to_previous;
  } else {
    ce = it->nextelem;
    it->nextelem = NULL;
    if (it->subcomparator != NULL) {
      eq = it->equalto;
      scp = it->subcomparator;
      while (ce != NULL && scp(ce, eq) != 0)
        ce = ce->ptr_to_next;
    }
    if (ce != NULL)
      it->nextelem = ce->ptr_to_next;
  }
  it->currentelem = ce;
  return (ce);
};

/* Driver for B1a: build a list from input[0..n-1] with sglib_dllist_add,
   walk it forward, then free every element while iterating (the sample's
   last loop).  Returns the last value seen by the walk. */
int b1(const int *input, int n) {
  dllist *l, *the_list = NULL;
  struct sglib_dllist_iterator it;
  int last = 0;
  for (int k = 0; k < n; k++) {
    l = malloc(sizeof(dllist));
    if (l == NULL)
      break;
    l->i = input[k];
    sglib_dllist_add(&the_list, l);
  }
  for (l = the_list; l != NULL; l = l->ptr_to_next)
    last = l->i;
  for (l = sglib_dllist_it_init(&it, the_list); l != NULL;
       l = sglib_dllist_it_next(&it))
    free(l);
  return last;
}

int input[4] = {6, 7, 3, 4};

int main(void) { return b1(input, 4); }
