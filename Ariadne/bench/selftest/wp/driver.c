/* Our driver (not sglib's): iterate over the nodes equal to *te, with
   myListCmp as the subcomparator, as the self-test's
   double_linked_list_test does.  Returns 1 iff one was found.  The
   iterator is a parameter (a local would be allocated after the
   precondition's list facts, which WP does not carry across). */
/*@ requires \valid(it) && !heap(\base_addr(it));
    requires list == \null || in_cmp_list(list);
    requires \valid(te) && !heap(\base_addr(te));
    requires te_init: \initialized(&te->n);
*/
int st_iter_equal(struct sglib_DoubleLinkedList_iterator *it,
                  DoubleLinkedList *list, DoubleLinkedList *te) {
  DoubleLinkedList *ll = NULL;
  int found = 0;
  /*@ loop invariant iter_ok(it, ll) && it->subcomparator == &myListCmp;
      loop assigns ll, found, *it;
  */
  for (ll = sglib_DoubleLinkedList_it_init_on_equal(it, list, myListCmp, te);
       ll != NULL; ll = sglib_DoubleLinkedList_it_next(it))
    found = 1;
  return found;
}
