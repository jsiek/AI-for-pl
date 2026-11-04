/* Executable version of b1.c's specification block (the ACSL logic
   definitions between part 1 and the allocator declarations), for
   E-ACSL.  gen_rac.py puts `#include "rac_spec.h"` in place of that block
   and refuses to run if the block's hash differs from the one below, so a
   change to the frozen spec forces a review of this file.

   spec-sha256: a42ee116b8fd1e940e414ceefcd66de8e2838076ed16558fb5fa555f4d7cae86

   Translation (README, "Translation rules"):
   - \list<dllist *> values are rac_list handles (a long), built and read
     by twins; \Nil is the handle 0;
   - written in the twins' logic form rac_f(x, ...); gen_rac.py inlines
     this file with every twin call cast for E-ACSL (README, "E-ACSL
     workarounds");
   - heap / dead are the allocation registry (rac_heap, rac_dead);
   - mem, all_live, all_init, live, live_dll stay in ACSL:
     their quantifiers range over the indices of a list, which E-ACSL
     executes; \valid, \offset, \initialized are E-ACSL's own;
     heap(\base_addr(p)) is heap_of(p) (E-ACSL has no \base_addr);
   - the inductive dll is its twin rac_dll;
   - in_live_list and iter_ok quantify over lists and pointers: each
     existential variable is replaced by its witness (rac_reach,
     rac_prev, rac_head), substituted in place, and integer existentials
     stay;
   - unchanged and the lemmas are left out: unchanged is used only under
     \forall over all lists (dropped annotations), and lemmas are proof
     facts. */

typedef long rac_list;

/* NULL as a node, for \null arguments of the predicates below (gen_rac.py,
   null_args; README, "E-ACSL workarounds"). */
dllist *rac_null = 0;  /* not const: E-ACSL 33 aborts marking it read-only */

/*@ predicate heap(char *b) = rac_heap(b) != 0;
    predicate dead(integer v, char *b) = rac_dead(b) != 0;
    // heap(\base_addr(p)) and dead(v, \base_addr(p)): E-ACSL 33 does not
    // execute \base_addr, so the registry finds the block containing p.
    predicate heap_of(void *p) = rac_heap_of(p) != 0;
    predicate dead_of(void *p) = rac_dead_of(p) != 0;

    predicate live{L}(dllist *p) =
      \valid(p) && \offset(p) == 0 && heap_of((void *)p)
      && !dead_of((void *)p);

    predicate mem(dllist *p, rac_list s) =
      \exists integer k; 0 <= k < rac_length(s) && rac_nth(s, (long)k) == p;

    predicate all_live{L}(rac_list s) =
      \forall integer k; 0 <= k < rac_length(s) ==>
        live(rac_nth(s, (long)k));

    predicate all_init{L}(rac_list s) =
      \forall integer k; 0 <= k < rac_length(s) ==>
        \initialized(rac_nth(s, (long)k));

    predicate dll{L}(dllist *prev, dllist *h, rac_list s) =
      rac_dll(prev, h, s) != 0;

    predicate live_dll{L}(dllist *prev, dllist *h, rac_list s) =
      dll(prev, h, s) && all_live(s) && all_init(s);

    // \exists dllist *h, \list<dllist *> s, integer k;
    //   live_dll(\null, h, s) && 0 <= k < \length(s) && p == \nth(s, k)
    // witnesses (substituted: E-ACSL has no \let on pointers):
    //   h = rac_head(p), s = rac_reach(h).
    predicate in_live_list{L}(dllist *p) =
      live_dll(\null, rac_head(p), rac_reach(rac_head(p)))
      && \exists integer k; 0 <= k < rac_length(rac_reach(rac_head(p)))
           && p == rac_nth(rac_reach(rac_head(p)), (long)k);

    // \exists dllist *p, \list<dllist *> t; live_dll(p, it->nextelem, t)
    // && ...; witnesses p = rac_prev(it->nextelem), t = rac_reach(...).
    predicate iter_ok{L}(struct sglib_dllist_iterator *it, dllist *cur) =
      it->subcomparator == \null && it->prevelem == \null
      && \initialized(&it->subcomparator) && \initialized(&it->prevelem)
      && \initialized(&it->nextelem)
      && live_dll(rac_prev(it->nextelem), it->nextelem,
                  rac_reach(it->nextelem))
      && (cur == \null ==> it->nextelem == \null)
      && (cur != \null ==> live(cur) && !mem(cur, rac_reach(it->nextelem)));
*/
