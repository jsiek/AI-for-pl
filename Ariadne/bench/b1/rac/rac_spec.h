/* Executable version of b1.c's specification block (the ACSL logic
   definitions between part 1 and the allocator declarations), for
   E-ACSL.  gen_rac.py puts `#include "rac_spec.h"` in place of that block
   and refuses to run if the block's hash differs from the one below, so a
   change to the frozen spec forces a review of this file.

   spec-sha256: a42ee116b8fd1e940e414ceefcd66de8e2838076ed16558fb5fa555f4d7cae86

   Translation (README, "Translation rules"):
   - \list<dllist *> values are rac_list handles (struct rac_seq *),
     built and read by twins; \Nil is the NULL handle;
   - heap / dead are the allocation registry (rac_heap, rac_dead);
   - mem, all_live, all_init, live, live_dll stay in ACSL:
     their quantifiers range over the indices of a list, which E-ACSL
     executes; \valid, \offset, \base_addr, \initialized are E-ACSL's own;
   - the inductive dll is its twin rac_dll;
   - in_live_list and iter_ok quantify over lists and pointers: each
     existential is replaced by its witness (rac_reach, rac_prev,
     rac_head), and integer existentials stay;
   - unchanged and the lemmas are left out: unchanged is used only under
     \forall over all lists (dropped annotations), and lemmas are proof
     facts. */

typedef struct rac_seq *rac_list;

/*@ predicate heap(char *b) = rac_heap(b) != 0;
    predicate dead(integer v, char *b) = rac_dead(b) != 0;

    predicate live{L}(dllist *p) =
      \valid(p) && \offset(p) == 0 && heap(\base_addr(p))
      && !dead(__heap, \base_addr(p));

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
    // witnesses: h = rac_head(p), s = rac_reach(h).
    predicate in_live_list{L}(dllist *p) =
      \let h = rac_head(p); \let s = rac_reach(h);
        live_dll(\null, h, s)
        && \exists integer k; 0 <= k < rac_length(s)
                              && p == rac_nth(s, (long)k);

    // \exists dllist *p, \list<dllist *> t; live_dll(p, it->nextelem, t)
    // && ...; witnesses: p = rac_prev(it->nextelem), t = rac_reach(...).
    predicate iter_ok{L}(struct sglib_dllist_iterator *it, dllist *cur) =
      it->subcomparator == \null && it->prevelem == \null
      && \initialized(&it->subcomparator) && \initialized(&it->prevelem)
      && \initialized(&it->nextelem)
      && (\let p = rac_prev(it->nextelem); \let t = rac_reach(it->nextelem);
           live_dll(p, it->nextelem, t)
           && (cur == \null ==> it->nextelem == \null)
           && (cur != \null ==> live(cur) && !mem(cur, t)));
*/
