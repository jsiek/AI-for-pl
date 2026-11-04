/* Regression fixture for gen_twins.py (review of PR #228):
   - zero, cell: indexed reads are guarded: p[0].key (Frama-C writes
     it (p + 0)->key) and q->a[k], whose index can leave the struct;
   - ok: a read under one arm of ?: is guarded inside that arm only
     (ok(\null) is true);
   - imp, orr: a read after ==> / || is guarded only where it is read;
   - first_cons, pmem: \Cons over two element types, the first rendered
     before the second type is seen: one cons builtin per type, named
     the same in the spec and in the twins header.
   guards_test.c runs the twins; check.sh compares the builtins the spec
   calls with the header's. */
#include "guards.h"

/*@ predicate zero(node *p) = p[0].key == 0;
    predicate cell(arr4 *q, integer k) = q->a[k] == 0;
    predicate ok(node *p) = (p == \null ? 0 : p->key) == 0;
    predicate imp(node *p) = p != \null ==> p->key == 0;
    predicate orr(node *p) = p == \null || p->key == 0;

    inductive is_zero{L}(node *p) {
      case is_zero_c{L}: \forall node *p; zero(p) ==> is_zero{L}(p);
    }
    inductive is_cell{L}(arr4 *q, integer k) {
      case is_cell_c{L}: \forall arr4 *q, integer k; cell(q, k) ==>
        is_cell{L}(q, k);
    }
    inductive is_ok{L}(node *p) {
      case is_ok_c{L}: \forall node *p; ok(p) ==> imp(p) ==> orr(p) ==>
        is_ok{L}(p);
    }

    predicate first_cons(node *p, \list<node *> s) = s == \Cons(p, \Nil);
    predicate pmem(pair *q, \list<pair *> t) =
      t == \Cons(q, \Nil)
      || \exists integer k; 0 <= k < \length(t) && \nth(t, k) == q;
*/
