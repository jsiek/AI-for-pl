/* Definitions gen_twins.py must refuse, each by name with its reason
   (tests/check.sh compares the diagnostics with untranslatable.expected). */
#include "shapes.h"

/*@ // Two states: a twin reads the current state only.
    predicate two_states{L1, L2}(node *p) =
      \at(p->key, L1) == \at(p->key, L2);

    // Translatable: c is determined by the equation a->next == c.
    inductive reach{L}(node *a, node *b) {
      case reach_refl{L}: \forall node *a; reach{L}(a, a);
      case reach_step{L}: \forall node *a, *b, *c;
        \valid(a) ==> a->next == c ==> reach{L}(c, b) ==> reach{L}(a, b);
    }

    // m occurs in a premise only, and no premise determines it (reach
    // has no mode computing its first argument from its second).
    inductive some_path{L}(node *a) {
      case some_path_any{L}:
        \forall node *a, *m; reach{L}(m, a) ==> some_path{L}(a);
    }

    // \initialized has no executable counterpart in plain C.
    inductive init_list{L}(node *h) {
      case init_nil{L}: init_list{L}(\null);
      case init_cons{L}: \forall node *h;
        h != \null ==> \initialized(h) ==> init_list{L}(h->next) ==>
        init_list{L}(h);
    }

    // k + 1 is not a pattern, and no premise determines k (deciding
    // above(p, n) would mean solving n == k + 1).
    inductive above{L}(node *p, integer n) {
      case above_key{L}: \forall node *p, integer k;
        \valid(p) ==> p->key <= k ==> above{L}(p, k + 1);
    }

    // Uses an untranslated definition.
    predicate uses_some_path{L}(node *a) = some_path(a) || a == \null;

    // \exists over a pointer with no determining conjunct.
    predicate pointed_to{L}(node *p) =
      \exists node *q; \valid(q) && q->next == p;

    // A logic declaration without a definition.
    logic integer weight(node *p);
*/
