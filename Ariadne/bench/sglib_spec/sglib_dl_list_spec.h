/* ACSL spec template for sglib's doubly linked list (plan Q12): B1's
   predicates, public contracts and proof annotations, as macros
   parallel to sglib's SGLIB_DEFINE_DL_LIST_FUNCTIONS(type, comparator,
   previous, next).  README.md says how to instantiate it.

   Every macro expands to ACSL text.  Use it inside an annotation, where
   Frama-C's preprocessing (-pp-annot, the default with gcc's cpp)
   expands it:

     /@ SGLIB_DL_LIST_SPEC(dllist, ptr_to_previous, ptr_to_next) @/

   (with the usual comment delimiters).  A code annotation comment may
   hold only one assert, so each assert is its own macro; a loop's
   invariants and assigns are one macro.

   Parameters are sglib's: `type` (the node type, a typedef name, also
   used in sglib's function and iterator names), `previous` and `next`
   (the link fields).  The comparator is not a parameter: no annotation
   mentions it (the verified functions do not call it).  One further
   parameter, `payload` of SGLIB_DL_LIST_CONTRACT_ADD, names the field
   the client must initialise before `add`; sglib has no such parameter
   (README.md, "Not in sglib's parameters").

   Public (Q11: changes need the owner's approval): SGLIB_DL_LIST_SPEC
   and the SGLIB_DL_LIST_CONTRACT_* macros.  Private: SGLIB_DL_LIST_LEMMAS
   and the SGLIB_DL_LIST_ANNOT_* macros.

   Inside the macros, comments are C comments (an ACSL `//` comment
   would swallow the rest of the macro, whose lines are joined first).
   The names of predicates and lemmas do not depend on the parameters, so
   a translation unit holds one instantiation. */

#ifndef SGLIB_DL_LIST_SPEC_H
#define SGLIB_DL_LIST_SPEC_H

/* ---- public: the shape predicates ---------------------------------- */

#define SGLIB_DL_LIST_SPEC(type, previous, next) \
  /* p is a usable list node: a live heap block at offset 0. */ \
  predicate live{L}(type *p) = \
    \valid(p) && \offset(p) == 0 && heap(\base_addr(p)) \
    && !dead(__heap, \base_addr(p)); \
  \
  predicate mem(type *p, \list<type *> s) = \
    \exists integer k; 0 <= k < \length(s) && \nth(s, k) == p; \
  \
  predicate all_live{L}(\list<type *> s) = \
    \forall integer k; 0 <= k < \length(s) ==> live(\nth(s, k)); \
  \
  /* Every node of s is initialised (all of its fields). */ \
  predicate all_init{L}(\list<type *> s) = \
    \forall integer k; 0 <= k < \length(s) ==> \initialized(\nth(s, k)); \
  \
  /* Shape only: the nodes reached from h by next are exactly s; each is \
     valid, its previous is its predecessor (prev for h), and none \
     repeats.  Liveness is separate (all_live), so allocation and free, \
     which change only __heap, leave dll untouched. */ \
  inductive dll{L}(type *prev, type *h, \list<type *> s) { \
    case dll_nil{L}: \forall type *prev; dll{L}(prev, \null, \Nil); \
    case dll_cons{L}: \
      \forall type *prev, *h, \list<type *> s; \
        h != \null ==> \valid(h) ==> h->previous == prev ==> \
        !mem(h, s) ==> dll{L}(h, h->next, s) ==> \
        dll{L}(prev, h, \Cons(h, s)); \
  } \
  \
  /* Between L1 and L2 the link fields of the nodes of s are unchanged \
     and every node is still valid. */ \
  predicate unchanged{L1, L2}(\list<type *> s) = \
    \forall integer k; 0 <= k < \length(s) ==> \
      \at(\nth(s, k)->next, L1) == \at(\nth(s, k)->next, L2) \
      && \at(\nth(s, k)->previous, L1) \
         == \at(\nth(s, k)->previous, L2) \
      && \valid{L2}(\nth(s, k)); \
  \
  /* A whole live, initialised list, given by any of its nodes' \
     predecessor. */ \
  predicate live_dll{L}(type *prev, type *h, \list<type *> s) = \
    dll(prev, h, s) && all_live(s) && all_init(s); \
  \
  /* p is a node of some whole live list (head's predecessor is NULL). */ \
  predicate in_live_list{L}(type *p) = \
    \exists type *h, \list<type *> s, integer k; \
      live_dll(\null, h, s) && 0 <= k < \length(s) && p == \nth(s, k); \
  \
  /* Iterator state reached by it_init/it_next with no subcomparator: the \
     backward walk is done and nextelem starts a well-formed live rest. */ \
  predicate iter_ok{L}(struct sglib_##type##_iterator *it, type *cur) = \
    it->subcomparator == \null && it->prevelem == \null \
    && \initialized(&it->subcomparator) && \initialized(&it->prevelem) \
    && \initialized(&it->nextelem) \
    && \exists type *p, \list<type *> t; \
         live_dll(p, it->nextelem, t) \
         && (cur == \null ==> it->nextelem == \null) \
         && (cur != \null ==> live(cur) && !mem(cur, t));

/* ---- private: lemmas (each is proved; order matters: a lemma uses
        only the lemmas before it) ------------------------------------ */

#define SGLIB_DL_LIST_LEMMAS(type, previous, next) \
  /* List facts used to unfold all_live and mem over \Cons (no \
     induction). */ \
  lemma mem_cons: \
    \forall type *x, *h, \list<type *> t; \
      mem(x, \Cons(h, t)) <==> (x == h || mem(x, t)); \
  lemma all_live_cons{L}: \
    \forall type *h, \list<type *> t; \
      all_live(\Cons(h, t)) <==> (live(h) && all_live(t)); \
  lemma all_live_nil{L}: all_live(\Nil); \
  \
  lemma all_init_cons{L}: \
    \forall type *h, \list<type *> t; \
      all_init(\Cons(h, t)) <==> (\initialized(h) && all_init(t)); \
  lemma all_init_nil{L}: all_init(\Nil); \
  \
  /* Unfolding dll (inversion). */ \
  lemma dll_null{L}: \
    \forall type *prev, \list<type *> s; dll(prev, \null, s) ==> s == \Nil; \
  lemma dll_inv{L}: \
    \forall type *prev, *h, \list<type *> s; \
      dll(prev, h, s) ==> h != \null ==> \
        \valid(h) && h->previous == prev \
        && \exists \list<type *> t; \
             s == \Cons(h, t) && !mem(h, t) && dll(h, h->next, t); \
  \
  /* Index view of dll: node k's links point to its neighbours in s. \
     (k is quantified at the top, so SMT instantiates this only for \
     indices already present in a goal.) */ \
  lemma dll_links{L}: \
    \forall type *prev, *h, \list<type *> s, integer k; \
      dll(prev, h, s) ==> 0 <= k < \length(s) ==> \
          \nth(s, k) != \null \
          && \nth(s, k)->previous \
             == (k == 0 ? prev : \nth(s, k - 1)) \
          && \nth(s, k)->next \
             == (k + 1 < \length(s) ? \nth(s, k + 1) : (type *)\null); \
  \
  /* Node 0 is the only node whose previous is NULL in a whole list. \
     (That node 0 is the head follows from dll_inv; a separate lemma \
     `nth(s, 0) == h` made SMT time out on add's goals.) */ \
  lemma dll_first{L}: \
    \forall type *h, \list<type *> s, integer k; \
      dll(\null, h, s) ==> 0 <= k < \length(s) ==> \
        \nth(s, k)->previous == \null ==> k == 0; \
  \
  lemma dll_frame{L1, L2}: \
    \forall type *prev, *h, \list<type *> s; \
      dll{L1}(prev, h, s) ==> unchanged{L1, L2}(s) ==> dll{L2}(prev, h, s); \
  \
  /* Unfolding live_dll one node (dll_inv with the cons lemmas). */ \
  lemma live_dll_inv{L}: \
    \forall type *prev, *h, \list<type *> s; \
      live_dll(prev, h, s) ==> h != \null ==> \
        \exists \list<type *> t; \
          s == \Cons(h, t) && live_dll(h, h->next, t);

/* ---- sglib_<type>_add ---------------------------------------------- */

/* Public.  Restricted to what B1 uses: *list is the head of a whole
   list (sglib allows any element). */
#define SGLIB_DL_LIST_CONTRACT_ADD(type, previous, next, payload) \
  requires \valid(list) && !heap(\base_addr(list)) && \initialized(list); \
  requires live(elem); \
  requires elem_init: \initialized(&elem->payload); \
  requires \exists \list<type *> s; \
    live_dll(\null, *list, s) && !mem(elem, s); \
  assigns *list, elem->next, elem->previous, \
          (*list)->previous; \
  ensures \initialized(list); \
  ensures \exists \list<type *> s; live_dll(\null, *list, s);

/* Private: the asserts at the end of add's body, in this order. */
#define SGLIB_DL_LIST_ANNOT_ADD_INIT_FRAME(type, previous, next) \
  assert init_frame: \initialized(elem) && \forall \list<type *> s; \
    all_init{Pre}(s) ==> all_init(s);
#define SGLIB_DL_LIST_ANNOT_ADD_OLD_HEAD_INIT(type, previous, next) \
  assert old_head_init: \
    \at(*list, Pre) != \null ==> \initialized(\at(*list, Pre));
#define SGLIB_DL_LIST_ANNOT_ADD_FRAME(type, previous, next) \
  assert frame: \forall \list<type *> s; \
    all_live{Pre}(s) && !mem(elem, s) && !mem(\at(*list, Pre), s) \
    ==> unchanged{Pre, Here}(s);
#define SGLIB_DL_LIST_ANNOT_ADD_LINKED(type, previous, next) \
  assert linked: \at(*list, Pre) != \null ==> \
    \forall \list<type *> t; \
      dll{Pre}(\at(*list, Pre), \at(\at(*list, Pre)->next, Pre), t) \
      && all_live{Pre}(t) && !mem(\at(*list, Pre), t) && !mem(elem, t) \
      ==> dll(\null, elem, \Cons(elem, \Cons(\at(*list, Pre), t))) \
          && all_live(\Cons(elem, \Cons(\at(*list, Pre), t)));
#define SGLIB_DL_LIST_ANNOT_ADD_LINKED_INIT(type, previous, next) \
  assert linked_init: \at(*list, Pre) != \null ==> \
    \forall \list<type *> t; \
      all_init(t) ==> all_init(\Cons(elem, \Cons(\at(*list, Pre), t)));
#define SGLIB_DL_LIST_ANNOT_ADD_TAIL(type, previous, next) \
  assert tail: \at(*list, Pre) != \null ==> \
    \exists \list<type *> t; \
      dll{Pre}(\at(*list, Pre), \at(\at(*list, Pre)->next, Pre), t) \
      && all_live{Pre}(t) && all_init(t) \
      && !mem(\at(*list, Pre), t) && !mem(elem, t);
#define SGLIB_DL_LIST_ANNOT_ADD_SINGLE(type, previous, next) \
  assert single: \at(*list, Pre) == \null ==> \
    live_dll(\null, elem, \Cons(elem, \Nil));

/* ---- sglib_<type>_get_first ---------------------------------------- */

#define SGLIB_DL_LIST_CONTRACT_GET_FIRST(type, previous, next) \
  requires list == \null || in_live_list(list); \
  assigns \nothing; \
  ensures list == \null ==> \result == \null; \
  /* the result heads the same live list that contains list */ \
  ensures heads_list: list != \null ==> \
    \exists \list<type *> s, integer k; \
      live_dll(\null, \result, s) && 0 <= k < \length(s) \
      && \nth(s, k) == list;

#define SGLIB_DL_LIST_ANNOT_GET_FIRST_LOOP(type, previous, next) \
  loop invariant \
    \exists type *h, \list<type *> s, integer j, k; \
      live_dll(\null, h, s) && 0 <= j < \length(s) \
      && 0 <= k < \length(s) && _dll_ == \nth(s, j) \
      && list == \nth(s, k); \
  loop assigns _dll_;
#define SGLIB_DL_LIST_ANNOT_GET_FIRST_AT_HEAD(type, previous, next) \
  assert at_head: \exists \list<type *> s, integer k; \
    live_dll(\null, _dll_, s) && 0 <= k < \length(s) \
    && \nth(s, k) == list;

/* ---- sglib_<type>_get_last ----------------------------------------- */

#define SGLIB_DL_LIST_CONTRACT_GET_LAST(type, previous, next) \
  requires list == \null || in_live_list(list); \
  assigns \nothing; \
  ensures list == \null ==> \result == \null; \
  /* the result is the last node of the same live list that contains \
     list */ \
  ensures last_of_list: list != \null ==> \
    \exists type *h, \list<type *> s, integer k; \
      live_dll(\null, h, s) && 0 <= k < \length(s) \
      && \nth(s, k) == list && \result == \nth(s, \length(s) - 1);

#define SGLIB_DL_LIST_ANNOT_GET_LAST_LOOP(type, previous, next) \
  SGLIB_DL_LIST_ANNOT_GET_FIRST_LOOP(type, previous, next)
#define SGLIB_DL_LIST_ANNOT_GET_LAST_AT_LAST(type, previous, next) \
  assert at_last: \exists type *h, \list<type *> s, integer k; \
    live_dll(\null, h, s) && 0 <= k < \length(s) \
    && \nth(s, k) == list && _dll_ == \nth(s, \length(s) - 1);

/* ---- iterator ------------------------------------------------------ */

#define SGLIB_DL_LIST_CONTRACT_IT_INIT_ON_EQUAL(type, previous, next) \
  requires \valid(it) && !heap(\base_addr(it)); \
  requires subcomparator == \null; \
  requires \exists \list<type *> s; live_dll(\null, list, s); \
  assigns *it; \
  ensures iter_ok(it, \result);

/* The asserts before it_init_on_equal's return, and before it_next's. */
#define SGLIB_DL_LIST_ANNOT_IT_FRAME(type, previous, next) \
  assert frame: \forall \list<type *> s; \
    all_live(s) ==> unchanged{Pre, Here}(s);
#define SGLIB_DL_LIST_ANNOT_IT_INIT_FRAME(type, previous, next) \
  assert init_frame: \forall \list<type *> s; \
    all_init{Pre}(s) ==> all_init(s);

#define SGLIB_DL_LIST_CONTRACT_IT_INIT(type, previous, next) \
  requires \valid(it) && !heap(\base_addr(it)); \
  requires \exists \list<type *> s; live_dll(\null, list, s); \
  assigns *it; \
  ensures iter_ok(it, \result);

#define SGLIB_DL_LIST_CONTRACT_IT_NEXT(type, previous, next) \
  requires \valid(it) && !heap(\base_addr(it)); \
  requires it->subcomparator == \null; \
  requires \initialized(&it->subcomparator) && \initialized(&it->prevelem) \
           && \initialized(&it->nextelem); \
  requires \
    (it->prevelem == \null \
     && \exists type *p, \list<type *> t; \
          live_dll(p, it->nextelem, t)) \
    || (it->prevelem != \null \
        && \exists \list<type *> t; \
             live_dll(\null, it->prevelem, \Cons(it->prevelem, t)) \
             && it->nextelem == it->prevelem->next); \
  assigns *it; \
  ensures iter_ok(it, \result);

/* The asserts at the end of it_next's body, after the IT_FRAME and
   IT_INIT_FRAME ones, in this order. */
#define SGLIB_DL_LIST_ANNOT_IT_NEXT_IT_INIT(type, previous, next) \
  assert it_init: \initialized(&it->subcomparator) \
    && \initialized(&it->prevelem) && \initialized(&it->nextelem);
#define SGLIB_DL_LIST_ANNOT_IT_NEXT_LIVE_FRAME(type, previous, next) \
  assert live_frame: \forall type *p, *h, \list<type *> t; \
    live_dll{Pre}(p, h, t) ==> live_dll(p, h, t);
#define SGLIB_DL_LIST_ANNOT_IT_NEXT_REST(type, previous, next) \
  assert rest: \exists type *p, \list<type *> t; \
    live_dll{Pre}(p, it->nextelem, t) \
    && (ce == \null ==> it->nextelem == \null) \
    && (ce != \null ==> live(ce) && !mem(ce, t));

#endif
