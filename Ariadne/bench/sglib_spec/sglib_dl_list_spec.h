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
   mentions it (the verified functions do not call it).  The list
   predicates cover only the link fields (all_init), so no parameter
   names the payload.

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

/* t is s with e inserted at index k (a macro, not a predicate: a
   proof device of the private lemmas and asserts). */
#define SGLIB_DL_LIST__INSERTED(t, s, e, k) \
  (\length(t) == \length(s) + 1 \
   && (\forall integer i_; 0 <= i_ < (k) ==> \nth(t, i_) == \nth(s, i_)) \
   && \nth(t, k) == (e) \
   && (\forall integer i_; (k) < i_ < \length(t) \
         ==> \nth(t, i_) == \nth(s, i_ - 1)))

#define SGLIB_DL_LIST_SPEC(type, previous, next, cmp_reads) \
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
  /* The links of every node of s are initialised (the list code reads \
     no other field). */ \
  predicate all_init{L}(\list<type *> s) = \
    \forall integer k; 0 <= k < \length(s) ==> \
      \initialized(&\nth(s, k)->previous) \
      && \initialized(&\nth(s, k)->next); \
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
  /* Every node of s has the fields the comparators read initialised \
     (cmp_reads: a client predicate, a template parameter). */ \
  predicate all_cmp_reads{L}(\list<type *> s) = \
    \forall integer k; 0 <= k < \length(s) ==> cmp_reads(\nth(s, k)); \
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
  /* p is a heap node, live or freed (freeing changes only __heap). */ \
  predicate heap_node{L}(type *p) = \valid(p) && heap(\base_addr(p)); \
  \
  /* The iterator's position in a whole list s.  sglib's iterator walks \
     from the start node back to the head (prevelem), then forward from \
     the start node's successor (nextelem).  prevelem is node b of s \
     (b == -1: none, the backward walk is done), nextelem node f \
     (f == \length(s): none), b < f; the nodes still to visit, 0 .. b and \
     f .. \length(s) - 1, are live.  dll and all_init do not depend on \
     liveness, so a client may free the nodes already returned. */ \
  predicate iter_at{L}(struct sglib_##type##_iterator *it, \
                       \list<type *> s, integer b, integer f) = \
    (\exists type *h; dll(\null, h, s)) && all_init(s) \
    && (\forall integer i; 0 <= i < \length(s) ==> \
          heap_node(\nth(s, i))) \
    && -1 <= b < f && f <= \length(s) \
    && it->prevelem == (b >= 0 ? \nth(s, b) : (type *)\null) \
    && it->nextelem == (f < \length(s) ? \nth(s, f) : (type *)\null) \
    && \forall integer i; (0 <= i <= b || f <= i < \length(s)) \
         ==> live(\nth(s, i)); \
  \
  /* Iterator fields that it_next reads, initialised; no subcomparator. */ \
  predicate iter_fields{L}(struct sglib_##type##_iterator *it) = \
    it->subcomparator == \null \
    && \initialized(&it->subcomparator) && \initialized(&it->prevelem) \
    && \initialized(&it->nextelem); \
  \
  /* A state it_next accepts. */ \
  predicate iter_pre{L}(struct sglib_##type##_iterator *it) = \
    iter_fields(it) \
    && \exists \list<type *> s, integer b, f; iter_at(it, s, b, f); \
  \
  /* The state after it_init/it_next returned cur: cur is \null at the \
     end, otherwise a live node between the two walks. */ \
  predicate iter_ok{L}(struct sglib_##type##_iterator *it, type *cur) = \
    iter_fields(it) \
    && \exists \list<type *> s, integer b, f; \
         iter_at(it, s, b, f) \
         && (cur == \null ==> b == -1 && f == \length(s)) \
         && (cur != \null ==> live(cur) \
             && \exists integer c; b < c < f && cur == \nth(s, c));

/* ---- public: the comparator ---------------------------------------- */

/* The contract every comparator meets, a function or a macro inlined at
   its call sites (owner decision, 2026-11-05).  a and b are the
   comparator's parameter names.  It reads only the fields cmp_reads names
   and writes nothing; it must be proved free of runtime errors (WP with
   -wp-rte) under this contract.  Under the liveness model (-ariadne)
   every read also needs its block not freed, hence the !dead clause; a
   stack or global object is never dead. */
#define SGLIB_DL_LIST_CONTRACT_COMPARATOR(type, cmp_reads, a, b) \
  requires \valid_read(a) && \valid_read(b) \
           && cmp_reads(a) && cmp_reads(b); \
  requires !dead(__heap, \base_addr(a)) && !dead(__heap, \base_addr(b)); \
  assigns \nothing;

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
      all_init(\Cons(h, t)) <==> \
        (\initialized(&h->previous) && \initialized(&h->next) \
         && all_init(t)); \
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
  /* The nodes of a list are distinct (induction). */ \
  lemma dll_distinct{L}: \
    \forall type *prev, *h, \list<type *> s, integer i, j; \
      dll(prev, h, s) ==> 0 <= i < \length(s) ==> 0 <= j < \length(s) \
      ==> \nth(s, i) == \nth(s, j) ==> i == j; \
  \
  /* The converse of dll_links: links, validity and distinctness by \
     index make a list (induction). */ \
  lemma dll_of_links{L}: \
    \forall type *prev, *h, \list<type *> s; \
      (\length(s) == 0 ==> h == \null) \
      ==> (\length(s) > 0 ==> h == \nth(s, 0)) \
      ==> (\forall integer i; 0 <= i < \length(s) ==> \
            \nth(s, i) != \null && \valid(\nth(s, i)) \
            && \nth(s, i)->previous \
               == (i == 0 ? prev : \nth(s, i - 1)) \
            && \nth(s, i)->next \
               == (i + 1 < \length(s) ? \nth(s, i + 1) : (type *)\null)) \
      ==> (\forall integer i, j; 0 <= i < \length(s) \
            ==> 0 <= j < \length(s) ==> \nth(s, i) == \nth(s, j) \
            ==> i == j) \
      ==> dll(prev, h, s); \
  \
  /* A list with e inserted at index k exists (induction). */ \
  lemma list_insert: \
    \forall \list<type *> s, type *e, integer k; 0 <= k <= \length(s) ==> \
      \exists \list<type *> t; SGLIB_DL_LIST__INSERTED(t, s, e, k); \
  \
  /* Unfolding live_dll one node (dll_inv with the cons lemmas). */ \
  lemma live_dll_inv{L}: \
    \forall type *prev, *h, \list<type *> s; \
      live_dll(prev, h, s) ==> h != \null ==> \
        \exists \list<type *> t; \
          s == \Cons(h, t) && live_dll(h, h->next, t); \
  \
  /* A node of a whole live list whose previous is NULL is its head. */ \
  lemma in_live_list_head{L}: \
    \forall type *p; in_live_list(p) ==> p->previous == \null ==> \
      \exists \list<type *> s; live_dll(\null, p, s);

/* ---- sglib_<type>_add ---------------------------------------------- */

/* Public.  add inserts elem before *list, any node of a whole live
   list (or NULL), and makes it *list. */
#define SGLIB_DL_LIST_CONTRACT_ADD(type, previous, next) \
  requires \valid(list) && !heap(\base_addr(list)) && \initialized(list); \
  requires live(elem); \
  requires *list == \null \
    || \exists type *h, \list<type *> s, integer k; \
         live_dll(\null, h, s) && 0 <= k < \length(s) \
         && *list == \nth(s, k) && !mem(elem, s); \
  assigns *list, elem->next, elem->previous, (*list)->previous, \
          { p->next | type *p; \at(*list, Pre) != \null \
                               && p == \at(\at(*list, Pre)->previous, Pre) }; \
  ensures \initialized(list); \
  ensures *list == elem && in_live_list(elem); \
  ensures was_head: \at(*list == \null || (*list)->previous == \null, Pre) \
    ==> elem->previous == \null;

/* Private: the asserts at the end of add's body, in this order.  The
   new list is the old one with elem inserted at the old node's index k
   (lemma list_insert); dll_of_links makes it a list from its links. */
#define SGLIB_DL_LIST__ADD_PRE(type) \
  live_dll{Pre}(\null, h, s) && 0 <= k < \length(s) \
  && \at(*list, Pre) == \nth(s, k) && !mem(elem, s)
#define SGLIB_DL_LIST__ADD_HYPS(type) \
  SGLIB_DL_LIST__ADD_PRE(type) && SGLIB_DL_LIST__INSERTED(t, s, elem, k)
#define SGLIB_DL_LIST_ANNOT_ADD_SINGLE(type, previous, next) \
  assert single: \at(*list, Pre) == \null ==> \
    live_dll(\null, elem, \Cons(elem, \Nil));
/* The old node's predecessor is NULL or a node (offset 0). */
#define SGLIB_DL_LIST_ANNOT_ADD_OLD_PREV(type, previous, next) \
  assert old_prev: \at(*list != \null ==> \
    (*list)->previous == \null \
    || (\offset((*list)->previous) == 0 \
        && heap(\base_addr((*list)->previous))), Pre);
/* Address-level frame: the links add does not write. */
#define SGLIB_DL_LIST_ANNOT_ADD_KEEP_PREV(type, previous, next) \
  assert keep_prev: \forall type *x; \offset(x) == 0 \
    && heap(\base_addr(x)) && x != elem && x != \at(*list, Pre) \
    ==> x->previous == \at(x->previous, Pre);
#define SGLIB_DL_LIST_ANNOT_ADD_KEEP_NEXT(type, previous, next) \
  assert keep_next: \forall type *x; \offset(x) == 0 \
    && heap(\base_addr(x)) && x != elem \
    && x != \at(\at(*list, Pre)->previous, Pre) \
    ==> x->next == \at(x->next, Pre);
#define SGLIB_DL_LIST_ANNOT_ADD_KEEP_INIT(type, previous, next) \
  assert keep_init: \forall type *x; \offset(x) == 0 \
    && heap(\base_addr(x)) \
    ==> (\initialized{Pre}(&x->previous) ==> \initialized(&x->previous)) \
     && (\initialized{Pre}(&x->next) ==> \initialized(&x->next));
/* The links of the old nodes that add does not write. */
#define SGLIB_DL_LIST_ANNOT_ADD_FRAME_PREV(type, previous, next) \
  assert frame_prev: \forall type *h, \list<type *> s, integer k; \
    SGLIB_DL_LIST__ADD_PRE(type) ==> \
    \forall integer i; 0 <= i < \length(s) ==> i != k ==> \
      \nth(s, i)->previous == \at(\nth(s, i)->previous, Pre) \
      && \initialized(&\nth(s, i)->previous);
#define SGLIB_DL_LIST_ANNOT_ADD_FRAME_NEXT(type, previous, next) \
  assert frame_next: \forall type *h, \list<type *> s, integer k; \
    SGLIB_DL_LIST__ADD_PRE(type) ==> \
    \forall integer i; 0 <= i < \length(s) ==> i != k - 1 ==> \
      \nth(s, i)->next == \at(\nth(s, i)->next, Pre) \
      && \initialized(&\nth(s, i)->next);
/* The four links add writes. */
#define SGLIB_DL_LIST_ANNOT_ADD_WRITTEN(type, previous, next) \
  assert written: \forall type *h, \list<type *> s, integer k; \
    SGLIB_DL_LIST__ADD_PRE(type) ==> \
      elem->next == \nth(s, k) \
      && elem->previous == (k > 0 ? \nth(s, k - 1) : (type *)\null) \
      && \nth(s, k)->previous == elem \
      && (k > 0 ==> \nth(s, k - 1)->next == elem) \
      && \initialized(&elem->next) && \initialized(&elem->previous) \
      && \initialized(&\nth(s, k)->previous) \
      && (k > 0 ==> \initialized(&\nth(s, k - 1)->next));
#define SGLIB_DL_LIST_ANNOT_ADD_LINKS(type, previous, next) \
  assert links: \forall type *h, \list<type *> s, t, integer k; \
    SGLIB_DL_LIST__ADD_HYPS(type) ==> \
    \forall integer i; 0 <= i < \length(t) ==> \
      \nth(t, i) != \null && \valid(\nth(t, i)) \
      && \nth(t, i)->previous == (i == 0 ? (type *)\null : \nth(t, i - 1)) \
      && \nth(t, i)->next \
         == (i + 1 < \length(t) ? \nth(t, i + 1) : (type *)\null);
#define SGLIB_DL_LIST_ANNOT_ADD_DISTINCT(type, previous, next) \
  assert distinct: \forall type *h, \list<type *> s, t, integer k; \
    SGLIB_DL_LIST__ADD_HYPS(type) ==> \
    \forall integer i, j; 0 <= i < \length(t) ==> 0 <= j < \length(t) \
      ==> \nth(t, i) == \nth(t, j) ==> i == j;
#define SGLIB_DL_LIST_ANNOT_ADD_NEW_DLL(type, previous, next) \
  assert new_dll: \forall type *h, \list<type *> s, t, integer k; \
    SGLIB_DL_LIST__ADD_HYPS(type) ==> dll(\null, \nth(t, 0), t);
#define SGLIB_DL_LIST_ANNOT_ADD_NEW_LIVE(type, previous, next) \
  assert new_live: \forall type *h, \list<type *> s, t, integer k; \
    SGLIB_DL_LIST__ADD_HYPS(type) ==> all_live(t) && all_init(t);
#define SGLIB_DL_LIST_ANNOT_ADD_INSERT_LIST(type, previous, next) \
  assert insert_list: \forall type *h, \list<type *> s, integer k; \
    SGLIB_DL_LIST__ADD_PRE(type) ==> \
    \exists \list<type *> t; SGLIB_DL_LIST__INSERTED(t, s, elem, k);
#define SGLIB_DL_LIST_ANNOT_ADD_INSERTED(type, previous, next) \
  assert inserted: \forall type *h, \list<type *> s, integer k; \
    SGLIB_DL_LIST__ADD_PRE(type) ==> \
    \exists \list<type *> t; SGLIB_DL_LIST__INSERTED(t, s, elem, k) \
      && live_dll(\null, \nth(t, 0), t);

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

/* Public.  The iterator starts at any node of a whole live list. */
#define SGLIB_DL_LIST_CONTRACT_IT_INIT_ON_EQUAL(type, previous, next) \
  requires \valid(it) && !heap(\base_addr(it)); \
  requires subcomparator == \null; \
  requires list == \null || in_live_list(list); \
  assigns *it; \
  ensures iter_ok(it, \result);

/* The asserts before it_init_on_equal's return, and before it_next's. */
#define SGLIB_DL_LIST_ANNOT_IT_FRAME(type, previous, next) \
  assert frame: \forall \list<type *> s; \
    (\forall integer i; 0 <= i < \length(s) ==> heap_node(\nth(s, i))) \
    ==> unchanged{Pre, Here}(s);
#define SGLIB_DL_LIST_ANNOT_IT_INIT_FRAME(type, previous, next) \
  assert init_frame: \forall \list<type *> s; \
    all_init{Pre}(s) ==> all_init(s);
/* it_init_on_equal: the start position (prevelem = list, nextelem its
   successor). */
#define SGLIB_DL_LIST_ANNOT_IT_START(type, previous, next) \
  assert start: (list == \null ==> iter_at(it, \Nil, -1, 0)) \
    && \forall type *h, \list<type *> s, integer k; \
         live_dll{Pre}(\null, h, s) && 0 <= k < \length(s) \
         && list == \nth(s, k) ==> iter_at(it, s, k, k + 1);

#define SGLIB_DL_LIST_CONTRACT_IT_INIT(type, previous, next) \
  requires \valid(it) && !heap(\base_addr(it)); \
  requires list == \null || in_live_list(list); \
  assigns *it; \
  ensures iter_ok(it, \result);

#define SGLIB_DL_LIST_CONTRACT_IT_NEXT(type, previous, next) \
  requires \valid(it) && !heap(\base_addr(it)); \
  requires iter_pre(it); \
  assigns *it; \
  ensures iter_ok(it, \result);

/* The asserts at the end of it_next's body, after the IT_FRAME and
   IT_INIT_FRAME ones, in this order: one step back, one step forward, or
   the end. */
#define SGLIB_DL_LIST_ANNOT_IT_NEXT_IT_INIT(type, previous, next) \
  assert it_init: \initialized(&it->subcomparator) \
    && \initialized(&it->prevelem) && \initialized(&it->nextelem);
#define SGLIB_DL_LIST_ANNOT_IT_NEXT_BACK(type, previous, next) \
  assert back: \forall \list<type *> s, integer b, f; \
    iter_at{Pre}(it, s, b, f) && b >= 0 \
    ==> ce == \nth(s, b) && iter_at(it, s, b - 1, f);
#define SGLIB_DL_LIST_ANNOT_IT_NEXT_FORWARD(type, previous, next) \
  assert forward: \forall \list<type *> s, integer b, f; \
    iter_at{Pre}(it, s, b, f) && b < 0 && f < \length(s) \
    ==> ce == \nth(s, f) && iter_at(it, s, -1, f + 1);
#define SGLIB_DL_LIST_ANNOT_IT_NEXT_END(type, previous, next) \
  assert end: \forall \list<type *> s, integer b, f; \
    iter_at{Pre}(it, s, b, f) && b < 0 && f == \length(s) \
    ==> ce == \null && iter_at(it, s, -1, f);

#endif
