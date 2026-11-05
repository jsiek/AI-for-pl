/* Benchmark B1, frozen-only variant (milestone M3): b1.c with the
   human's internal annotations removed.  Kept: the shape predicates and
   logic definitions, the frozen contracts (requires / ensures / assigns)
   of the benchmark functions, the ghost liveness instrumentation of the
   -ariadne plugin (ARIADNE_ALLOC / ARIADNE_FREE), and the C code
   unchanged.  Removed: every loop invariant, loop assigns, loop variant
   and assert, and every ACSL lemma (they are the annotator's to write;
   see README "Frozen-only variant").

   Specification status: the predicates and contracts below are the
   human-reviewed, frozen spec of plan section 4 (guardrail 3a).  */

#include <assert.h>
#include <stddef.h>
#include "ariadne_alloc.h"

/* BEGIN GENERATED (b1_gen.c), part 1: types */
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
/* END GENERATED, part 1 */

/*@ // p is a usable list node: a live heap block at offset 0.
    predicate live{L}(dllist *p) =
      \valid(p) && \offset(p) == 0 && heap(\base_addr(p))
      && !dead(__heap, \base_addr(p));

    predicate mem(dllist *p, \list<dllist *> s) =
      \exists integer k; 0 <= k < \length(s) && \nth(s, k) == p;

    predicate all_live{L}(\list<dllist *> s) =
      \forall integer k; 0 <= k < \length(s) ==> live(\nth(s, k));

    // Every node of s is initialised (all of its fields).
    predicate all_init{L}(\list<dllist *> s) =
      \forall integer k; 0 <= k < \length(s) ==> \initialized(\nth(s, k));

    // Shape only: the nodes reached from h by ptr_to_next are exactly s;
    // each is valid, its ptr_to_previous is its predecessor (prev for h),
    // and none repeats.  Liveness is separate (all_live), so allocation and
    // free, which change only __heap, leave dll untouched.
    inductive dll{L}(dllist *prev, dllist *h, \list<dllist *> s) {
      case dll_nil{L}: \forall dllist *prev; dll{L}(prev, \null, \Nil);
      case dll_cons{L}:
        \forall dllist *prev, *h, \list<dllist *> s;
          h != \null ==> \valid(h) ==> h->ptr_to_previous == prev ==>
          !mem(h, s) ==> dll{L}(h, h->ptr_to_next, s) ==>
          dll{L}(prev, h, \Cons(h, s));
    }

    // Between L1 and L2 the link fields of the nodes of s are unchanged and
    // every node is still valid.
    predicate unchanged{L1, L2}(\list<dllist *> s) =
      \forall integer k; 0 <= k < \length(s) ==>
        \at(\nth(s, k)->ptr_to_next, L1) == \at(\nth(s, k)->ptr_to_next, L2)
        && \at(\nth(s, k)->ptr_to_previous, L1)
           == \at(\nth(s, k)->ptr_to_previous, L2)
        && \valid{L2}(\nth(s, k));

    // A whole live, initialised list, given by any of its nodes'
    // predecessor.
    predicate live_dll{L}(dllist *prev, dllist *h, \list<dllist *> s) =
      dll(prev, h, s) && all_live(s) && all_init(s);

    // p is a node of some whole live list (head's predecessor is NULL).
    predicate in_live_list{L}(dllist *p) =
      \exists dllist *h, \list<dllist *> s, integer k;
        live_dll(\null, h, s) && 0 <= k < \length(s) && p == \nth(s, k);

    // Iterator state reached by it_init/it_next with no subcomparator:
    // the backward walk is done and nextelem starts a well-formed live rest.
    predicate iter_ok{L}(struct sglib_dllist_iterator *it, dllist *cur) =
      it->subcomparator == \null && it->prevelem == \null
      && \initialized(&it->subcomparator) && \initialized(&it->prevelem)
      && \initialized(&it->nextelem)
      && \exists dllist *p, \list<dllist *> t;
           live_dll(p, it->nextelem, t)
           && (cur == \null ==> it->nextelem == \null)
           && (cur != \null ==> live(cur) && !mem(cur, t));
*/

/*@ lemma dll_null{L}: \forall dllist *p, \list<dllist *> s;
      dll(p, \null, s) ==> s == \Nil;

    lemma dll_inv{L}: \forall dllist *p, *h, \list<dllist *> s;
      h != \null ==> dll(p, h, s) ==>
      \exists \list<dllist *> t; s == \Cons(h, t) && \valid(h)
        && h->ptr_to_previous == p && !mem(h, t)
        && dll(h, h->ptr_to_next, t);

    lemma dll_head{L}: \forall dllist *p, *h, \list<dllist *> s;
      dll(p, h, s) ==> 0 < \length(s) ==> \nth(s, 0) == h;

    lemma dll_frame{L1, L2}: \forall dllist *p, *h, \list<dllist *> s;
      dll{L1}(p, h, s) ==> unchanged{L1, L2}(s) ==> dll{L2}(p, h, s);

    lemma dll_nth_prev{L}: \forall dllist *p, *h, \list<dllist *> s, integer k;
      dll(p, h, s) ==> 0 < k < \length(s) ==>
      \nth(s, k)->ptr_to_previous == \nth(s, k - 1);

    lemma dll_nth_next{L}: \forall dllist *p, *h, \list<dllist *> s, integer k;
      dll(p, h, s) ==> 0 <= k < \length(s) - 1 ==>
      \nth(s, k)->ptr_to_next == \nth(s, k + 1);

    lemma dll_last{L}: \forall dllist *p, *h, \list<dllist *> s;
      dll(p, h, s) ==> 0 < \length(s) ==>
      \nth(s, \length(s) - 1)->ptr_to_next == \null;

    lemma in_live_list_prev{L}: \forall dllist *q;
      in_live_list(q) ==> q->ptr_to_previous != \null ==>
      in_live_list(q->ptr_to_previous);

    lemma same_base{L}: \forall dllist *p, *q;
      \offset(p) == 0 ==> \offset(q) == 0 ==>
      \base_addr(p) == \base_addr(q) ==> p == q;

    lemma not_mem_cons: \forall dllist *x, *h, \list<dllist *> t;
      !mem(x, \Cons(h, t)) ==> x != h && !mem(x, t);

    lemma live_dll_cons{L}: \forall dllist *p, *x, \list<dllist *> t;
      live(x) ==> \initialized(x) ==> x->ptr_to_previous == p ==>
      !mem(x, t) ==> live_dll(x, x->ptr_to_next, t) ==>
      live_dll(p, x, \Cons(x, t));

    lemma live_dll_single{L}: \forall dllist *p, *x;
      live(x) ==> \initialized(x) ==> x->ptr_to_previous == p ==>
      x->ptr_to_next == \null ==> live_dll(p, x, \Cons(x, \Nil));

    lemma in_live_list_live{L}: \forall dllist *q;
      in_live_list(q) ==> live(q) && \initialized(q);

    lemma live_dll_nil{L}: \forall dllist *p; live_dll(p, \null, \Nil);

    lemma all_live_tail{L}: \forall dllist *h, \list<dllist *> t;
      all_live(\Cons(h, t)) ==> live(h) && all_live(t);

    lemma all_init_tail{L}: \forall dllist *h, \list<dllist *> t;
      all_init(\Cons(h, t)) ==> \initialized(h) && all_init(t);

    lemma live_dll_tail{L}: \forall dllist *p, *h, \list<dllist *> s;
      h != \null ==> live_dll(p, h, s) ==>
      \exists \list<dllist *> t; s == \Cons(h, t) && live(h)
        && \initialized(h) && h->ptr_to_previous == p && !mem(h, t)
        && live_dll(h, h->ptr_to_next, t);

    lemma live_dll_in_live_list{L}: \forall dllist *h, \list<dllist *> s;
      h != \null ==> live_dll(\null, h, s) ==> in_live_list(h);

    lemma all_live_alloc{L1, L2}: \forall \list<dllist *> s;
      all_live{L1}(s) ==>
      (\forall char *b; heap(b) ==> !dead(\at(__heap, L1), b) ==>
         !dead(\at(__heap, L2), b)) ==>
      (\forall integer k; 0 <= k < \length(s) ==> \valid{L2}(\nth(s, k))) ==>
      all_live{L2}(s);

    lemma not_mem_fresh{L}: \forall \list<dllist *> s, dllist *x;
      all_live(s) ==>
      (\forall char *b; heap(b) ==> !dead(__heap, b) ==> b != \base_addr(x)) ==>
      !mem(x, s);

    lemma all_live_free{L1, L2}: \forall \list<dllist *> s, dllist *x;
      all_live{L1}(s) ==> live{L1}(x) ==> !mem(x, s) ==>
      (\forall char *b; b != \base_addr{L1}(x) ==>
         (dead(\at(__heap, L2), b) <==> dead(\at(__heap, L1), b))) ==>
      (\forall integer k; 0 <= k < \length(s) ==> \valid{L2}(\nth(s, k))) ==>
      all_live{L2}(s);
*/

/*@ ARIADNE_ALLOC */ dllist *ariadne_alloc_dllist(void);
/*@ ARIADNE_FREE */ void ariadne_free_dllist(dllist *p);

/* BEGIN GENERATED (b1_gen.c), part 2: prototypes and functions */
extern void sglib_dllist_add(dllist **list, dllist *elem);
extern void sglib_dllist_add_before(dllist **list, dllist *elem);
extern void sglib_dllist_add_after(dllist **list, dllist *elem);
extern int sglib_dllist_add_if_not_member(dllist **list, dllist *elem,
                                          dllist **member);
extern int sglib_dllist_add_before_if_not_member(dllist **list, dllist *elem,
                                                 dllist **member);
extern int sglib_dllist_add_after_if_not_member(dllist **list, dllist *elem,
                                                dllist **member);
extern void sglib_dllist_concat(dllist **first, dllist *second);
extern void sglib_dllist_delete(dllist **list, dllist *elem);
extern int sglib_dllist_delete_if_member(dllist **list, dllist *elem,
                                         dllist **member);
extern int sglib_dllist_is_member(dllist *list, dllist *elem);
extern dllist *sglib_dllist_find_member(dllist *list, dllist *elem);
extern dllist *sglib_dllist_get_first(dllist *list);
extern dllist *sglib_dllist_get_last(dllist *list);
extern void sglib_dllist_sort(dllist **list);
extern int sglib_dllist_len(dllist *list);
extern void sglib_dllist_reverse(dllist **list);
extern dllist *sglib_dllist_it_init(struct sglib_dllist_iterator *it,
                                    dllist *list);
extern dllist *
sglib_dllist_it_init_on_equal(struct sglib_dllist_iterator *it, dllist *list,
                              int (*subcomparator)(dllist *, dllist *),
                              dllist *equalto);
extern dllist *sglib_dllist_it_current(struct sglib_dllist_iterator *it);
extern dllist *sglib_dllist_it_next(struct sglib_dllist_iterator *it);
;
/*@ requires \valid(list) && !heap(\base_addr(list)) && \initialized(list);
    requires live(elem);
    requires elem_init: \initialized(&elem->i);
    requires \exists \list<dllist *> s;
      live_dll(\null, *list, s) && !mem(elem, s);
    assigns *list, elem->ptr_to_next, elem->ptr_to_previous,
            (*list)->ptr_to_previous;
    ensures \initialized(list);
    ensures \exists \list<dllist *> s; live_dll(\null, *list, s);
*/
void sglib_dllist_add(dllist **list, dllist *elem) {
  {
    {
      if ((*list) == NULL) {
        {
          (*list) = (elem);
          (*list)->ptr_to_next = (*list)->ptr_to_previous = NULL;
          /*@ assert elem->ptr_to_next == \null
                && elem->ptr_to_previous == \null
                && live(elem) && \initialized(elem); */
          //@ assert live_dll(\null, elem, \Cons(elem, \Nil));
        };
      } else {
        /*@ assert \exists \list<dllist *> t;
              live_dll(*list, (*list)->ptr_to_next, t) && live(*list)
              && \initialized(*list) && (*list)->ptr_to_previous == \null
              && !mem(*list, t) && !mem(elem, t) && elem != *list; */
        (elem)->ptr_to_next = (*list);
        (elem)->ptr_to_previous = (*list)->ptr_to_previous;
        (*list)->ptr_to_previous = (elem);
        if ((elem)->ptr_to_previous != NULL)
          (elem)->ptr_to_previous->ptr_to_next = (elem);
        /*@ assert \exists \list<dllist *> t;
              live_dll{Pre}(*list, \at((*list)->ptr_to_next, Pre), t)
              && live(*list) && \initialized(*list)
              && !mem(*list, t) && !mem(elem, t) && elem != *list
              && *list == \at(*list, Pre)
              && (*list)->ptr_to_previous == elem
              && elem->ptr_to_next == *list
              && elem->ptr_to_previous == \null; */
      }
    }
    (*list) = (elem);
    /*@ assert \forall \list<dllist *> t;
          all_live{Pre}(t) ==> !mem(elem, t) ==> !mem(\at(*list, Pre), t) ==>
          unchanged{Pre, Here}(t) && (all_init{Pre}(t) ==> all_init(t)); */
    /*@ assert \at(*list, Pre) != \null ==>
          \exists \list<dllist *> t; !mem(elem, t) && !mem(\at(*list, Pre), t)
            && live_dll{Pre}(\at(*list, Pre), \at((*list)->ptr_to_next, Pre), t)
            && \at((*list)->ptr_to_next, Pre) == \at(*list, Pre)->ptr_to_next; */
    /*@ assert \at(*list, Pre) != \null ==>
          \at(*list, Pre)->ptr_to_previous == elem
          && elem->ptr_to_next == \at(*list, Pre)
          && elem->ptr_to_previous == \null
          && live(\at(*list, Pre)) && \initialized(\at(*list, Pre))
          && live(elem) && \initialized(elem) && elem != \at(*list, Pre); */
    /*@ assert \at(*list, Pre) != \null ==>
          \exists \list<dllist *> t; !mem(elem, t) && !mem(\at(*list, Pre), t)
            && live_dll(\at(*list, Pre), \at(*list, Pre)->ptr_to_next, t); */
    /*@ assert \at(*list, Pre) != \null ==>
          \exists \list<dllist *> t;
            !mem(elem, \Cons(\at(*list, Pre), t))
            && live_dll(elem, \at(*list, Pre), \Cons(\at(*list, Pre), t)); */
    /*@ assert \at(*list, Pre) != \null ==>
          \exists \list<dllist *> t;
            live_dll(\null, elem, \Cons(elem, \Cons(\at(*list, Pre), t))); */
  };
}
void sglib_dllist_add_after(dllist **list, dllist *elem) {
  {
    if ((*list) == NULL) {
      {
        (*list) = (elem);
        (*list)->ptr_to_next = (*list)->ptr_to_previous = NULL;
      };
    } else {
      (elem)->ptr_to_next = (*list)->ptr_to_next;
      (elem)->ptr_to_previous = (*list);
      (*list)->ptr_to_next = (elem);
      if ((elem)->ptr_to_next != NULL)
        (elem)->ptr_to_next->ptr_to_previous = (elem);
    }
  };
}
void sglib_dllist_add_before(dllist **list, dllist *elem) {
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
  };
}
int sglib_dllist_add_if_not_member(dllist **list, dllist *elem,
                                   dllist **member) {
  {
    {
      dllist *_dlp_;
      for (_dlp_ = (*list); _dlp_ != NULL && (_dlp_->i - (elem)->i) != 0;
           _dlp_ = _dlp_->ptr_to_previous)
        ;
      if (_dlp_ == NULL && (*list) != NULL) {
        for (_dlp_ = (*list)->ptr_to_next;
             _dlp_ != NULL && (_dlp_->i - (elem)->i) != 0;
             _dlp_ = _dlp_->ptr_to_next)
          ;
      }
      (*member) = _dlp_;
      if (_dlp_ == NULL) {
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
    };
  };
  return (*member == NULL);
}
int sglib_dllist_add_after_if_not_member(dllist **list, dllist *elem,
                                         dllist **member) {
  {
    {
      dllist *_dlp_;
      for (_dlp_ = (*list); _dlp_ != NULL && (_dlp_->i - (elem)->i) != 0;
           _dlp_ = _dlp_->ptr_to_previous)
        ;
      if (_dlp_ == NULL && (*list) != NULL) {
        for (_dlp_ = (*list)->ptr_to_next;
             _dlp_ != NULL && (_dlp_->i - (elem)->i) != 0;
             _dlp_ = _dlp_->ptr_to_next)
          ;
      }
      (*member) = _dlp_;
      if (_dlp_ == NULL) {
        {
          if ((*list) == NULL) {
            {
              (*list) = (elem);
              (*list)->ptr_to_next = (*list)->ptr_to_previous = NULL;
            };
          } else {
            (elem)->ptr_to_next = (*list)->ptr_to_next;
            (elem)->ptr_to_previous = (*list);
            (*list)->ptr_to_next = (elem);
            if ((elem)->ptr_to_next != NULL)
              (elem)->ptr_to_next->ptr_to_previous = (elem);
          }
        };
      }
    };
  };
  return (*member == NULL);
}
int sglib_dllist_add_before_if_not_member(dllist **list, dllist *elem,
                                          dllist **member) {
  {
    {
      dllist *_dlp_;
      for (_dlp_ = (*list); _dlp_ != NULL && (_dlp_->i - (elem)->i) != 0;
           _dlp_ = _dlp_->ptr_to_previous)
        ;
      if (_dlp_ == NULL && (*list) != NULL) {
        for (_dlp_ = (*list)->ptr_to_next;
             _dlp_ != NULL && (_dlp_->i - (elem)->i) != 0;
             _dlp_ = _dlp_->ptr_to_next)
          ;
      }
      (*member) = _dlp_;
      if (_dlp_ == NULL) {
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
        };
      }
    };
  };
  return (*member == NULL);
}
void sglib_dllist_concat(dllist **first, dllist *second) {
  {
    if ((*first) == NULL) {
      (*first) = (second);
    } else if ((second) != NULL) {
      dllist *_dlp_;
      for (_dlp_ = (*first); _dlp_->ptr_to_next != NULL;
           _dlp_ = _dlp_->ptr_to_next)
        ;
      {
        if ((_dlp_) == NULL) {
          {
            (_dlp_) = (second);
            (_dlp_)->ptr_to_next = (_dlp_)->ptr_to_previous = NULL;
          };
        } else {
          (second)->ptr_to_next = (_dlp_)->ptr_to_next;
          (second)->ptr_to_previous = (_dlp_);
          (_dlp_)->ptr_to_next = (second);
          if ((second)->ptr_to_next != NULL)
            (second)->ptr_to_next->ptr_to_previous = (second);
        }
      };
    }
  };
}
void sglib_dllist_delete(dllist **list, dllist *elem) {
  {
    dllist *_l_;
    _l_ = (*list);
    if (_l_ == (elem)) {
      if ((elem)->ptr_to_previous != NULL)
        _l_ = (elem)->ptr_to_previous;
      else
        _l_ = (elem)->ptr_to_next;
    }
    if ((elem)->ptr_to_next != NULL)
      (elem)->ptr_to_next->ptr_to_previous = (elem)->ptr_to_previous;
    if ((elem)->ptr_to_previous != NULL)
      (elem)->ptr_to_previous->ptr_to_next = (elem)->ptr_to_next;
    (*list) = _l_;
  };
}
int sglib_dllist_delete_if_member(dllist **list, dllist *elem,
                                  dllist **member) {
  {
    dllist *_dlp_;
    for (_dlp_ = (*list); _dlp_ != NULL && (_dlp_->i - (elem)->i) != 0;
         _dlp_ = _dlp_->ptr_to_previous)
      ;
    if (_dlp_ == NULL && (*list) != NULL) {
      for (_dlp_ = (*list)->ptr_to_next;
           _dlp_ != NULL && (_dlp_->i - (elem)->i) != 0;
           _dlp_ = _dlp_->ptr_to_next)
        ;
    }
    (*member) = _dlp_;
    if (_dlp_ != NULL) {
      {
        dllist *_l_;
        _l_ = (*list);
        if (_l_ == (_dlp_)) {
          if ((_dlp_)->ptr_to_previous != NULL)
            _l_ = (_dlp_)->ptr_to_previous;
          else
            _l_ = (_dlp_)->ptr_to_next;
        }
        if ((_dlp_)->ptr_to_next != NULL)
          (_dlp_)->ptr_to_next->ptr_to_previous = (_dlp_)->ptr_to_previous;
        if ((_dlp_)->ptr_to_previous != NULL)
          (_dlp_)->ptr_to_previous->ptr_to_next = (_dlp_)->ptr_to_next;
        (*list) = _l_;
      };
    }
  };
  return (*member != NULL);
}
int sglib_dllist_is_member(dllist *list, dllist *elem) {
  int result;
  {
    dllist *_dlp_;
    {
      dllist *_p_;
      for (_p_ = (list); _p_ != NULL && _p_ != (elem);
           _p_ = _p_->ptr_to_previous)
        ;
      (result) = (_p_ != NULL);
    };
    if (result == 0 && (list) != NULL) {
      _dlp_ = (list)->ptr_to_next;
      {
        dllist *_p_;
        for (_p_ = (_dlp_); _p_ != NULL && _p_ != (elem);
             _p_ = _p_->ptr_to_next)
          ;
        (result) = (_p_ != NULL);
      };
    }
  };
  return (result);
}
dllist *sglib_dllist_find_member(dllist *list, dllist *elem) {
  dllist *result;
  {
    dllist *_dlp_;
    {
      dllist *_p_;
      for (_p_ = (list); _p_ != NULL && (_p_->i - (elem)->i) != 0;
           _p_ = _p_->ptr_to_previous)
        ;
      (result) = _p_;
    };
    if ((result) == NULL && (list) != NULL) {
      _dlp_ = (list)->ptr_to_next;
      {
        dllist *_p_;
        for (_p_ = (_dlp_); _p_ != NULL && (_p_->i - (elem)->i) != 0;
             _p_ = _p_->ptr_to_next)
          ;
        (result) = _p_;
      };
    }
  };
  return (result);
}
/*@ requires list == \null || in_live_list(list);
    assigns \nothing;
    ensures list == \null ==> \result == \null;
    // the result heads the same live list that contains list
    ensures heads_list: list != \null ==>
      \exists \list<dllist *> s, integer k;
        live_dll(\null, \result, s) && 0 <= k < \length(s)
        && \nth(s, k) == list;
*/
dllist *sglib_dllist_get_first(dllist *list) {
  dllist *result;
  {
    dllist *_dll_;
    _dll_ = (list);
    if (_dll_ != NULL) {
      /*@ loop invariant \exists \list<dllist *> s, integer k, integer j;
            live_dll(\null, \nth(s, 0), s) && 0 <= k < \length(s)
            && 0 <= j < \length(s) && \nth(s, k) == _dll_
            && \nth(s, j) == list;
          loop assigns _dll_;
      */
      for (; _dll_->ptr_to_previous != NULL; _dll_ = _dll_->ptr_to_previous)
        ;
    }
    (result) = _dll_;
  };
  return (result);
}
/*@ requires list == \null || in_live_list(list);
    assigns \nothing;
    ensures list == \null ==> \result == \null;
    // the result is the last node of the same live list that contains list
    ensures last_of_list: list != \null ==>
      \exists dllist *h, \list<dllist *> s, integer k;
        live_dll(\null, h, s) && 0 <= k < \length(s)
        && \nth(s, k) == list && \result == \nth(s, \length(s) - 1);
*/
dllist *sglib_dllist_get_last(dllist *list) {
  dllist *result;
  {
    dllist *_dll_;
    _dll_ = (list);
    if (_dll_ != NULL) {
      /*@ loop invariant \exists \list<dllist *> s, integer k, integer j;
            live_dll(\null, \nth(s, 0), s) && 0 <= k < \length(s)
            && 0 <= j < \length(s) && \nth(s, k) == _dll_
            && \nth(s, j) == list;
          loop assigns _dll_;
      */
      for (; _dll_->ptr_to_next != NULL; _dll_ = _dll_->ptr_to_next)
        ;
    }
    (result) = _dll_;
  };
  return (result);
}
void sglib_dllist_sort(dllist **list) {
  {
    dllist *_dll_, *_dlp_, *_dlt_;
    _dll_ = (*list);
    if (_dll_ != NULL) {
      for (; _dll_->ptr_to_previous != NULL; _dll_ = _dll_->ptr_to_previous)
        ;
      {
        dllist *_r_;
        dllist *_a_, *_b_, *_todo_, *_t_, **_restail_;
        int _i_, _n_, _contFlag_;
        _r_ = (_dll_);
        _contFlag_ = 1;
        for (_n_ = 1; _contFlag_; _n_ = _n_ + _n_) {
          _todo_ = _r_;
          _r_ = NULL;
          _restail_ = &_r_;
          _contFlag_ = 0;
          while (_todo_ != NULL) {
            _a_ = _todo_;
            for (_i_ = 1, _t_ = _a_; _i_ < _n_ && _t_ != NULL;
                 _i_++, _t_ = _t_->ptr_to_next)
              ;
            if (_t_ == NULL) {
              *_restail_ = _a_;
              break;
            }
            _b_ = _t_->ptr_to_next;
            _t_->ptr_to_next = NULL;
            for (_i_ = 1, _t_ = _b_; _i_ < _n_ && _t_ != NULL;
                 _i_++, _t_ = _t_->ptr_to_next)
              ;
            if (_t_ == NULL) {
              _todo_ = NULL;
            } else {
              _todo_ = _t_->ptr_to_next;
              _t_->ptr_to_next = NULL;
            }
            while (_a_ != NULL && _b_ != NULL) {
              if ((_a_->i - _b_->i) < 0) {
                *_restail_ = _a_;
                _restail_ = &(_a_->ptr_to_next);
                _a_ = _a_->ptr_to_next;
              } else {
                *_restail_ = _b_;
                _restail_ = &(_b_->ptr_to_next);
                _b_ = _b_->ptr_to_next;
              }
            }
            if (_a_ != NULL)
              *_restail_ = _a_;
            else
              *_restail_ = _b_;
            while (*_restail_ != NULL)
              _restail_ = &((*_restail_)->ptr_to_next);
            _contFlag_ = 1;
          }
        }
        (_dll_) = _r_;
      };
      {
        dllist *_dlp_, *_dlt_;
        _dlp_ = NULL;
        for (_dlt_ = (_dll_); _dlt_ != NULL; _dlt_ = _dlt_->ptr_to_next) {
          _dlt_->ptr_to_previous = _dlp_;
          _dlp_ = _dlt_;
        }
      };
      (*list) = _dll_;
    }
  };
}
int sglib_dllist_len(dllist *list) {
  int res;
  {
    dllist *_dl_;
    int _r1_, _r2_;
    if ((list) == NULL) {
      (res) = 0;
    } else {
      {
        (_r1_) = 0;
        {
          dllist *_ne_;
          dllist *_ce_;
          (_ce_) = (list);
          while ((_ce_) != NULL) {
            _ne_ = (_ce_)->ptr_to_previous;
            { (_r1_)++; };
            (_ce_) = _ne_;
          }
        };
      };
      _dl_ = (list)->ptr_to_next;
      {
        (_r2_) = 0;
        {
          dllist *_ne_;
          dllist *_ce_;
          (_ce_) = (_dl_);
          while ((_ce_) != NULL) {
            _ne_ = (_ce_)->ptr_to_next;
            { (_r2_)++; };
            (_ce_) = _ne_;
          }
        };
      };
      (res) = _r1_ + _r2_;
    }
  };
  return (res);
}
void sglib_dllist_reverse(dllist **list) {
  {
    dllist *_list_, *_nlist_, *_dlp_, *_dln_;
    _list_ = (*list);
    if (_list_ != NULL) {
      _nlist_ = _list_->ptr_to_next;
      while (_list_ != NULL) {
        _dln_ = _list_->ptr_to_next;
        _dlp_ = _list_->ptr_to_previous;
        _list_->ptr_to_next = _dlp_;
        _list_->ptr_to_previous = _dln_;
        _list_ = _dlp_;
      }
      while (_nlist_ != NULL) {
        _dln_ = _nlist_->ptr_to_next;
        _dlp_ = _nlist_->ptr_to_previous;
        _nlist_->ptr_to_next = _dlp_;
        _nlist_->ptr_to_previous = _dln_;
        _nlist_ = _dln_;
      }
    }
  };
}
/*@ requires \valid(it) && !heap(\base_addr(it));
    requires subcomparator == \null;
    requires \exists \list<dllist *> s; live_dll(\null, list, s);
    assigns *it;
    ensures iter_ok(it, \result);
*/
dllist *sglib_dllist_it_init_on_equal(struct sglib_dllist_iterator *it,
                                      dllist *list,
                                      int (*subcomparator)(dllist *, dllist *),
                                      dllist *equalto) {
  /*@ assert list == \null ||
        \exists \list<dllist *> t; live_dll(\null, list, \Cons(list, t)); */
  it->subcomparator = subcomparator;
  it->equalto = equalto;
  it->prevelem = list;
  it->nextelem = list;
  if (list != NULL)
    it->nextelem = list->ptr_to_next;
  /*@ assert \forall \list<dllist *> t; all_live{Pre}(t) ==>
        unchanged{Pre, Here}(t) && (all_init{Pre}(t) ==> all_init(t)); */
  /*@ assert list == \null ||
        \exists \list<dllist *> t; live_dll(\null, list, \Cons(list, t)); */
  return (sglib_dllist_it_next(it));
}
/*@ requires \valid(it) && !heap(\base_addr(it));
    requires \exists \list<dllist *> s; live_dll(\null, list, s);
    assigns *it;
    ensures iter_ok(it, \result);
*/
dllist *sglib_dllist_it_init(struct sglib_dllist_iterator *it, dllist *list) {
  return (sglib_dllist_it_init_on_equal(it, list, NULL, NULL));
}
dllist *sglib_dllist_it_current(struct sglib_dllist_iterator *it) {
  return (it->currentelem);
}
/*@ requires \valid(it) && !heap(\base_addr(it));
    requires it->subcomparator == \null;
    requires \initialized(&it->subcomparator) && \initialized(&it->prevelem)
             && \initialized(&it->nextelem);
    requires
      (it->prevelem == \null
       && \exists dllist *p, \list<dllist *> t;
            live_dll(p, it->nextelem, t))
      || (it->prevelem != \null
          && \exists \list<dllist *> t;
               live_dll(\null, it->prevelem, \Cons(it->prevelem, t))
               && it->nextelem == it->prevelem->ptr_to_next);
    assigns *it;
    ensures iter_ok(it, \result);
*/
dllist *sglib_dllist_it_next(struct sglib_dllist_iterator *it) {
  dllist *ce, *eq;
  int (*scp)(dllist *, dllist *);
  /*@ assert \exists dllist *p, \list<dllist *> t;
        (it->prevelem == \null ==> live_dll(p, it->nextelem, t))
        && (it->prevelem != \null ==>
              live_dll(it->prevelem, it->nextelem, t) && live(it->prevelem)
              && !mem(it->prevelem, t)
              && it->prevelem->ptr_to_previous == \null); */
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
  /*@ assert \forall \list<dllist *> t; all_live{Pre}(t) ==>
        unchanged{Pre, Here}(t) && (all_init{Pre}(t) ==> all_init(t)); */
  /*@ assert \exists dllist *p, \list<dllist *> t;
        live_dll{Pre}(p, it->nextelem, t)
        && (ce == \null ==> it->nextelem == \null)
        && (ce != \null ==> live(ce) && !mem(ce, t)); */
  it->currentelem = ce;
  /*@ assert \forall \list<dllist *> t; all_live{Pre}(t) ==>
        unchanged{Pre, Here}(t) && (all_init{Pre}(t) ==> all_init(t)); */
  return (ce);
};
/* END GENERATED, part 2 */

/* Driver for B1a: build a list from input[0..n-1] with sglib_dllist_add,
   walk it forward from sglib_dllist_get_first and backward from
   sglib_dllist_get_last (B1b, as the sample does), then free every element
   while iterating (the sample's last loop).  Returns the last value seen by the walk. */
/*@ requires 0 <= n && \valid_read(input + (0 .. n - 1));
    requires \initialized(input + (0 .. n - 1));
    requires !heap(\base_addr(input));
*/
int b1(const int *input, int n) {
  dllist *l = NULL, *the_list = NULL;
  struct sglib_dllist_iterator it;
  int last = 0;
  //@ assert live_dll(\null, the_list, \Nil);
  /*@ loop invariant 0 <= k <= n;
      loop invariant \initialized(input + (0 .. n - 1));
      loop invariant \initialized(&the_list);
      loop invariant \exists \list<dllist *> s;
                       live_dll(\null, the_list, s);
      loop assigns k, l, the_list, __heap, the_list->ptr_to_previous,
                   { *q | dllist *q; heap(\base_addr(q)) };
  */
  for (int k = 0; k < n; k++) {
  before_alloc:
    l = ariadne_alloc_dllist();
    /*@ assert \forall char *b; heap(b) ==>
          !dead(\at(__heap, before_alloc), b) ==>
          !dead(__heap, b) && (l != \null ==> b != \base_addr(l)); */
    /*@ assert \exists \list<dllist *> s; live_dll(\null, the_list, s)
          && (l != \null ==> !mem(l, s)); */
    if (l == NULL)
      break;
    l->i = input[k];
    //@ assert \exists \list<dllist *> s; live_dll(\null, the_list, s) && !mem(l, s);
    sglib_dllist_add(&the_list, l);
  }
  //@ assert \exists \list<dllist *> s; live_dll(\null, the_list, s);
  /*@ loop invariant \exists dllist *p, \list<dllist *> t; live_dll(p, l, t);
      loop assigns l, last;
  */
  for (l = sglib_dllist_get_first(the_list); l != NULL; l = l->ptr_to_next)
    last = l->i;
  /*@ loop invariant l == \null || in_live_list(l);
      loop assigns l, last;
  */
  for (l = sglib_dllist_get_last(the_list); l != NULL;
       l = l->ptr_to_previous)
    last = l->i;
  /*@ loop invariant iter_ok(&it, l);
      loop assigns l, it, __heap;
  */
  for (l = sglib_dllist_it_init(&it, the_list); l != NULL;
       l = sglib_dllist_it_next(&it)) {
  before_free:
    /*@ assert \exists dllist *p, \list<dllist *> t;
          live_dll(p, it.nextelem, t) && live(l) && !mem(l, t); */
    ariadne_free_dllist(l);
    /*@ assert \forall \list<dllist *> t;
          all_live{before_free}(t) ==> !mem(l, t) ==> all_live(t); */
    /*@ assert \exists dllist *p, \list<dllist *> t;
          live_dll(p, it.nextelem, t); */
  }
  return last;
}
