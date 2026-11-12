/* Benchmark B1a (plan section 6.2): sglib's doubly linked list, from
   samples/dllist.c.  The code between the BEGIN/END GENERATED markers is
   b1_gen.c (./gen.sh) byte for byte, with ACSL annotations inserted;
   everything else is ours: the ghost model, the shape predicates, and a
   driver replacing the sample's main (input array instead of argv/sscanf,
   no printf, ariadne allocators instead of malloc/free, NULL check added,
   l initialised to NULL; see README "Initialisation").

   Specification status: the predicates and contracts below are the
   human-reviewed, frozen spec of plan section 4 (guardrail 3a).  */

#include <assert.h>
#include <stddef.h>
#include "ariadne_alloc.h"
#include "sglib_dl_list_spec.h"

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

/*@ // The fields DLLIST_COMPARATOR reads (template parameter
    // cmp_reads).
    predicate dllist_cmp_reads{L}(dllist *p) = \initialized(&p->i);
    SGLIB_DL_LIST_SPEC(dllist, ptr_to_previous, ptr_to_next,
                       dllist_cmp_reads)
    SGLIB_DL_LIST_LEMMAS(dllist, ptr_to_previous, ptr_to_next)
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
/*@ SGLIB_DL_LIST_CONTRACT_ADD(dllist, ptr_to_previous, ptr_to_next) */
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
    /*@ SGLIB_DL_LIST_ANNOT_ADD_SINGLE(
          dllist, ptr_to_previous, ptr_to_next) */
    /*@ SGLIB_DL_LIST_ANNOT_ADD_OLD_PREV(
          dllist, ptr_to_previous, ptr_to_next) */
    /*@ SGLIB_DL_LIST_ANNOT_ADD_KEEP_PREV(
          dllist, ptr_to_previous, ptr_to_next) */
    /*@ SGLIB_DL_LIST_ANNOT_ADD_KEEP_NEXT(
          dllist, ptr_to_previous, ptr_to_next) */
    /*@ SGLIB_DL_LIST_ANNOT_ADD_KEEP_INIT(
          dllist, ptr_to_previous, ptr_to_next) */
    /*@ SGLIB_DL_LIST_ANNOT_ADD_FRAME_PREV(
          dllist, ptr_to_previous, ptr_to_next) */
    /*@ SGLIB_DL_LIST_ANNOT_ADD_FRAME_NEXT(
          dllist, ptr_to_previous, ptr_to_next) */
    /*@ SGLIB_DL_LIST_ANNOT_ADD_WRITTEN(
          dllist, ptr_to_previous, ptr_to_next) */
    /*@ SGLIB_DL_LIST_ANNOT_ADD_LINKS(
          dllist, ptr_to_previous, ptr_to_next) */
    /*@ SGLIB_DL_LIST_ANNOT_ADD_DISTINCT(
          dllist, ptr_to_previous, ptr_to_next) */
    /*@ SGLIB_DL_LIST_ANNOT_ADD_NEW_DLL(
          dllist, ptr_to_previous, ptr_to_next) */
    /*@ SGLIB_DL_LIST_ANNOT_ADD_NEW_LIVE(
          dllist, ptr_to_previous, ptr_to_next) */
    /*@ SGLIB_DL_LIST_ANNOT_ADD_OLD_FRESH(
          dllist, ptr_to_previous, ptr_to_next) */
    /*@ SGLIB_DL_LIST_ANNOT_ADD_OLD_HEAD(
          dllist, ptr_to_previous, ptr_to_next) */
    /*@ SGLIB_DL_LIST_ANNOT_ADD_INSERT_LIST(
          dllist, ptr_to_previous, ptr_to_next) */
    /*@ SGLIB_DL_LIST_ANNOT_ADD_INSERTED(
          dllist, ptr_to_previous, ptr_to_next) */
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
      for (_dlp_ = (*list); _dlp_ != NULL && ((_dlp_->i > (elem)->i) -
                                              (_dlp_->i < (elem)->i)) != 0;
           _dlp_ = _dlp_->ptr_to_previous)
        ;
      if (_dlp_ == NULL && (*list) != NULL) {
        for (_dlp_ = (*list)->ptr_to_next;
             _dlp_ != NULL &&
             ((_dlp_->i > (elem)->i) - (_dlp_->i < (elem)->i)) != 0;
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
      for (_dlp_ = (*list); _dlp_ != NULL && ((_dlp_->i > (elem)->i) -
                                              (_dlp_->i < (elem)->i)) != 0;
           _dlp_ = _dlp_->ptr_to_previous)
        ;
      if (_dlp_ == NULL && (*list) != NULL) {
        for (_dlp_ = (*list)->ptr_to_next;
             _dlp_ != NULL &&
             ((_dlp_->i > (elem)->i) - (_dlp_->i < (elem)->i)) != 0;
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
      for (_dlp_ = (*list); _dlp_ != NULL && ((_dlp_->i > (elem)->i) -
                                              (_dlp_->i < (elem)->i)) != 0;
           _dlp_ = _dlp_->ptr_to_previous)
        ;
      if (_dlp_ == NULL && (*list) != NULL) {
        for (_dlp_ = (*list)->ptr_to_next;
             _dlp_ != NULL &&
             ((_dlp_->i > (elem)->i) - (_dlp_->i < (elem)->i)) != 0;
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
    for (_dlp_ = (*list); _dlp_ != NULL && ((_dlp_->i > (elem)->i) -
                                            (_dlp_->i < (elem)->i)) != 0;
         _dlp_ = _dlp_->ptr_to_previous)
      ;
    if (_dlp_ == NULL && (*list) != NULL) {
      for (_dlp_ = (*list)->ptr_to_next;
           _dlp_ != NULL &&
           ((_dlp_->i > (elem)->i) - (_dlp_->i < (elem)->i)) != 0;
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
      for (_p_ = (list);
           _p_ != NULL && ((_p_->i > (elem)->i) - (_p_->i < (elem)->i)) != 0;
           _p_ = _p_->ptr_to_previous)
        ;
      (result) = _p_;
    };
    if ((result) == NULL && (list) != NULL) {
      _dlp_ = (list)->ptr_to_next;
      {
        dllist *_p_;
        for (_p_ = (_dlp_);
             _p_ != NULL && ((_p_->i > (elem)->i) - (_p_->i < (elem)->i)) != 0;
             _p_ = _p_->ptr_to_next)
          ;
        (result) = _p_;
      };
    }
  };
  return (result);
}
/*@ SGLIB_DL_LIST_CONTRACT_GET_FIRST(dllist, ptr_to_previous, ptr_to_next) */
dllist *sglib_dllist_get_first(dllist *list) {
  dllist *result;
  {
    dllist *_dll_;
    _dll_ = (list);
    if (_dll_ != NULL) {
      /*@ SGLIB_DL_LIST_ANNOT_GET_FIRST_LOOP(
            dllist, ptr_to_previous, ptr_to_next) */
      for (; _dll_->ptr_to_previous != NULL; _dll_ = _dll_->ptr_to_previous)
        ;
      /*@ SGLIB_DL_LIST_ANNOT_GET_FIRST_AT_HEAD(
            dllist, ptr_to_previous, ptr_to_next) */
    }
    (result) = _dll_;
  };
  return (result);
}
/*@ SGLIB_DL_LIST_CONTRACT_GET_LAST(dllist, ptr_to_previous, ptr_to_next) */
dllist *sglib_dllist_get_last(dllist *list) {
  dllist *result;
  {
    dllist *_dll_;
    _dll_ = (list);
    if (_dll_ != NULL) {
      /*@ SGLIB_DL_LIST_ANNOT_GET_LAST_LOOP(
            dllist, ptr_to_previous, ptr_to_next) */
      for (; _dll_->ptr_to_next != NULL; _dll_ = _dll_->ptr_to_next)
        ;
      /*@ SGLIB_DL_LIST_ANNOT_GET_LAST_AT_LAST(
            dllist, ptr_to_previous, ptr_to_next) */
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
              if (((_a_->i > _b_->i) - (_a_->i < _b_->i)) < 0) {
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
/*@ SGLIB_DL_LIST_CONTRACT_IT_INIT_ON_EQUAL(
      dllist, ptr_to_previous, ptr_to_next, dllist_cmp_reads, (0)) */
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
  /*@ SGLIB_DL_LIST_ANNOT_IT_FRAME(dllist, ptr_to_previous, ptr_to_next) */
  /*@ SGLIB_DL_LIST_ANNOT_IT_INIT_FRAME(
        dllist, ptr_to_previous, ptr_to_next) */
  /*@ SGLIB_DL_LIST_ANNOT_IT_START_CMP(dllist, ptr_to_previous, ptr_to_next) */
  /*@ SGLIB_DL_LIST_ANNOT_IT_START(dllist, ptr_to_previous, ptr_to_next) */
  /*@ SGLIB_DL_LIST_ANNOT_IT_START_NODE(dllist, ptr_to_previous, ptr_to_next) */
  return (sglib_dllist_it_next(it));
}
/*@ SGLIB_DL_LIST_CONTRACT_IT_INIT(dllist, ptr_to_previous, ptr_to_next) */
dllist *sglib_dllist_it_init(struct sglib_dllist_iterator *it, dllist *list) {
  return (sglib_dllist_it_init_on_equal(it, list, NULL, NULL));
}
dllist *sglib_dllist_it_current(struct sglib_dllist_iterator *it) {
  return (it->currentelem);
}
/*@ SGLIB_DL_LIST_CONTRACT_IT_NEXT(dllist, ptr_to_previous, ptr_to_next,
                                    (0)) */
dllist *sglib_dllist_it_next(struct sglib_dllist_iterator *it) {
  dllist *ce, *eq;
  int (*scp)(dllist *, dllist *);
  ce = it->prevelem;
  it->prevelem = NULL;
  if (it->subcomparator != NULL) {
    eq = it->equalto;
    scp = it->subcomparator;
    /*@ SGLIB_DL_LIST_ANNOT_IT_NEXT_BACK_LOOP(
          dllist, ptr_to_previous, ptr_to_next) */
    while (ce != NULL) {
      /*@ SGLIB_DL_LIST_ANNOT_IT_NEXT_CALLS((0)) */
      if (scp(eq, ce) == 0)
        break;
      ce = ce->ptr_to_previous;
    }
  }
  /*@ SGLIB_DL_LIST_ANNOT_IT_NEXT_MID_BACK(dllist, ptr_to_previous, ptr_to_next) */
  if (ce != NULL) {
    it->prevelem = ce->ptr_to_previous;
  } else {
    ce = it->nextelem;
    it->nextelem = NULL;
    if (it->subcomparator != NULL) {
      eq = it->equalto;
      scp = it->subcomparator;
      /*@ SGLIB_DL_LIST_ANNOT_IT_NEXT_FWD_LOOP(
            dllist, ptr_to_previous, ptr_to_next) */
      while (ce != NULL) {
        /*@ SGLIB_DL_LIST_ANNOT_IT_NEXT_CALLS((0)) */
        if (scp(ce, eq) == 0)
          break;
        ce = ce->ptr_to_next;
      }
    }
    /*@ SGLIB_DL_LIST_ANNOT_IT_NEXT_MID_FWD(dllist, ptr_to_previous, ptr_to_next) */
    if (ce != NULL)
      it->nextelem = ce->ptr_to_next;
  }
  it->currentelem = ce;
  /*@ SGLIB_DL_LIST_ANNOT_IT_FRAME(dllist, ptr_to_previous, ptr_to_next) */
  /*@ SGLIB_DL_LIST_ANNOT_IT_INIT_FRAME(
        dllist, ptr_to_previous, ptr_to_next) */
  /*@ SGLIB_DL_LIST_ANNOT_IT_NEXT_IT_INIT(
        dllist, ptr_to_previous, ptr_to_next) */
  /*@ SGLIB_DL_LIST_ANNOT_IT_NEXT_CMP_FRAME(
        dllist, ptr_to_previous, ptr_to_next) */
  /*@ SGLIB_DL_LIST_ANNOT_IT_NEXT_EQ_FRAME(
        dllist, ptr_to_previous, ptr_to_next) */
  /*@ SGLIB_DL_LIST_ANNOT_IT_NEXT_FOUND(dllist, ptr_to_previous, ptr_to_next) */
  /*@ SGLIB_DL_LIST_ANNOT_IT_NEXT_CE_LIVE(dllist, ptr_to_previous, ptr_to_next) */
  /*@ SGLIB_DL_LIST_ANNOT_IT_NEXT_BACK(dllist, ptr_to_previous, ptr_to_next) */
  /*@ SGLIB_DL_LIST_ANNOT_IT_NEXT_FORWARD(dllist, ptr_to_previous, ptr_to_next) */
  /*@ SGLIB_DL_LIST_ANNOT_IT_NEXT_END(dllist, ptr_to_previous, ptr_to_next) */
  /*@ SGLIB_DL_LIST_ANNOT_IT_NEXT_OK_BACK(dllist, ptr_to_previous, ptr_to_next) */
  /*@ SGLIB_DL_LIST_ANNOT_IT_NEXT_OK_FORWARD(
        dllist, ptr_to_previous, ptr_to_next) */
  /*@ SGLIB_DL_LIST_ANNOT_IT_NEXT_OK_END(dllist, ptr_to_previous, ptr_to_next) */
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
    // every live node's payload is initialised (the walks read it, and
    // the list predicates cover only the links)
    requires payload_init: \forall dllist *q; live(q) ==> \initialized(&q->i);
*/
int b1(const int *input, int n) {
  dllist *l = NULL, *the_list = NULL;
  struct sglib_dllist_iterator it;
  int last = 0;
  //@ assert live_dll(\null, the_list, \Nil);
  /*@ loop invariant 0 <= k <= n;
      loop invariant !dead(__heap, \base_addr(input));
      loop invariant \initialized(&the_list);
      loop invariant \initialized(input + (0 .. n - 1));
      loop invariant \exists \list<dllist *> s; live_dll(\null, the_list, s);
      loop invariant payload_init:
        \forall dllist *q; live(q) ==> \initialized(&q->i);
      loop assigns k, l, the_list, __heap,
        { q->i | dllist *q; heap(\base_addr(q)) },
        { q->ptr_to_next | dllist *q },
        { q->ptr_to_previous | dllist *q; heap(\base_addr(q)) };
      loop variant n - k;
  */
  for (int k = 0; k < n; k++) {
  before_alloc:
    l = ariadne_alloc_dllist();
    if (l == NULL)
      break;
    /*@ assert old_nodes_live:
          \forall dllist *q; live{before_alloc}(q) ==> live(q) && q != l; */
    /*@ assert old_lists_live:
          \forall \list<dllist *> s;
            all_live{before_alloc}(s) ==> all_live(s) && !mem(l, s); */
    l->i = input[k];
    /*@ assert old_head: the_list == \null
          || the_list->ptr_to_previous == \null; */
    /*@ assert add_pre: the_list == \null
          || \exists \list<dllist *> s; live_dll(\null, the_list, s)
             && the_list == \nth(s, 0) && !mem(l, s); */
    /*@ assert payload_written:
          \forall dllist *q; live(q) ==> \initialized(&q->i); */
    sglib_dllist_add(&the_list, l);
    /*@ assert head_after_add:
          \exists \list<dllist *> s; live_dll(\null, the_list, s); */
    /*@ assert payload_kept:
          \forall dllist *q; live(q) ==> \initialized(&q->i); */
  }
  /*@ assert head_is_node0:
        the_list == \null
        || \exists \list<dllist *> t;
             live_dll(\null, the_list, \Cons(the_list, t)); */
  /*@ loop invariant l == \null || in_live_list(l);
      loop invariant l != \null ==> live(l);
      loop assigns l, last;
  */
  for (l = sglib_dllist_get_first(the_list); l != NULL; l = l->ptr_to_next)
    last = l->i;
  /*@ loop invariant l == \null || in_live_list(l);
      loop invariant l != \null ==> live(l);
      loop assigns l, last;
  */
  for (l = sglib_dllist_get_last(the_list); l != NULL;
       l = l->ptr_to_previous)
    last = l->i;
  /*@ assert start_node: the_list == \null || in_live_list(the_list); */
  /*@ loop invariant l == \null
        || \exists \list<dllist *> s; iter_ok(&it, s, l);
      loop invariant it.subcomparator == \null;
      loop invariant payload_init:
        \forall dllist *q; live(q) ==> \initialized(&q->i);
      loop assigns l, it, __heap;
  */
  for (l = sglib_dllist_it_init(&it, the_list); l != NULL;
       l = sglib_dllist_it_next(&it)) {
  before_free:
    ariadne_free_dllist(l);
    /*@ assert others_live:
          \forall dllist *q; live{before_free}(q) && q != l ==> live(q); */
    /*@ assert iter_after_free:
          \forall \list<dllist *> s, integer b, f, c;
            iter_at{before_free}(&it, s, b, f) && b < c < f
            && l == \nth(s, c) ==> iter_at(&it, s, b, f); */
  }
  return last;
}
