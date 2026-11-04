/* Executable twins of B1's logic definitions (plan section 4 item 5).
   Prototypes only, in struct form (no typedefs), so this header can be
   force-included (gcc -include) before the instrumented code, which
   E-ACSL prints without the prototypes of functions used only in logic.

   Each function here is an E-ACSL builtin (-e-acsl-builtins): ACSL
   annotations call it like a logic function.  Test code only; nothing
   here enters a proof. */
#ifndef RAC_TWINS_H
#define RAC_TWINS_H


/* Allocation registry: the executable heap/dead of ariadne_alloc.h. */
void rac_reg_alloc(void *b, unsigned long size);  /* b was returned by
                                                     ariadne_alloc_T */
void rac_reg_free(void *b);     /* b is passed to ariadne_free_T */
int rac_heap(char *b);          /* heap(b): b ever returned by an allocator */
int rac_dead(char *b);          /* dead(__heap, b): b freed since */
int rac_heap_of(void *p);       /* heap(\base_addr(p)) */
int rac_dead_of(void *p);       /* dead(__heap, \base_addr(p)) */

struct dllist;

/* \list<dllist *> values are handles (rac_list, a long); 0 is \Nil.
   Results that are nodes are returned as long (README, "E-ACSL
   workarounds"); node arguments are pointers. */
long rac_length(long s);                 /* \length(s) */
long rac_nth(long s, long k);            /* \nth(s, k) */
long rac_cons(struct dllist *h, long t);  /* \Cons(h, t) */
long rac_tail(long s);                   /* t with s == \Cons(_, t);
                                            \Nil for \Nil */

/* Twin of the inductive dll{L}(prev, h, s). */
int rac_dll(struct dllist *prev, struct dllist *h, long s);

/* Witnesses for existentials over dll (README, "Witnesses"). */
long rac_reach(struct dllist *h);  /* the s with dll(_, h, s) */
long rac_prev(struct dllist *h);   /* the p with dll(p, h, _) */
long rac_head(struct dllist *x);   /* the h with dll(\null, h, s)
                                       and mem(x, s) */

/* Test harness: free all list values; reset the registry. */
void rac_reset(void);

#endif
