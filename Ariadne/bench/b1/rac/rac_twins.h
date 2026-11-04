/* Executable twins of B1's logic definitions (plan section 4 item 5).
   Prototypes only, in struct form (no typedefs), so this header can be
   force-included (gcc -include) before the instrumented code, which
   E-ACSL prints without the prototypes of functions used only in logic.

   Each function here is an E-ACSL builtin (-e-acsl-builtins): ACSL
   annotations call it like a logic function.  Test code only; nothing
   here enters a proof. */
#ifndef RAC_TWINS_H
#define RAC_TWINS_H

struct dllist;
struct rac_seq;                 /* a \list<dllist *> value (immutable) */

/* Allocation registry: the executable heap/dead of ariadne_alloc.h. */
void rac_reg_alloc(void *b);    /* b was returned by ariadne_alloc_T */
void rac_reg_free(void *b);     /* b is passed to ariadne_free_T */
int rac_heap(char *b);          /* heap(b): b ever returned by an allocator */
int rac_dead(char *b);          /* dead(__heap, b): b freed since */

/* \list<dllist *> values.  A NULL handle is \Nil. */
long rac_length(struct rac_seq *s);                     /* \length(s) */
struct dllist *rac_nth(struct rac_seq *s, long k);      /* \nth(s, k) */
struct rac_seq *rac_cons(struct dllist *h, struct rac_seq *t);  /* \Cons */
struct rac_seq *rac_tail(struct rac_seq *s);   /* t with s == \Cons(_, t);
                                                  \Nil for \Nil */

/* Twin of the inductive dll{L}(prev, h, s). */
int rac_dll(struct dllist *prev, struct dllist *h, struct rac_seq *s);

/* Witnesses for existentials over dll (README, "Witnesses"). */
struct rac_seq *rac_reach(struct dllist *h);  /* the s with dll(_, h, s) */
struct dllist *rac_prev(struct dllist *h);    /* the p with dll(p, h, _) */
struct dllist *rac_head(struct dllist *x);    /* the h with dll(\null, h, s),
                                                 mem(x, s) */

/* Test harness: free all list values; reset the registry. */
void rac_reset(void);

#endif
