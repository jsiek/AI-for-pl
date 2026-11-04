/* Runtime support for generated executable twins (gen_twins.py): the
   allocation registry (the executable heap / dead of ariadne_alloc.h),
   \list values, and the step bound.  Hand-written and spec-independent;
   test code only, nothing here enters a proof.

   Only basic types appear here (lists are `long` handles at the
   interface), so the header can be force-included (gcc -include) before
   E-ACSL's output, like the generated <prefix>_twins.h. */
#ifndef RAC_RT_H
#define RAC_RT_H

/* ---- Allocation registry ---------------------------------------------
   The ariadne allocators call rac_reg_alloc / rac_reg_free; the twins and
   the spec ask the registry instead of reading E-ACSL's shadow memory
   (which plain C cannot query). */
void rac_reg_alloc(void *b, unsigned long size);  /* b was returned by
                                                     ariadne_alloc_T */
void rac_reg_free(void *b);     /* b is passed to ariadne_free_T */
int rac_heap(char *b);          /* heap(b): b ever returned by an allocator */
int rac_dead(char *b);          /* dead(__heap, b): b freed since */
int rac_heap_of(void *p);       /* heap(\base_addr(p)) */
int rac_dead_of(void *p);       /* dead(__heap, \base_addr(p)) */
/* The twins' \valid(p) for an object of `size` bytes at p: p lies, with
   all its bytes, in a registered block that is not freed. */
int rac_valid(const void *p, unsigned long size);

/* ---- \list values -----------------------------------------------------
   A list is a handle (long); 0 is \Nil.  These are E-ACSL builtins
   (element type independent); <prefix>_twins.h adds rac_cons for the
   element type of the spec. */
long rac_length(long s);         /* \length(s) */
long rac_nth(long s, long k);    /* \nth(s, k) (0 out of range) */
long rac_tail(long s);           /* t with s == \Cons(_, t); \Nil for \Nil */
long rac_concat(long s, long t); /* \concat(s, t) */

/* Test harness: free every list value; empty the registry. */
void rac_reset(void);

#ifdef RAC_TWIN_IMPL
/* ---- For generated code only ---------------------------------------- */
struct rac_seq;
/* "No witness": a computation left the live heap or ran out of steps.
   A list of length 0 that is not \Nil, so no twin accepts it. */
extern struct rac_seq rac_bad_seq;
#define RAC_BAD (&rac_bad_seq)
long rac_seq_len(struct rac_seq *s);
void *rac_seq_nth(struct rac_seq *s, long k);
void *rac_seq_hd(struct rac_seq *s);               /* s non-empty */
struct rac_seq *rac_seq_tl(struct rac_seq *s);     /* s non-empty */
struct rac_seq *rac_seq_cons(void *h, struct rac_seq *t);
struct rac_seq *rac_seq_concat(struct rac_seq *a, struct rac_seq *b);
int rac_seq_eq(struct rac_seq *a, struct rac_seq *b);
int rac_seq_is_nil(struct rac_seq *s);             /* s == \Nil */
int rac_seq_is_cons(struct rac_seq *s);            /* s == \Cons(_, _) */
/* rac_tail on values: the tail of a \Cons, \Nil for \Nil, bad for bad. */
struct rac_seq *rac_seq_tail(struct rac_seq *s);

/* Step bound: every twin call spends a step and is one level deeper; a
   computation over RAC_FUEL steps or RAC_DEPTH levels fails (false, or
   no witness), so a cyclic or corrupt heap cannot hang the run or
   overflow the C stack.  Each builtin restarts the count. */
extern long rac_steps;
int rac_tick(int depth);
#endif

#endif
