/* Executable twins of B1's logic definitions (plan section 4 item 5);
   see rac_twins.h and README.md ("Translation rules").

   Written by hand for B1, in the style a generator would use:
     - an inductive predicate becomes a function with one branch per
       case, tried in order; a case applies when the arguments match its
       conclusion, and then its premises are checked left to right, the
       inductive premises by recursive calls;
     - every recursive call and every heap walk spends one unit of a step
       bound (RAC_FUEL), so a cyclic or corrupt heap gives false, never a
       hang;
     - \valid(p) of a node, before reading its fields, is the registry's
       "allocated and not freed" (rac_live_node): plain C cannot ask
       E-ACSL whether memory is valid, and must not read freed memory.

   Not instrumented by E-ACSL (compiled separately and linked), so the
   twins' own reads are not checked; they read only nodes the registry
   says are live. */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include "b1_types.h"   /* struct dllist, written by gen_rac.py from b1.c */
#include "rac_twins.h"

#ifndef RAC_FUEL
#define RAC_FUEL 1000000L
#endif

static void oom(void) {
  static const char msg[] = "rac_twins: out of memory\n";
  (void)!fwrite(msg, 1, sizeof msg - 1, stderr);
  abort();
}

/* ---- Allocation registry (heap, dead) -------------------------------- */

/* Open addressing on block addresses; state 1 = live, 2 = dead. */
static struct reg { void *b; int state; } *reg;
static size_t reg_cap, reg_n;

static size_t reg_hash(void *b) {
  return (size_t)(((unsigned long long)(size_t)b >> 4) * 0x9E3779B97F4A7C15ULL);
}

static struct reg *reg_find(void *b) {
  if (reg_cap == 0)
    return NULL;
  for (size_t i = reg_hash(b) & (reg_cap - 1);; i = (i + 1) & (reg_cap - 1))
    if (reg[i].b == b || reg[i].b == NULL)
      return &reg[i];
}

static void reg_grow(void) {
  struct reg *old = reg;
  size_t old_cap = reg_cap;
  reg_cap = reg_cap ? 2 * reg_cap : 1024;
  reg = calloc(reg_cap, sizeof *reg);
  if (!reg)
    oom();
  for (size_t i = 0; i < old_cap; i++)
    if (old[i].b)
      *reg_find(old[i].b) = old[i];
  free(old);
}

void rac_reg_alloc(void *b) {
  if (2 * (reg_n + 1) > reg_cap)
    reg_grow();
  struct reg *r = reg_find(b);
  if (r->b == NULL)
    reg_n++;
  r->b = b;
  r->state = 1;  /* a freed block may be handed out again: live again */
}

void rac_reg_free(void *b) {
  struct reg *r = reg_find(b);
  if (r && r->b == b)
    r->state = 2;
}

int rac_heap(char *b) {
  struct reg *r = reg_find(b);
  return r && r->b == (void *)b;
}

int rac_dead(char *b) {
  struct reg *r = reg_find(b);
  return r && r->b == (void *)b && r->state == 2;
}

/* The twins' stand-in for \valid(p) on a node: a live registered block. */
static int rac_live_node(dllist *p) {
  return p != NULL && rac_heap((char *)p) && !rac_dead((char *)p);
}

/* ---- \list<dllist *> values ----------------------------------------- */

struct rac_seq {
  long len;
  dllist **a;
};

/* Every list value lives in an arena freed by rac_reset. */
static void **arena;
static size_t arena_n, arena_cap;

static void *arena_alloc(size_t size) {
  if (arena_n == arena_cap) {
    arena_cap = arena_cap ? 2 * arena_cap : 1024;
    arena = realloc(arena, arena_cap * sizeof *arena);
    if (!arena)
      oom();
  }
  void *p = malloc(size ? size : 1);
  if (!p)
    oom();
  return arena[arena_n++] = p;
}

static struct rac_seq *seq_new(long len, dllist **a) {
  struct rac_seq *s = arena_alloc(sizeof *s);
  s->len = len;
  s->a = a;
  return s;
}

/* No witness: a walk left the live heap or ran out of steps.  It is a
   list of length 0 that is not \Nil, so rac_dll is false on it. */
static struct rac_seq bad = {0, NULL};

long rac_length(struct rac_seq *s) { return s ? s->len : 0; }

dllist *rac_nth(struct rac_seq *s, long k) {
  return s && 0 <= k && k < s->len ? s->a[k] : NULL;
}

struct rac_seq *rac_cons(dllist *h, struct rac_seq *t) {
  if (t == &bad)
    return &bad;
  long n = rac_length(t);
  dllist **a = arena_alloc((size_t)(n + 1) * sizeof *a);
  a[0] = h;
  if (n)
    memcpy(a + 1, t->a, (size_t)n * sizeof *a);
  return seq_new(n + 1, a);
}

struct rac_seq *rac_tail(struct rac_seq *s) {
  if (s == &bad)
    return &bad;
  return rac_length(s) <= 1 ? NULL : seq_new(s->len - 1, s->a + 1);
}

/* \Nil and \Cons(h, t) as patterns: is_nil(s), and is_cons(s, &h, &t). */
static int is_nil(struct rac_seq *s) { return s != &bad && rac_length(s) == 0; }

static int is_cons(struct rac_seq *s, dllist **h, struct rac_seq **t) {
  if (rac_length(s) == 0)
    return 0;
  *h = s->a[0];
  *t = s->len == 1 ? NULL : seq_new(s->len - 1, s->a + 1);
  return 1;
}

/* Twin of predicate mem(p, s) (a bounded \exists over the indices of s). */
static int rac_mem(dllist *p, struct rac_seq *s) {
  for (long k = 0; k < rac_length(s); k++)
    if (rac_nth(s, k) == p)
      return 1;
  return 0;
}

/* ---- inductive dll -------------------------------------------------- */

/* inductive dll{L}(dllist *prev, dllist *h, \list<dllist *> s) {
     case dll_nil{L}: \forall dllist *prev; dll{L}(prev, \null, \Nil);
     case dll_cons{L}:
       \forall dllist *prev, *h, \list<dllist *> s;
         h != \null ==> \valid(h) ==> h->ptr_to_previous == prev ==>
         !mem(h, s) ==> dll{L}(h, h->ptr_to_next, s) ==>
         dll{L}(prev, h, \Cons(h, s));
   } */
static int dll_fuel(dllist *prev, dllist *h, struct rac_seq *s, long fuel) {
  if (fuel-- <= 0)
    return 0;
  /* case dll_nil: conclusion dll(prev, \null, \Nil) */
  if (h == NULL && is_nil(s))
    return 1;
  /* case dll_cons: conclusion dll(prev, h', \Cons(h', t)) with h' == h */
  dllist *h1;
  struct rac_seq *t;
  if (is_cons(s, &h1, &t) && h1 == h) {
    if (h != NULL                                   /* h != \null */
        && rac_live_node(h)                         /* \valid(h) */
        && h->ptr_to_previous == prev               /* links back */
        && !rac_mem(h, t)                           /* !mem(h, s) */
        && dll_fuel(h, h->ptr_to_next, t, fuel))    /* dll(h, next, s) */
      return 1;
  }
  return 0;  /* no case applies */
}

int rac_dll(dllist *prev, dllist *h, struct rac_seq *s) {
  return dll_fuel(prev, h, s, RAC_FUEL);
}

/* ---- Witnesses ------------------------------------------------------ */

/* dll(p, h, s) determines s: the nodes reached from h by ptr_to_next.
   The walk is the dll_cons case read as a function of h. */
struct rac_seq *rac_reach(dllist *h) {
  long n = 0;
  for (dllist *q = h; q != NULL; q = q->ptr_to_next) {
    if (n == RAC_FUEL || !rac_live_node(q))
      return &bad;
    n++;
  }
  dllist **a = arena_alloc((size_t)n * sizeof *a);
  n = 0;
  for (dllist *q = h; q != NULL; q = q->ptr_to_next)
    a[n++] = q;
  return seq_new(n, a);
}

/* dll(p, h, s) with h != \null determines p: h->ptr_to_previous.
   With h == \null every p works (dll_nil); \null is returned. */
dllist *rac_prev(dllist *h) {
  return rac_live_node(h) ? h->ptr_to_previous : NULL;
}

/* dll(\null, h, s) and mem(x, s) determine h: walk back from x by
   ptr_to_previous to the node whose ptr_to_previous is \null
   (lemma dll_links).  NULL when there is no such walk. */
dllist *rac_head(dllist *x) {
  long n = 0;
  for (dllist *q = x; rac_live_node(q); q = q->ptr_to_previous) {
    if (q->ptr_to_previous == NULL)
      return q;
    if (++n == RAC_FUEL)
      break;
  }
  return NULL;
}

void rac_reset(void) {
  for (size_t i = 0; i < arena_n; i++)
    free(arena[i]);
  arena_n = 0;
  free(reg);
  reg = NULL;
  reg_cap = reg_n = 0;
}
