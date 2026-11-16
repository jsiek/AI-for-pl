/* Runtime support for generated executable twins; see rac_rt.h.
   Not instrumented by E-ACSL (compiled apart and linked): it reads only
   its own data and blocks the registry says are live. */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#define RAC_TWIN_IMPL
#include "rac_rt.h"

#ifndef RAC_FUEL
#define RAC_FUEL 1000000L
#endif
#ifndef RAC_DEPTH
#define RAC_DEPTH 20000
#endif

static void oom(void) {
  static const char msg[] = "rac_rt: out of memory\n";
  (void)!fwrite(msg, 1, sizeof msg - 1, stderr);
  abort();
}

/* ---- Allocation registry (heap, dead) -------------------------------- */

/* Open addressing on block addresses; state 1 = live, 2 = dead. */
static struct reg { void *b; unsigned long size; int state; } *reg;
static size_t reg_cap, reg_n;
static unsigned long reg_max_size;  /* largest block registered */

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

void rac_reg_alloc(void *b, unsigned long size) {
  if (2 * (reg_n + 1) > reg_cap)
    reg_grow();
  struct reg *r = reg_find(b);
  if (r->b == NULL)
    reg_n++;
  r->b = b;
  r->size = size;
  if (size > reg_max_size)
    reg_max_size = size;
  r->state = 1;  /* a freed block may be handed out again: live again */
}

long rac_reg_count(long unused) { (void)unused; return (long)reg_cap; }
long rac_reg_nth(long i) {
  return i >= 0 && (size_t)i < reg_cap ? (long)(size_t)reg[i].b : 0;
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

/* The registered block containing p, if any: its base is at most
   reg_max_size bytes below p, and malloc'd blocks are 8-byte aligned. */
static struct reg *reg_containing(const void *p) {
  unsigned long long a = (unsigned long long)(size_t)p;
  for (unsigned long long c = a & ~7ULL; c + reg_max_size > a && c; c -= 8) {
    struct reg *r = reg_find((void *)(size_t)c);
    if (r && r->b == (void *)(size_t)c && a < c + r->size)
      return r;
    if (c < 8)
      break;
  }
  return NULL;
}

int rac_heap_of(void *p) { return reg_containing(p) != NULL; }

int rac_dead_of(void *p) {
  struct reg *r = reg_containing(p);
  return r && r->state == 2;
}

int rac_keep_freed;

int rac_valid(const void *p, unsigned long size) {
  if (p == NULL)
    return 0;
  struct reg *r = reg_containing(p);
  return r && (r->state == 1 || (r->state == 2 && rac_keep_freed)) &&
         (unsigned long long)(size_t)p + size
           <= (unsigned long long)(size_t)r->b + r->size;
}

/* ---- Step bound ------------------------------------------------------ */

long rac_steps;

int rac_tick(int depth) {
  return depth <= RAC_DEPTH && ++rac_steps <= RAC_FUEL;
}

/* ---- \list values ---------------------------------------------------- */

/* A list is a cons cell (hd, tl) or an array slice (a), with its length;
   a cons cell also gets a slice on the first \nth of it or of a list it
   is a suffix of.  \Nil is NULL.

   Cons cells are hash-consed: rac_seq_cons(h, t) returns the existing
   cell for (h, t), so recomputing a witness on an unchanged heap (E-ACSL
   evaluates a witness term once per use, and once per index inside a
   quantifier) allocates nothing new. */
struct rac_seq {
  long len;
  void **a;
  void *hd;
  struct rac_seq *tl;
  int cons;
};

struct rac_seq rac_bad_seq = {0, NULL, NULL, NULL, 0};

/* Every list value lives in an arena (chunks) freed by rac_reset. */
#define CHUNK (1 << 16)
static struct chunk { struct chunk *next; size_t used, cap; } *chunks;

static void *arena_alloc(size_t size) {
  size = (size + 15) & ~(size_t)15;
  if (!chunks || chunks->used + size > chunks->cap) {
    size_t cap = size > CHUNK ? size : CHUNK;
    struct chunk *c = malloc(sizeof *c + 16 + cap);
    if (!c)
      oom();
    c->next = chunks;
    c->used = 0;
    c->cap = cap;
    chunks = c;
  }
  void *p = (char *)(chunks + 1) + 16 + chunks->used;
  chunks->used += size;
  return p;
}

static struct rac_seq *seq_new(long len, void **a, void *hd,
                               struct rac_seq *tl, int cons) {
  struct rac_seq *s = arena_alloc(sizeof *s);
  s->len = len;
  s->a = a;
  s->hd = hd;
  s->tl = tl;
  s->cons = cons;
  return s;
}

/* The hash-cons table: open addressing on (hd, tl). */
static struct rac_seq **hc;
static size_t hc_cap, hc_n;

static size_t hc_hash(void *h, struct rac_seq *t) {
  unsigned long long x = (unsigned long long)(size_t)h * 0x9E3779B97F4A7C15ULL
                         ^ (unsigned long long)(size_t)t * 0xC2B2AE3D27D4EB4FULL;
  return (size_t)(x ^ (x >> 29));
}

static struct rac_seq **hc_slot(void *h, struct rac_seq *t) {
  for (size_t i = hc_hash(h, t) & (hc_cap - 1);; i = (i + 1) & (hc_cap - 1))
    if (!hc[i] || (hc[i]->hd == h && hc[i]->tl == t))
      return &hc[i];
}

static void hc_grow(void) {
  struct rac_seq **old = hc;
  size_t old_cap = hc_cap;
  hc_cap = hc_cap ? 2 * hc_cap : 1024;
  hc = calloc(hc_cap, sizeof *hc);
  if (!hc)
    oom();
  for (size_t i = 0; i < old_cap; i++)
    if (old[i])
      *hc_slot(old[i]->hd, old[i]->tl) = old[i];
  free(old);
}

long rac_seq_len(struct rac_seq *s) { return s ? s->len : 0; }
int rac_seq_is_nil(struct rac_seq *s) { return s == NULL; }
int rac_seq_is_cons(struct rac_seq *s) { return s && s->len > 0; }

static void **seq_array(struct rac_seq *s) {
  if (!s->a) {
    void **a = arena_alloc((size_t)s->len * sizeof *a);
    long n = 0;
    struct rac_seq *q = s;
    while (q && !q->a && n < s->len) {
      a[n++] = q->hd;
      q = q->tl;
    }
    if (n < s->len)
      memcpy(a + n, q->a, (size_t)(s->len - n) * sizeof *a);
    /* every cons cell of the chain is a suffix: give it its slice */
    n = 0;
    for (q = s; q && !q->a; q = q->tl)
      q->a = a + n++;
  }
  return s->a;
}

void *rac_seq_nth(struct rac_seq *s, long k) {
  return s && 0 <= k && k < s->len ? seq_array(s)[k] : NULL;
}

void *rac_seq_hd(struct rac_seq *s) { return s->cons ? s->hd : s->a[0]; }

struct rac_seq *rac_seq_tl(struct rac_seq *s) {
  if (s->cons)
    return s->tl;
  if (s->len == 1)
    return NULL;
  return seq_new(s->len - 1, s->a + 1, NULL, NULL, 0);
}

struct rac_seq *rac_seq_cons(void *h, struct rac_seq *t) {
  if (t == RAC_BAD)
    return RAC_BAD;
  if (2 * (hc_n + 1) > hc_cap)
    hc_grow();
  struct rac_seq **slot = hc_slot(h, t);
  if (!*slot) {
    *slot = seq_new(rac_seq_len(t) + 1, NULL, h, t, 1);
    hc_n++;
  }
  return *slot;
}

struct rac_seq *rac_seq_concat(struct rac_seq *a, struct rac_seq *b) {
  if (a == RAC_BAD || b == RAC_BAD)
    return RAC_BAD;
  long n = rac_seq_len(a), m = rac_seq_len(b);
  if (n == 0)
    return b;
  if (m == 0)
    return a;
  void **c = arena_alloc((size_t)(n + m) * sizeof *c);
  memcpy(c, seq_array(a), (size_t)n * sizeof *c);
  memcpy(c + n, seq_array(b), (size_t)m * sizeof *c);
  return seq_new(n + m, c, NULL, NULL, 0);
}

int rac_seq_eq(struct rac_seq *a, struct rac_seq *b) {
  if (a == RAC_BAD || b == RAC_BAD)
    return 0;
  if (a == b)
    return 1;
  long n = rac_seq_len(a);
  if (n != rac_seq_len(b))
    return 0;
  for (long k = 0; k < n; k++)
    if (rac_seq_nth(a, k) != rac_seq_nth(b, k))
      return 0;
  return 1;
}

static void seq_reset(void) {
  while (chunks) {
    struct chunk *c = chunks->next;
    free(chunks);
    chunks = c;
  }
  free(hc);
  hc = NULL;
  hc_cap = hc_n = 0;
}

/* ---- Builtins on handles --------------------------------------------- */

#define SEQ(s) ((struct rac_seq *)(size_t)(s))
#define L(x) ((long)(size_t)(x))

long rac_length(long s) { return rac_seq_len(SEQ(s)); }
long rac_index(long s, void *x) {
  struct rac_seq *q = SEQ(s);
  for (long k = 0; k < rac_seq_len(q); k++)
    if (rac_seq_nth(q, k) == x)
      return k;
  return -1;
}
long rac_nth(long s, long k) { return L(rac_seq_nth(SEQ(s), k)); }
struct rac_seq *rac_seq_tail(struct rac_seq *s) {
  if (s == RAC_BAD)
    return RAC_BAD;
  return rac_seq_is_cons(s) ? rac_seq_tl(s) : NULL;
}

long rac_tail(long s) { return L(rac_seq_tail(SEQ(s))); }
long rac_concat(long s, long t) { return L(rac_seq_concat(SEQ(s), SEQ(t))); }

void rac_reset(void) {
  seq_reset();
  free(reg);
  reg = NULL;
  reg_cap = reg_n = 0;
  reg_max_size = 0;
}
