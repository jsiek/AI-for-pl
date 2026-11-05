/* E-ACSL's assertion function, replaced (e-acsl-gcc --external-assert)
   so that a failed check is recorded and the run goes on: the goal is the
   list of every contract check the self-test fails, not the first one.

   Each distinct check (kind, name, function, line) is counted; at exit
   the table goes to stderr, one line per check:
     FAILED <count> <kind> <name or -> in <function> at <file>:<line>: <predicate>
   then a last line "checks failed: <distinct> distinct, <total> total".

   The struct mirrors the head of E-ACSL 33's eacsl_assert_data_t
   (instrumentation_model/e_acsl_assert_data.h); only these fields are
   read. */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

typedef struct {
  int blocking;
  const char *kind;
  const char *name;
  const char *pred_txt;
  const char *file;
  const char *fct;
  int line;
  void *values;
} collect_data_t;

#define MAX_CHECKS 256

static struct {
  const char *kind, *name, *fct, *file, *pred;
  int line;
  long count;
} checks[MAX_CHECKS];
static int nchecks;
static long total;
static int registered;

static void report(void) {
  for (int k = 0; k < nchecks; k++)
    fprintf(stderr, "FAILED %ld %s %s in %s at %s:%d: %s\n", checks[k].count,
            checks[k].kind, checks[k].name ? checks[k].name : "-",
            checks[k].fct, checks[k].file, checks[k].line, checks[k].pred);
  fprintf(stderr, "checks failed: %d distinct, %ld total\n", nchecks, total);
}

static int same(const char *a, const char *b) {
  return a == b || (a && b && strcmp(a, b) == 0);
}

void __e_acsl_assert(int predicate, collect_data_t *data) {
  if (!registered) {
    registered = 1;
    atexit(report);
  }
  if (predicate)
    return;
  total++;
  for (int k = 0; k < nchecks; k++)
    if (checks[k].line == data->line && same(checks[k].kind, data->kind) &&
        same(checks[k].name, data->name) && same(checks[k].fct, data->fct) &&
        same(checks[k].pred, data->pred_txt)) {
      checks[k].count++;
      return;
    }
  if (nchecks == MAX_CHECKS) {
    fprintf(stderr, "eacsl_collect: more than %d distinct checks\n",
            MAX_CHECKS);
    abort();
  }
  checks[nchecks].kind = data->kind;
  checks[nchecks].name = data->name;
  checks[nchecks].fct = data->fct;
  checks[nchecks].file = data->file;
  checks[nchecks].pred = data->pred_txt;
  checks[nchecks].line = data->line;
  checks[nchecks].count = 1;
  nchecks++;
}
