/* E-ACSL's assertion function, replaced (e-acsl-gcc --external-assert):
   every evaluation of every check is counted, a failed check is recorded
   and the run goes on.  For step 0's coverage report (plan Q11): which
   clauses ran, how often, with which outcome.

   Checks whose name contains `rac_side_` are probes that gen_rac.py
   --cov adds to observe one side of an implication or disjunction: they
   are counted but never fail.

   At exit:
   - stderr gets one line per failed check,
       FAILED <count> <kind> <name or -> in <function> at <file>:<line>: <predicate>
     then "checks failed: <distinct> distinct, <total> total";
   - then, for every check named by gen_rac.py --cov (rac_cov_<n>,
     rac_side_<n>_<j>), a tab-separated line
       COV <kind> <name> <function> <line> <true count> <false count>
     (stderr, not a file: at exit E-ACSL's runtime has released the
     memory model, and file I/O there crashes).

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

#define MAX_CHECKS 16384

static struct {
  const char *kind, *name, *fct, *file, *pred;
  int line;
  long t, f;
} checks[MAX_CHECKS];
static int nchecks, nfailed;
static long total;
static int registered;

static void report(void) {
  for (int k = 0; k < nchecks; k++)
    if (checks[k].f && !(checks[k].name && strstr(checks[k].name,
                                                  "rac_side_")))
      fprintf(stderr, "FAILED %ld %s %s in %s at %s:%d: %s\n", checks[k].f,
              checks[k].kind, checks[k].name ? checks[k].name : "-",
              checks[k].fct, checks[k].file, checks[k].line, checks[k].pred);
  fprintf(stderr, "checks failed: %d distinct, %ld total\n", nfailed, total);
  /* coverage of the clauses gen_rac.py --cov named (file I/O is not
     usable here: at exit E-ACSL's runtime has released its memory) */
  for (int k = 0; k < nchecks; k++)
    if (checks[k].name && (strstr(checks[k].name, "rac_cov_") ||
                           strstr(checks[k].name, "rac_side_")))
      fprintf(stderr, "COV\t%s\t%s\t%s\t%d\t%ld\t%ld\n", checks[k].kind,
              checks[k].name, checks[k].fct, checks[k].line, checks[k].t,
              checks[k].f);
}

static int same(const char *a, const char *b) {
  return a == b || (a && b && strcmp(a, b) == 0);
}

void __e_acsl_assert(int predicate, collect_data_t *data) {
  if (!registered) {
    registered = 1;
    atexit(report);
  }
  int probe = data->name && strstr(data->name, "rac_side_");
  for (int k = 0; k < nchecks; k++)
    if (checks[k].line == data->line && same(checks[k].kind, data->kind) &&
        same(checks[k].name, data->name) && same(checks[k].fct, data->fct) &&
        same(checks[k].pred, data->pred_txt)) {
      if (predicate) {
        checks[k].t++;
      } else {
        if (!checks[k].f && !probe)
          nfailed++;
        checks[k].f++;
        total += !probe;
      }
      return;
    }
  if (nchecks == MAX_CHECKS) {
    fprintf(stderr, "rac_collect: more than %d distinct checks\n",
            MAX_CHECKS);
    abort();
  }
  checks[nchecks].kind = data->kind;
  checks[nchecks].name = data->name;
  checks[nchecks].fct = data->fct;
  checks[nchecks].file = data->file;
  checks[nchecks].pred = data->pred_txt;
  checks[nchecks].line = data->line;
  checks[nchecks].t = predicate != 0;
  checks[nchecks].f = predicate == 0;
  if (!predicate && !probe) {
    nfailed++;
    total++;
  }
  nchecks++;
}
