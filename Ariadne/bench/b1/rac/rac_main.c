/* Test driver for B1's b1(input, n): random inputs, property-style.

     ./b1_xxx [runs [seed [large]]]     defaults: 300 1 200

   Run r uses n = r for r < 6 (so n = 0, 1, 2, ... always occur), n =
   `large` every 25th run, otherwise n random in 0..40; values random in
   -1000..1000.  Every 4th run with n > 0 also injects an allocation
   failure: allocation rac_fail_at (random in 0..n-1) returns NULL, which
   exercises b1's NULL check (mutant nullchk removes it).

   Oracle: b1 prepends each node, walks forward from the head (ending at
   input[0]) and then backward from the last node (ending at the head), so
   it returns the last value it stored, input[m - 1] for the m nodes it
   built (m = n, or rac_fail_at under injection), or 0 when m = 0.  The
   oracle is ours, not part of b1.c's spec; check.sh reports its failures
   separately from sanitizer and E-ACSL failures.  With RAC_ORACLE_B1A
   (../../b1a/rac/check.sh) the oracle is B1a's: only the forward walk,
   so input[0], or 0 when m = 0.

   In the E-ACSL build this file is #included at the end of b1_rac.c (so
   main's mallocs are tracked too); in the sanitizer builds it is compiled
   on its own. */
#include <stdio.h>
#include <stdlib.h>
#include "rac_twins.h"

int b1(const int *input, int n);
extern long rac_alloc_count, rac_fail_at;

static unsigned long long rng_state;

static unsigned rng(unsigned bound) {   /* xorshift64*, then mod bound */
  rng_state ^= rng_state >> 12;
  rng_state ^= rng_state << 25;
  rng_state ^= rng_state >> 27;
  return (unsigned)((rng_state * 2685821657736338717ULL) >> 33) % bound;
}

int main(int argc, char **argv) {
  long runs = argc > 1 ? atol(argv[1]) : 300;
  /* atol, not strtoull: E-ACSL has no memory model for strtoull */
  rng_state = argc > 2 ? (unsigned long long)atol(argv[2]) : 1;
  int large = argc > 3 ? atoi(argv[3]) : 200;
  long injected = 0, nodes = 0;
  if (rng_state == 0)
    rng_state = 1;
  for (long r = 0; r < runs; r++) {
    int n = r < 6 ? (int)r : r % 25 == 0 ? large : (int)rng(41);
    /* one extra cell, so input is a valid block even when n == 0 */
    int *input = malloc((size_t)(n + 1) * sizeof *input);
    if (!input) {
      fprintf(stderr, "driver: malloc failed\n");
      return 3;
    }
    for (int k = 0; k < n; k++)
      input[k] = (int)rng(2001) - 1000;
    rac_alloc_count = 0;
    rac_fail_at = -1;
    if (r % 4 == 3 && n > 0) {
      rac_fail_at = rng((unsigned)n);
      injected++;
    }
    int m = rac_fail_at >= 0 ? (int)rac_fail_at : n;
#ifdef RAC_ORACLE_B1A
    /* B1a's driver: only the forward walk, ending at input[0] */
    int expected = m > 0 ? input[0] : 0;
#else
    int expected = m > 0 ? input[m - 1] : 0;
#endif
    int got = b1(input, n);
    if (got != expected) {
      fprintf(stderr,
              "ORACLE FAIL: run %ld, n = %d, fail_at = %ld: b1 returned %d,"
              " expected %d\n", r, n, rac_fail_at, got, expected);
      return 2;
    }
    nodes += m;
    free(input);
    rac_reset();
  }
  printf("ok: %ld runs, %ld nodes, %ld with an injected allocation failure,"
         " largest n = %d\n", runs, nodes, injected, large);
  return 0;
}
