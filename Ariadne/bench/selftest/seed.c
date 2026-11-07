/* Fixed seed for sglib's samples/selftest.c, without editing it.

   selftest.c's main calls srandom(time(NULL)).  Linking with
   -Wl,--wrap=time sends that call (and only the calls from the objects
   linked with the flag) here: time() returns the seed, taken from the
   environment variable SELFTEST_SEED (default 1), so a run is
   reproducible and a seed can still be varied. */
#include <stdlib.h>
#include <time.h>

time_t __wrap_time(time_t *t) {
  const char *s = getenv("SELFTEST_SEED");
  time_t v = s ? (time_t)strtol(s, NULL, 10) : 1;
  if (t)
    *t = v;
  return v;
}
