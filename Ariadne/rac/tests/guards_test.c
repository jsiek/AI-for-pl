/* Unit test of the twins generated from guards.c, under ASan + UBSan:
   NULL and freed nodes give the ACSL value (or false) without a bad
   read. */
#include <stdio.h>
#include <stdlib.h>
#include "guards.h"
#include "guards_twins.h"

static int failures;
#define CHECK(c) \
  do { if (!(c)) { failures++; printf("FAIL line %d: %s\n", __LINE__, #c); } } while (0)

int main(void) {
  node *p = calloc(1, sizeof *p);
  if (!p)
    return 2;
  rac_reg_alloc(p, sizeof *p);
  CHECK(rac_is_zero(p));
  CHECK(!rac_is_zero(NULL));        /* p[0].key unreadable: false */
  CHECK(rac_is_ok(p));
  CHECK(rac_is_ok(NULL));           /* p->key read in no arm taken */
  p->key = 3;
  CHECK(!rac_is_zero(p));
  CHECK(!rac_is_ok(p));
  node *volatile dead = p;          /* a dangling copy, kept from gcc */
  rac_reg_free(p);
  free(p);
  CHECK(!rac_is_zero(dead));        /* freed: false, and no read */
  CHECK(!rac_is_ok(dead));
  arr4 *q = calloc(1, sizeof *q);
  if (!q)
    return 2;
  rac_reg_alloc(q, sizeof *q);
  CHECK(rac_is_cell(q, 0) && rac_is_cell(q, 3));
  CHECK(!rac_is_cell(q, 4));        /* past the array: false, no read */
  CHECK(!rac_is_cell(q, -1));
  CHECK(!rac_is_cell(NULL, 0));
  rac_reg_free(q);
  free(q);
  rac_reset();
  printf("guards twin unit tests: %s\n", failures ? "FAIL" : "ok");
  return failures != 0;
}
