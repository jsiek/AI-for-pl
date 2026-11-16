"""Build vst/b1/b1.c from bench/b1/b1_gen.c (verbatim functions), and
the mutants bad_*.c (negative tests) next to it.

usage: python3 -I make_b1.py ../../bench/b1/b1_gen.c b1.c

Every copied piece is checked to occur verbatim in b1_gen.c."""
import os
import re
import sys

gen = open(sys.argv[1]).read()
out = sys.argv[2]

LINES = gen.split("\n")

def function(name):
    """The definition of `name` in gen: the first line at column 0 that
    starts a definition of it (not an `extern` prototype), through the
    next line that is `}` or `};`."""
    for i, line in enumerate(LINES):
        if (not line.startswith("extern") and not line.startswith(" ")
                and re.search(r"\b" + re.escape(name) + r"\(", line)
                and not line.rstrip().endswith(";")):
            start = i
            # a return type alone on the previous line (clang-format)
            if LINES[i - 1] and not LINES[i - 1].rstrip().endswith((";", "}")):
                start = i - 1
            # a definition: no `extern`, and its header (up to the first
            # `{`) has no `;` (skips continuation lines of prototypes)
            header = "\n".join(LINES[start:]).split("{", 1)[0]
            if LINES[start].startswith("extern") or ";" in header:
                continue
            for j in range(i, len(LINES)):
                if LINES[j] in ("}", "};"):
                    text = "\n".join(LINES[start:j + 1]) + "\n"
                    assert text.count("{") == text.count("}"), name
                    return text
    raise AssertionError(name)

types_end = gen.index("};\n", gen.index("struct sglib_dllist_iterator {")) + 3
types = gen[:types_end]

HEADER = """/* Benchmark B1a + B1b for VST: the same sglib code as
   ../../bench/b1/b1.c.  The type definitions and the six sglib
   functions B1a and B1b use are
   copied verbatim from ../../bench/b1/b1_gen.c (sglib's macros expanded
   by ../../bench/b1/gen.sh); the other generated functions are not
   called, so they are left out (VST's whole-program theorem needs every
   function in the file verified).  The driver is the same as in the
   Frama-C version, but with real malloc/free: VST models them itself,
   no ghost allocators are needed.  main runs it on a fixed input. */

#include <stddef.h>
#include <stdlib.h>

"""

DRIVER = """
/* Driver for B1a + B1b: build a list from input[0..n-1] with
   sglib_dllist_add, walk it forward from sglib_dllist_get_first and
   backward (ptr_to_previous) from sglib_dllist_get_last, then free every
   element while iterating (the sample's last loop).  Returns the last
   value seen by the walks. */
int b1(const int *input, int n) {
  dllist *l, *the_list = NULL;
  struct sglib_dllist_iterator it;
  int last = 0;
  for (int k = 0; k < n; k++) {
    l = malloc(sizeof(dllist));
    if (l == NULL)
      break;
    l->i = input[k];
    sglib_dllist_add(&the_list, l);
  }
  for (l = sglib_dllist_get_first(the_list); l != NULL; l = l->ptr_to_next)
    last = l->i;
  for (l = sglib_dllist_get_last(the_list); l != NULL;
       l = l->ptr_to_previous)
    last = l->i;
  for (l = sglib_dllist_it_init(&it, the_list); l != NULL;
       l = sglib_dllist_it_next(&it))
    free(l);
  return last;
}

int input[4] = {6, 7, 3, 4};

int main(void) { return b1(input, 4); }
"""

# Order matters for C: it_next is called by it_init_on_equal.
parts = [
    "dllist *sglib_dllist_it_next(struct sglib_dllist_iterator *it);\n",
    function("sglib_dllist_add"),
    function("sglib_dllist_get_first"),
    function("sglib_dllist_get_last"),
    function("sglib_dllist_it_init_on_equal"),
    function("sglib_dllist_it_init"),
    function("sglib_dllist_it_next"),
]
for p in [types] + parts[1:]:
    assert p in gen, "not verbatim from b1_gen.c"
with open(out, "w") as f:
    f.write(HEADER)
    f.write(types)
    for p in parts:
        f.write(p if p.endswith("\n") else p + "\n")
    f.write(DRIVER)


# Mutants for verif_bad.v.  A driver mutant holds the types, the
# prototypes of the sglib functions (their specs are assumed from
# verif_b1.v) and a mutated driver, still called b1 so that it is checked
# against the same b1_spec.  A function mutant holds the types and the
# mutated sglib function, checked against that function's spec.
WALK = """  for (l = sglib_dllist_get_first(the_list); l != NULL; l = l->ptr_to_next)
    last = l->i;
"""
BACK = """  for (l = sglib_dllist_get_last(the_list); l != NULL;
       l = l->ptr_to_previous)
    last = l->i;
"""
FREE = """  for (l = sglib_dllist_it_init(&it, the_list); l != NULL;
       l = sglib_dllist_it_next(&it))
    free(l);
"""
NULLCHK = """    if (l == NULL)
      break;
"""
RESULT = "    (result) = _dll_;\n"
DRIVER_ONLY = DRIVER[:DRIVER.index("int input[4]")]
assert DRIVER_ONLY.count(WALK + BACK + FREE) == 1
assert DRIVER_ONLY.count(NULLCHK) == 1
DRIVER_MUTANTS = {
    # use after free: the forward walk moved after the free loop
    "bad_uaf.c": DRIVER_ONLY.replace(WALK + BACK + FREE, BACK + FREE + WALK),
    # use after free: the backward walk moved after the free loop
    "bad_uaf_back.c": DRIVER_ONLY.replace(WALK + BACK + FREE,
                                          WALK + FREE + BACK),
    # no NULL check after malloc
    "bad_nonull.c": DRIVER_ONLY.replace(NULLCHK, ""),
}


def null_result(fun):
    """fun, copied verbatim, but with `(result) = NULL;` after its
    traversal (as the Frama-C mutants nullfirst / nulllast)."""
    text = function(fun)
    assert text in gen and text.count(RESULT) == 1, fun
    return text.replace(RESULT, "    (result) = NULL;\n")


FUNCTION_MUTANTS = {
    "bad_nullfirst.c": null_result("sglib_dllist_get_first"),
    "bad_nulllast.c": null_result("sglib_dllist_get_last"),
}
PROTOS = """void sglib_dllist_add(dllist **list, dllist *elem);
dllist *sglib_dllist_get_first(dllist *list);
dllist *sglib_dllist_get_last(dllist *list);
dllist *sglib_dllist_it_init(struct sglib_dllist_iterator *it, dllist *list);
dllist *sglib_dllist_it_next(struct sglib_dllist_iterator *it);
"""


def write_mutant(name, body):
    with open(os.path.join(os.path.dirname(out) or ".", name), "w") as f:
        f.write("/* Mutant of b1.c for verif_bad.v (generated by make_b1.py). */\n")
        f.write("#include <stddef.h>\n#include <stdlib.h>\n\n")
        f.write(types)
        f.write(body)


for name, driver in DRIVER_MUTANTS.items():
    write_mutant(name, PROTOS + driver)
for name, fun in FUNCTION_MUTANTS.items():
    write_mutant(name, fun)
