"""Build the B1a inputs of the plan Q10 comparison (Frama-C/WP vs VST)
from B1 as it stands, so that both sides get the same C code.

    python3 -I make_b1a.py          (from this directory; writes in place)

Writes
  b1a_frozen.c   the Frama-C input: B1a's code with only the public spec
                 (the frozen contracts and predicates of b1_frozen.c);
  b1a.c          the VST input: the same code with real malloc/free and
                 a `main`, no annotations;
  spec/sglib_dl_list_spec.h
                 the public part of ../sglib_spec/sglib_dl_list_spec.h
                 (the private lemma and annotation macros left out, so
                 the annotator cannot invoke the human's proof).

B1a is the first stage of B1 (../b1/README.md): sglib_dllist_add,
sglib_dllist_it_init_on_equal, sglib_dllist_it_init, sglib_dllist_it_next
and a driver that builds a list, walks it forward from its head, and
frees every element while iterating.  The code is after bug fix #1 and
verification refactor #1 (../b1/CHANGES.md).  Every sglib function and
the types are copied verbatim from ../b1/b1_gen.c, and every contract
and the spec block verbatim from ../b1/b1_frozen.c (asserted below)."""
import os
import re

HERE = os.path.dirname(os.path.abspath(__file__))
B1 = os.path.join(HERE, "..", "b1")
GEN = open(os.path.join(B1, "b1_gen.c")).read()
FROZEN = open(os.path.join(B1, "b1_frozen.c")).read()
TEMPLATE = open(os.path.join(HERE, "..", "sglib_spec",
                             "sglib_dl_list_spec.h")).read()
FUNCTIONS = ["sglib_dllist_add", "sglib_dllist_it_init_on_equal",
             "sglib_dllist_it_init", "sglib_dllist_it_next"]
LINES = GEN.split("\n")


def function(name):
    """The definition of `name` in b1_gen.c (not a prototype), through
    the next line that is `}` or `};` (as ../../vst/b1/make_b1.py)."""
    for i, line in enumerate(LINES):
        if (not line.startswith("extern") and not line.startswith(" ")
                and re.search(r"\b" + re.escape(name) + r"\(", line)
                and not line.rstrip().endswith(";")):
            start = i
            if LINES[i - 1] and not LINES[i - 1].rstrip().endswith(
                    (";", "}")):
                start = i - 1
            header = "\n".join(LINES[start:]).split("{", 1)[0]
            if LINES[start].startswith("extern") or ";" in header:
                continue
            for j in range(i, len(LINES)):
                if LINES[j] in ("}", "};"):
                    text = "\n".join(LINES[start:j + 1]) + "\n"
                    assert text.count("{") == text.count("}"), name
                    return text
    raise AssertionError(name)


def contract(text):
    """The annotation comment right before `text` in b1_frozen.c."""
    i = FROZEN.index(text.split("\n", 1)[0])
    j = FROZEN.rindex("/*@", 0, i)
    c = FROZEN[j:i]
    assert c.rstrip().endswith("*/") and c.count("/*@") == 1, c
    return c


TYPES_START = GEN.index("typedef struct dllist {")
TYPES = GEN[TYPES_START:GEN.index(
    "};\n", GEN.index("struct sglib_dllist_iterator {")) + 3]
SPEC = FROZEN[FROZEN.index("/*@ // The fields DLLIST_COMPARATOR reads"):
              FROZEN.index("/* BEGIN GENERATED (b1_gen.c), part 2")]
PROTO = "dllist *sglib_dllist_it_next(struct sglib_dllist_iterator *it);\n"
BODIES = [function(f) for f in FUNCTIONS]
for p in [TYPES, SPEC] + BODIES:
    assert p in GEN or p in FROZEN, "not verbatim"
B1_CONTRACT = FROZEN[FROZEN.index("/*@ requires 0 <= n"):
                     FROZEN.index("int b1(const int *input, int n) {")]

# The B1a driver: B1's driver with B1b's two walks replaced by the
# forward walk from the head that B1a had (git a4039605), and `l`
# initialised as in B1 (README "Initialisation").
DRIVER_WP = """int b1(const int *input, int n) {
  dllist *l = NULL, *the_list = NULL;
  struct sglib_dllist_iterator it;
  int last = 0;
  for (int k = 0; k < n; k++) {
  before_alloc:
    l = ariadne_alloc_dllist();
    if (l == NULL)
      break;
    l->i = input[k];
    sglib_dllist_add(&the_list, l);
  }
  for (l = the_list; l != NULL; l = l->ptr_to_next)
    last = l->i;
  for (l = sglib_dllist_it_init(&it, the_list); l != NULL;
       l = sglib_dllist_it_next(&it)) {
  before_free:
    ariadne_free_dllist(l);
  }
  return last;
}
"""
# B1's driver minus B1b's walks must be this driver plus the walk.
B1_DRIVER = FROZEN[FROZEN.index("int b1(const int *input, int n) {"):]
B1B_WALKS = """  for (l = sglib_dllist_get_first(the_list); l != NULL; l = l->ptr_to_next)
    last = l->i;
  for (l = sglib_dllist_get_last(the_list); l != NULL;
       l = l->ptr_to_previous)
    last = l->i;
"""
B1A_WALK = """  for (l = the_list; l != NULL; l = l->ptr_to_next)
    last = l->i;
"""
assert B1_DRIVER.replace(B1B_WALKS, B1A_WALK) == DRIVER_WP
# VST: real malloc/free (VST models them), no labels (the ghost
# liveness model's \\at points; no-ops in C).
DRIVER_VST = (DRIVER_WP.replace("  before_alloc:\n", "")
              .replace("  before_free:\n", "")
              .replace("ariadne_alloc_dllist()", "malloc(sizeof(dllist))")
              .replace("ariadne_free_dllist(l)", "free(l)"))
assert DRIVER_VST.count("malloc(") == 1 and DRIVER_VST.count("free(l)") == 1

COMMENT = """/* Driver: build a list from input[0..n-1] with sglib_dllist_add, walk
   it forward from its head, then free every element while iterating
   (sglib's samples/dllist.c).  Returns the last value seen by the
   walk. */
"""

WP = f"""/* Benchmark B1a, frozen-only (plan Q10): the public spec only.
   Generated by make_b1a.py from ../b1/b1_gen.c (code) and
   ../b1/b1_frozen.c (spec); do not edit.  Kept: the shape predicates,
   the frozen contracts of the four sglib functions and the driver, and
   the ghost liveness model's allocator contracts.  The private
   annotations (loop invariants, asserts, lemmas) are for the annotator
   to write.  */

#include <assert.h>
#include <stddef.h>
#include "ariadne_alloc.h"
#include "sglib_dl_list_spec.h"

/* BEGIN GENERATED (b1_gen.c), part 1: types */
{TYPES}/* END GENERATED, part 1 */

{SPEC}{PROTO}
""" + "".join(contract(b) + b for b in BODIES) + "\n" + COMMENT \
    + B1_CONTRACT + DRIVER_WP

VST = f"""/* Benchmark B1a for VST (plan Q10).  Generated by make_b1a.py: the
   types and the four sglib functions verbatim from ../b1/b1_gen.c
   (sglib's macros expanded), the driver as in b1a_frozen.c but with
   real malloc/free, and a main that runs it on a fixed input. */

#include <stddef.h>
#include <stdlib.h>

{TYPES}
{PROTO}""" + "".join(BODIES) + "\n" + COMMENT + DRIVER_VST + """
int input[4] = {6, 7, 3, 4};

int main(void) { return b1(input, 4); }
"""

# The public header: the template without its private macros (and the
# comment block attached to each), and without the private section
# headers.
PRIVATE = re.compile(r"#define SGLIB_DL_LIST_(LEMMAS|ANNOT_\w+|_ADD_PRE"
                     r"|_ADD_HYPS|_INSERTED)\(")
out, chunk, i = [], [], 0
src = TEMPLATE.split("\n")
while i < len(src):
    line = src[i]
    if line.startswith("#define"):
        macro = [line]
        while macro[-1].endswith("\\"):
            i += 1
            macro.append(src[i])
        if PRIVATE.match(line):
            chunk = []  # its attached comment goes too
        else:
            out += chunk + macro
            chunk = []
    elif line == "":
        if not any(re.match(r"/\* (---- private|Private)", c)
                   for c in chunk):
            out += chunk
        out.append("")
        chunk = []
    else:
        chunk.append(line)
    i += 1
out += chunk
public = re.sub(r"\n{3,}", "\n\n", "\n".join(out))
public = public.replace(
    "#ifndef SGLIB_DL_LIST_SPEC_H",
    "/* The public part only (plan Q11), generated by\n"
    "   ../make_b1a.py from ../../sglib_spec/sglib_dl_list_spec.h. */\n\n"
    "#ifndef SGLIB_DL_LIST_SPEC_H", 1)
assert not re.search(r"SGLIB_DL_LIST_(LEMMAS|ANNOT_|_ADD_|_INSERTED)\w*\(",
                     public.split("#ifndef", 1)[1])
for m in re.findall(r"#define (SGLIB_DL_LIST_(?:SPEC|CONTRACT_\w+))\(",
                    TEMPLATE):
    assert f"#define {m}(" in public, m

os.makedirs(os.path.join(HERE, "spec"), exist_ok=True)
for name, text in [("b1a_frozen.c", WP), ("b1a.c", VST),
                   ("spec/sglib_dl_list_spec.h", public)]:
    open(os.path.join(HERE, name), "w").write(text)
