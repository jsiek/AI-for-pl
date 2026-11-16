"""B1c's mutants (plan Q10, the list reused after iterating), for both
sides.  Anchors are C code (annotations allowed between the lines, as
in mutants.py), so they fit any annotated B1c source.

C-level (the same edit on both sides; ALLOC/FREE are the allocator
names of the side, ariadne_alloc_dllist / free or malloc / free):
  uaf       a payload read through the_list after the last iteration
            freed every node;
  nullchk   the NULL check after allocation (build loop) removed;
  noinit    `l->i = input[k];` removed (the first walk reads an
            uninitialised payload);
  addfreed  step 3's add given a freed node: the recorded middle node is
            freed just before `the_list = mid;`.
Spec-level (Frama-C):
  vacuity   `assert \\false` before the driver's return;
  nowashead add's contract without `was_head` (the build loop relies on
            the new node being the head);
  noassign  `elem->previous` dropped from add's `assigns`;
  nextpost  it_next's postcondition of 2026-11-08 replaced by the
            unanchored one of before (\\exists s; iter_ok(it, s, \\result)):
            a client can no longer show that the iterator stays on its
            list, so the driver's step-3 add is no longer provable.
"""
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from mutants import span, once  # noqa: E402

HDR = os.path.join(HERE, "..", "bench", "b1c", "spec",
                   "sglib_dl_list_spec.h")
RETURN = "  return sum;\n}"
NULLCHK = "    if (l == NULL)\n      break;\n"
NOINIT = "    l->i = input[k];\n"
SET_MID = "      the_list = mid;\n"
CONTRACT_CALLS = {
    "add": "/*@ SGLIB_DL_LIST_CONTRACT_ADD(dllist, ptr_to_previous, "
           "ptr_to_next) */",
    "it_next": "/*@ SGLIB_DL_LIST_CONTRACT_IT_NEXT(dllist, ptr_to_previous, "
               "ptr_to_next,"}
C_LEVEL = ["uaf", "nullchk", "noinit", "addfreed"]
SPEC_LEVEL = ["vacuity", "nowashead", "noassign", "nextpost"]
RUNTIME = ["vacuity", "uaf", "nullchk", "noinit", "addfreed"]
FUNCTION = {"uaf": "b1", "nullchk": "b1", "noinit": "b1", "addfreed": "b1",
            "vacuity": "b1", "nowashead": "b1",
            "noassign": "sglib_dllist_add", "nextpost": "b1"}


def free_name(src):
    return "ariadne_free_dllist" if "ariadne_free_dllist(" in src else "free"


def redefine(src, macro, call, old, new):
    hdr = open(HDR).read()
    i = hdr.index(f"#define {macro}(")
    d = hdr[i:hdr.index("\n\n", i)]
    assert d.count(old) == 1, old
    once(src, call)
    return src.replace(call, f"#undef {macro}\n" + d.replace(old, new)
                       + "\n" + call)


def mutant(name, src):
    if name == "uaf":
        once(src, RETURN)
        return src.replace(RETURN, "  if (the_list != NULL)\n"
                           "    sum += (unsigned)the_list->i;\n" + RETURN)
    if name == "nullchk":
        i, j = span(src, NULLCHK)
        return src[:i] + src[j:]
    if name == "noinit":
        i, j = span(src, NOINIT)
        return src[:i] + src[j:]
    if name == "addfreed":
        i, j = span(src, SET_MID)
        return src[:i] + f"      {free_name(src)}(mid);\n" + src[i:]
    if name == "vacuity":
        once(src, RETURN)
        return src.replace(RETURN, "  //@ assert vacuity: \\false;\n"
                           + RETURN)
    if name == "nowashead":
        hdr = open(HDR).read()
        i = hdr.index("#define SGLIB_DL_LIST_CONTRACT_ADD(")
        d = hdr[i:hdr.index("\n\n", i)]
        k = d.index("  ensures was_head:")
        return redefine(src, "SGLIB_DL_LIST_CONTRACT_ADD",
                        CONTRACT_CALLS["add"], d[k:], "  ensures \\true;")
    if name == "noassign":
        return redefine(src, "SGLIB_DL_LIST_CONTRACT_ADD",
                        CONTRACT_CALLS["add"], "elem->next, elem->previous,",
                        "elem->next,")
    if name == "nextpost":
        return redefine(
            src, "SGLIB_DL_LIST_CONTRACT_IT_NEXT", CONTRACT_CALLS["it_next"],
            "  ensures \\forall \\list<type *> s, integer b, f; \\\n"
            "    iter_at{Pre}(it, s, b, f) ==> iter_ok(it, s, \\result); \\\n",
            "  ensures \\exists \\list<type *> s; iter_ok(it, s, \\result); \\\n")
    raise KeyError(name)


def main(argv):
    """python3 mutants_b1c.py SRC OUTDIR [NAME ...] (default: RUNTIME)."""
    src_path, out = argv[1], argv[2]
    os.makedirs(out, exist_ok=True)
    src = open(src_path).read()
    for name in argv[3:] or RUNTIME:
        open(os.path.join(out, name + ".c"), "w").write(mutant(name, src))


if __name__ == "__main__":
    main(sys.argv)
