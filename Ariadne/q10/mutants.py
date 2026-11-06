"""B1's nine mutants (../bench/b1/check.sh), as they apply to B1a, for
both sides of the plan Q10 comparison.

C-level mutants (the same edit of the driver on both sides; anchors are
C code only, so they fit any annotated source):
  uaf       the forward walk (with the loop annotation right before it,
            if any) moved after the free loop;
  nullchk   the NULL check after allocation removed;
  noinit    `l->i = input[k];` removed (the walk reads an uninitialised
            payload).
Spec-level mutants (Frama-C; the VST analogues are in README.md):
  vacuity   `assert \\false` before the driver's return;
  nowashead add's contract without `was_head`;
  noassign  `elem->previous` dropped from add's `assigns`.
Not applicable to B1a: uaf_back, nullfirst, nulllast (they change B1b
code: get_first, get_last and the backward walk).
"""
import os

HERE = os.path.dirname(os.path.abspath(__file__))
HDR = os.path.join(HERE, "..", "bench", "b1a", "spec",
                   "sglib_dl_list_spec.h")
WALK = ("  for (l = the_list; l != NULL; l = l->ptr_to_next)\n"
        "    last = l->i;\n")
FREE_HEAD = "  for (l = sglib_dllist_it_init(&it, the_list); l != NULL;\n"
NULLCHK = "    if (l == NULL)\n      break;\n"
NOINIT = "    l->i = input[k];\n"
RETURN = "  return last;\n}"
ADD_CALL = ("/*@ SGLIB_DL_LIST_CONTRACT_ADD(dllist, ptr_to_previous, "
            "ptr_to_next) */")
C_LEVEL = ["uaf", "nullchk", "noinit"]
SPEC_LEVEL = ["vacuity", "nowashead", "noassign"]
NOT_APPLICABLE = ["uaf_back", "nullfirst", "nulllast"]


def once(src, s):
    assert src.count(s) == 1, s
    return src.index(s)


def block_end(src, i):
    """The end of the statement starting at i: through the matching `}`
    if its first line opens a block, else through its next `;` line."""
    j = src.index("{", i)
    depth = 0
    for k in range(j, len(src)):
        depth += {"{": 1, "}": -1}.get(src[k], 0)
        if depth == 0:
            return src.index("\n", k) + 1
    raise AssertionError("unbalanced")


def uaf(src):
    i = once(src, WALK)
    start = i
    before = src[:i].rstrip()
    if before.endswith("*/"):  # the walk's loop annotation moves with it
        a = before.rindex("/*@")
        start = src.rindex("\n", 0, a) + 1
    walk = src[start:i + len(WALK)]
    rest = src[:start] + src[i + len(WALK):]
    f = once(rest, FREE_HEAD)
    h = rest.index("sglib_dllist_it_next(&it))", f)
    eol = rest.index("\n", h)
    if rest[h:eol].rstrip().endswith("{"):  # Frama-C: a block body
        e = block_end(rest, h)
    else:  # VST: `for (...) free(l);`
        e = rest.index(";\n", eol) + 2
    return rest[:e] + walk + rest[e:]


def add_contract(src, old, new):
    hdr = open(HDR).read()
    i = hdr.index("#define SGLIB_DL_LIST_CONTRACT_ADD(")
    d = hdr[i:hdr.index("\n\n", i)]
    assert d.count(old) == 1, old
    once(src, ADD_CALL)
    return src.replace(ADD_CALL, "#undef SGLIB_DL_LIST_CONTRACT_ADD\n"
                       + d.replace(old, new) + "\n" + ADD_CALL)


def mutant(name, src):
    if name == "uaf":
        return uaf(src)
    if name == "nullchk":
        once(src, NULLCHK)
        return src.replace(NULLCHK, "")
    if name == "noinit":
        once(src, NOINIT)
        return src.replace(NOINIT, "")
    if name == "vacuity":
        once(src, RETURN)
        return src.replace(RETURN, "  //@ assert vacuity: \\false;\n"
                           + RETURN)
    if name == "nowashead":
        hdr = open(HDR).read()
        i = hdr.index("#define SGLIB_DL_LIST_CONTRACT_ADD(")
        d = hdr[i:hdr.index("\n\n", i)]
        k = d.index("  ensures was_head:")
        return add_contract(src, d[k:], "  ensures \\true;")
    if name == "noassign":
        return add_contract(src, "elem->next, elem->previous,",
                            "elem->next,")
    raise KeyError(name)


# The function whose goals each mutant should break.
FUNCTION = {"uaf": "b1", "nullchk": "b1", "noinit": "b1", "vacuity": "b1",
            "nowashead": "b1", "noassign": "sglib_dllist_add"}

# Mutants step 0 can catch: each makes some run go wrong.  nowashead and
# noassign only weaken add's contract; the code still runs correctly, so
# runtime checking cannot see them (WP rejects them, check_wp.py).
RUNTIME = ["vacuity", "uaf", "nullchk", "noinit"]


def main(argv):
    """python3 mutants.py SRC OUTDIR [NAME ...]: write OUTDIR/NAME.c for
    each mutant (default: RUNTIME), from SRC (any annotated B1a source,
    expanded or not: the anchors are C code)."""
    src_path, out = argv[1], argv[2]
    os.makedirs(out, exist_ok=True)
    src = open(src_path).read()
    for name in argv[3:] or RUNTIME:
        open(os.path.join(out, name + ".c"), "w").write(mutant(name, src))


if __name__ == "__main__":
    import sys
    main(sys.argv)
