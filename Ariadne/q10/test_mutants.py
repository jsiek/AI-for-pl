"""Offline tests of mutants.py's anchors: every mutant applies to the
VST C, the frozen-only source and the step-0 reference, and the C-level
ones also to a source with annotations between the lines of the mutated
statements (as an annotator may write them: wp-run3's second patch put
an assert inside the forward walk's body, and step 0 then failed on the
anchor instead of checking the patch).

    python3 test_mutants.py
"""
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import mutants  # noqa: E402

B1A = os.path.join(HERE, "..", "bench", "b1a")
fails = []


def expect(name, cond, detail=""):
    print(("ok  " if cond else "FAIL") + f" {name}")
    if not cond:
        fails.append(name)
        print("    " + str(detail)[:800].replace("\n", "\n    "))


def applies(src, names):
    out = {}
    for n in names:
        try:
            out[n] = mutants.mutant(n, src) != src
        except AssertionError as e:
            out[n] = f"anchor: {e}"
    return out


frozen = open(os.path.join(B1A, "b1a_frozen.c")).read()
ref = open(os.path.join(B1A, "b1a_ref.c")).read()
vst = open(os.path.join(B1A, "b1a.c")).read()
for name, src, names in [("b1a.c", vst, mutants.C_LEVEL),
                         ("b1a_frozen.c", frozen,
                          mutants.C_LEVEL + mutants.SPEC_LEVEL),
                         ("b1a_ref.c", ref, mutants.RUNTIME)]:
    r = applies(src, names)
    expect(f"{name}: every mutant applies", all(v is True for v in r.values()),
           r)

# Annotations between the lines of each mutated statement.
annotated = (frozen
             .replace("  for (l = the_list; l != NULL; l = l->ptr_to_next)\n",
                      "  for (l = the_list; l != NULL; l = l->ptr_to_next)\n"
                      "    /*@ assert l != \\null; */\n")
             .replace("    if (l == NULL)\n",
                      "    if (l == NULL)\n      //@ assert l == \\null;\n")
             .replace("    l->i = input[k];\n",
                      "    /*@ assert \\valid(l)\n"
                      "          && \\valid(&l->i); */\n"
                      "    l->i = input[k];\n"))
assert annotated.count("@ assert") == 3
r = applies(annotated, mutants.C_LEVEL + ["vacuity"])
expect("annotations inside the mutated statements: every mutant applies",
       all(v is True for v in r.values()), r)
u = mutants.mutant("uaf", annotated)
w = u.index("  for (l = the_list;")
expect("uaf moves the walk with its inner annotation after the free loop",
       u[w:].startswith("  for (l = the_list; l != NULL; "
                        "l = l->ptr_to_next)\n    /*@ assert l != \\null; */"
                        "\n    last = l->i;\n")
       and w > u.index("ariadne_free_dllist(l);"), u[w - 200:w + 200])
n = mutants.mutant("nullchk", annotated)
expect("nullchk removes the check (and the assert inside it)",
       "if (l == NULL)" not in n and "assert l == \\null" not in n)
print(f"{'FAIL' if fails else 'PASS'}: {len(fails)} failed")
sys.exit(1 if fails else 0)
