"""Regression tests for gen_rac.py's clause splitting: run it on b1.c
with extra asserts inserted, and check what it keeps.
Usage: python3 -I test_gen_rac.py <b1.c> <scratch dir>"""
import os
import subprocess
import sys

src_path, tmp = sys.argv[1], sys.argv[2]
here = os.path.dirname(os.path.abspath(__file__))
src = open(src_path).read()

# Inserted after add's `linked` assert.  ACSL: ==> and <==> bind looser
# than &&, so `a ==> b && c` is `a ==> (b && c)`.
anchor = "&& all_live(\\Cons(elem, \\Cons(\\at(*list, Pre), t))); */\n"
assert src.count(anchor) == 1
extra = (
    # dll{Pre} cannot be translated; the whole implication must go, not
    # leave `elem->i == 0` unguarded.
    "    /*@ assert prec_impl: elem == \\null ==>\n"
    "          dll{Pre}(\\null, elem, \\Nil) && elem->i == 0; */\n"
    # independent conjuncts are still split: the first is kept.
    "    /*@ assert prec_conj: elem != \\null\n"
    "          && dll{Pre}(\\null, elem, \\Nil); */\n"
    # <==> is not split at its ==>.
    "    /*@ assert prec_iff: elem != \\null <==> \\valid(elem); */\n")
i = src.index(anchor) + len(anchor)
os.makedirs(tmp, exist_ok=True)
fixture = os.path.join(tmp, "b1_prec.c")
open(fixture, "w").write(src[:i] + extra + src[i:])

subprocess.run([sys.executable, "-I", os.path.join(here, "gen_rac.py"),
                fixture, tmp], check=True, stdout=subprocess.DEVNULL)
report = open(os.path.join(tmp, "annotations.txt")).read()
out = open(os.path.join(tmp, "b1_rac.c")).read()


def line(name):
    ls = [l for l in report.splitlines() if f"assert {name}:" in l]
    assert len(ls) == 1, (name, ls)
    return ls[0]


fails = []
if ": dropped" not in line("prec_impl") or "prec_impl" in out:
    fails.append("prec_impl: implication not dropped as a whole")
if ": partly-kept" not in line("prec_conj") or "assert prec_conj: elem != \\null;" not in out.replace("\n", " ").replace("  ", " "):
    fails.append("prec_conj: independent conjunct not kept")
if ": kept" not in line("prec_iff") or "<==>" not in out:
    fails.append("prec_iff: <==> split")
for f in fails:
    print("FAIL:", f)
if fails:
    sys.exit(1)
print("ok: 3 clause-splitting cases")
