"""Tests of the unanchored-postcondition lint (spec_lint.py, plan Q11
rule 2).  Uses the image's cpp to expand the spec templates.

  * B1's spec now (bench/sglib_spec) and the self-test's: nothing flagged;
  * the iterator spec of 2026-11-07 (fixtures/sglib_dl_list_spec.h, a
    copy of the template before the owner's change of 2026-11-08):
    it_init, it_init_on_equal and it_next flagged, nothing else;
  * get_first / get_last as they were before eaa42ed2 (2026-11-03):
    both flagged, nothing else.

    python3 test_spec_lint.py
"""
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
ARIADNE = os.path.dirname(HERE)
sys.path.insert(0, HERE)
import spec_lint  # noqa: E402
from acsl_expand import expand  # noqa: E402

fails = []


def expect(name, cond, detail=""):
    print(("ok  " if cond else "FAIL") + f" {name}")
    if not cond:
        fails.append(name)
        print("    " + str(detail)[:1200].replace("\n", "\n    "))


NEW = "-I/ariadne/plugin/share -I/ariadne/bench/sglib_spec"
OLD = "-I/ariadne/plugin/share -I/ariadne/harness/fixtures"
frozen = open(os.path.join(ARIADNE, "bench", "b1", "b1_frozen.c")).read()


def flagged(text, cpp):
    return sorted(f["function"] for f in spec_lint.lint(expand(text, cpp)))


r = flagged(frozen, NEW)
expect("B1's spec (2026-11-08): nothing flagged", r == [], r)
st = open(os.path.join(ARIADNE, "bench", "selftest", "wp", "st_wp.c")).read()
r = flagged(st, NEW)
expect("the self-test's instance: nothing flagged", r == [], r)
r = flagged(frozen, OLD)
expect("the 2026-11-07 iterator spec: it_init, it_init_on_equal, it_next",
       r == ["sglib_dllist_it_init", "sglib_dllist_it_init_on_equal",
             "sglib_dllist_it_next"], r)

# get_first / get_last before eaa42ed2: the result is in *some* live list.
OLD_FIRST = """/*@ requires list == \\null || in_live_list(list);
    assigns \\nothing;
    ensures \\exists \\list<dllist *> s; live_dll(\\null, \\result, s);
*/"""
OLD_LAST = """/*@ requires list == \\null || in_live_list(list);
    assigns \\nothing;
    ensures \\result == \\null
            || \\exists dllist *h, \\list<dllist *> s;
                 live_dll(\\null, h, s) && \\length(s) > 0
                 && \\result == \\nth(s, \\length(s) - 1);
*/"""
old = (frozen
       .replace("/*@ SGLIB_DL_LIST_CONTRACT_GET_FIRST(dllist, ptr_to_previous,"
                " ptr_to_next) */", OLD_FIRST)
       .replace("/*@ SGLIB_DL_LIST_CONTRACT_GET_LAST(dllist, ptr_to_previous,"
                " ptr_to_next) */", OLD_LAST))
assert old.count("live_dll(\\null, \\result, s)") == 1
r = flagged(old, NEW)
expect("get_first / get_last before eaa42ed2: both flagged",
       r == ["sglib_dllist_get_first", "sglib_dllist_get_last"], r)

# Units: an anchor through a parameter's value, a pre-state term, and
# \result tied to an input elsewhere; and a dereference is no anchor.
preds = {}
cases = [
    ("ensures \\exists integer k; k == n;", ["n"], 0),
    ("ensures \\exists integer k; k == \\old(p->x);", ["p"], 0),
    ("ensures \\exists integer k; k == p->x;", ["p"], 1),
    ("ensures \\result == n; ensures \\exists integer k; k == \\result;",
     ["n"], 0),
    ("ensures \\exists integer k; k == \\result;", ["n"], 1),
]
for contract, params, n in cases:
    got = spec_lint.anchored(contract, params, preds)
    expect(f"unit: {contract} -> {n} finding(s)", len(got) == n, got)
print(f"{'FAIL' if fails else 'PASS'}: {len(fails)} failed")
sys.exit(1 if fails else 0)
