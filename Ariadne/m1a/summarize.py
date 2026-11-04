"""Summarise M1a WP reports: did each test function behave as expected?

    python3 summarize.py [--any] alloc.c report_Typed.json [report_Bytes.json ...]

Expectations come from the C source itself:
  good_*     every goal proved;
  bad_*      the goals on the line marked `BAD` fail, all others proved;
  vacuous_*  the `assert vacuity: \\false` fails.
A test is SOUND if nothing that should fail was proved, and COMPLETE if
nothing that should be proved failed.  With --any, a bad_* test is SOUND
if at least one goal on its BAD line fails (used when a checking assert
shares its line with a goal WP proves anyway, as with the plugin).

Every good_/bad_/vacuous_ function defined in the source must appear in
each report; a missing one is reported as MISSING and counts as a
failure, so a dropped obligation cannot make a run pass.
"""

import json
import re
import sys
from collections import defaultdict

TEST_PREFIXES = ("good_", "bad_", "vacuous_")


def parse_source(path):
    """Test functions defined in the source, and their BAD/vacuity lines."""
    tests = []
    lines = defaultdict(set)
    func = None
    with open(path) as f:
        for n, text in enumerate(f, 1):
            m = re.match(r"\w[\w\s\*]*\b(\w+)\([^)]*\) \{", text)
            if m:
                func = m.group(1)
                if func.startswith(TEST_PREFIXES):
                    tests.append(func)
            if "BAD" in text or "vacuity" in text:
                lines[func].add(n)
    return tests, lines


def classify(goals, expected_fail_lines, any_mode=False):
    should_fail = [g for g in goals if g["line"] in expected_fail_lines]
    should_pass = [g for g in goals if g["line"] not in expected_fail_lines]
    unsound = [g for g in should_fail if g["verdict"] == "valid"]
    if any_mode and len(unsound) < len(should_fail):
        unsound = []
    incomplete = [g for g in should_pass if g["verdict"] != "valid"]
    if expected_fail_lines and not should_fail:
        unsound = [{"goal": "(no goal generated at BAD line)", "line": 0}]
    return unsound, incomplete


def main():
    args = sys.argv[1:]
    any_mode = args[:1] == ["--any"]
    if any_mode:
        args = args[1:]
    tests, expected = parse_source(args[0])
    all_ok = True
    for report in args[1:]:
        goals = json.load(open(report))
        by_func = defaultdict(list)
        for g in goals:
            by_func[g["function"]].append(g)
        print(f"== {report}")
        for func in sorted(set(tests) | set(by_func)):
            if func not in by_func:
                print(f"  {func:30s} MISSING")
                all_ok = False
                continue
            unsound, incomplete = classify(by_func[func], expected[func],
                                           any_mode)
            verdict = ("ok" if not unsound and not incomplete else
                       ", ".join(filter(None, [
                           "UNSOUND" if unsound else "",
                           "incomplete" if incomplete else ""])))
            print(f"  {func:30s} {verdict}")
            all_ok = all_ok and verdict == "ok"
            for g in unsound:
                print(f"      proved but should fail: {g['goal']}")
            for g in incomplete:
                print(f"      failed but should pass: {g['goal']}"
                      f" (line {g['line']}, {g['verdict']})")
    return 0 if all_ok else 1


if __name__ == "__main__":
    sys.exit(main())
