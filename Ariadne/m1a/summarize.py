"""Summarise M1a WP reports: did each test function behave as expected?

    python3 summarize.py alloc.c report_Typed.json [report_Bytes.json ...]

Expectations come from the C source itself:
  good_*     every goal proved;
  bad_*      the goals on the line marked `BAD` fail, all others proved;
  vacuous_*  the `assert vacuity: \\false` fails.
A test is SOUND if nothing that should fail was proved, and COMPLETE if
nothing that should be proved failed.
"""

import json
import re
import sys
from collections import defaultdict


def bad_lines(path):
    lines = defaultdict(set)
    func = None
    with open(path) as f:
        for n, text in enumerate(f, 1):
            m = re.match(r"\w[\w\s\*]*\b(\w+)\(void\) \{", text)
            if m:
                func = m.group(1)
            if "BAD" in text or "vacuity" in text:
                lines[func].add(n)
    return lines


def classify(goals, expected_fail_lines):
    should_fail = [g for g in goals if g["line"] in expected_fail_lines]
    should_pass = [g for g in goals if g["line"] not in expected_fail_lines]
    unsound = [g for g in should_fail if g["verdict"] == "valid"]
    incomplete = [g for g in should_pass if g["verdict"] != "valid"]
    if expected_fail_lines and not should_fail:
        unsound = [{"goal": "(no goal generated at BAD line)", "line": 0}]
    return unsound, incomplete


def main():
    expected = bad_lines(sys.argv[1])
    all_ok = True
    for report in sys.argv[2:]:
        goals = json.load(open(report))
        by_func = defaultdict(list)
        for g in goals:
            by_func[g["function"]].append(g)
        print(f"== {report}")
        for func in sorted(by_func):
            unsound, incomplete = classify(by_func[func], expected[func])
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
