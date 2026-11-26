"""Tests of post_lint.py on lint/tests/cases.v (compiled first): every
good_* spec passes, every bad_* spec fails, and nothing else is
reported.  Runs Coq in the VST image (../../../vst/run.sh).

    python3 -I test_post_lint.py
"""
import os
import re
import subprocess
import sys
import unittest

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)
RUN = os.path.join(ROOT, "..", "vst", "run.sh")
CASES = os.path.join(HERE, "tests", "cases.v")

EXPECTED_BAD = {
    "bad_tt_spec": "TT",
    "bad_codex_paren_binder_spec": "an existential over mpred",
    "bad_codex_post_newline_spec": "TT",
    "bad_typed_binder_spec": "an existential over mpred",
    "bad_ex_notation_spec": "an existential over mpred",
    "bad_exp_direct_spec": "an existential over mpred",
    "bad_ex_function_spec": "an existential over mpred",
    "bad_hidden_ex_spec": "an existential over mpred",
    "bad_tt_via_definitions_spec": "TT",
    "bad_prop_true_spec": "!! P outside a conjunction",
    "bad_two_props_spec": "a conjunction of two props",
    "bad_wand_spec": "the connective wand",
    "bad_tt_pair_spec": "TT",
    "bad_main_spec": "does not hold mem_mgr",
    "bad_main_tt_spec": "TT",
    "bad_opaque_spec": "no body to examine",
    "bad_foreign_spec": "no postcondition found",
}
EXPECTED_GOOD = {"good_spec", "good_pair_spec", "good_main_spec"}


class PostLint(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        subprocess.run([RUN, "coqc", "-native-compiler", "no", "-Q", ".",
                        "Lint", os.path.relpath(CASES, ROOT)],
                       cwd=ROOT, check=True, capture_output=True)
        p = subprocess.run([sys.executable, "-I",
                            os.path.join(HERE, "post_lint.py"),
                            "--root", ROOT, "--lib", "Lint", "Lint.lint.tests.cases"],
                           capture_output=True, text=True)
        cls.rc, cls.out = p.returncode, p.stdout

    def results(self, kind):
        found = {}
        for line in self.out.split("\n"):
            m = re.match(kind + r": ([\w']+)(.*)", line)
            if m:
                found.setdefault(m.group(1), []).append(m.group(2))
        return found

    def test_exit_code(self):
        self.assertEqual(self.rc, 1)

    def test_bad_specs_fail_for_the_right_reason(self):
        fails = self.results("FAIL")
        self.assertEqual(set(fails), set(EXPECTED_BAD), self.out)
        for name, why in EXPECTED_BAD.items():
            self.assertTrue(any(why in r for r in fails[name]),
                            (name, fails[name]))

    def test_good_specs_pass(self):
        self.assertEqual(set(self.results("OK")), EXPECTED_GOOD, self.out)


if __name__ == "__main__":
    unittest.main()
