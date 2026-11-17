"""Tests of post_lint.py.   python3 -I test_post_lint.py"""
import os
import sys
import unittest

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import post_lint  # noqa: E402

CLEAN = """
Definition cell (p: val) : mpred := data_at Ews tint (Vint Int.zero) p.
(* TT in a comment is ignored. *)
Definition f_spec :=
 DECLARE _f
  WITH p: val
  PRE [ tptr tint ] PROP () PARAMS (p) SEP (cell p)
  POST [ tvoid ] PROP () RETURN () SEP (cell p).
"""


class PostLint(unittest.TestCase):
    def lint(self, text):
        return post_lint.lint([text])

    def test_clean_passes(self):
        self.assertEqual(self.lint(CLEAN), [])

    def test_tt_in_post_fails(self):
        r = self.lint(CLEAN.replace("SEP (cell p).", "SEP (cell p; TT)."))
        self.assertEqual(len(r), 1)
        self.assertIn("TT", r[0])

    def test_tt_in_used_helper_fails(self):
        text = CLEAN.replace(
            "Definition cell (p: val) : mpred := data_at",
            "Definition cell (p: val) : mpred := TT * data_at")
        r = self.lint(text)
        self.assertEqual(len(r), 1)
        self.assertIn("f_spec -> cell", r[0])

    def test_tt_in_nested_helper_fails(self):
        text = ("Definition junk : mpred := TT.\n"
                "Definition wrap (p: val) : mpred := cell p * junk.\n"
                + CLEAN.replace("SEP (cell p).", "SEP (wrap p)."))
        r = self.lint(text)
        self.assertEqual(len(r), 1)
        self.assertIn("f_spec -> wrap -> junk", r[0])

    def test_ex_mpred_fails(self):
        r = self.lint(CLEAN.replace(
            "POST [ tvoid ] PROP ()",
            "POST [ tvoid ] EX R: mpred, PROP ()").replace(
            "SEP (cell p).", "SEP (cell p; R)."))
        self.assertEqual(len(r), 1)
        self.assertIn("existential over mpred", r[0])

    def test_tt_only_in_pre_passes(self):
        self.assertEqual(self.lint(CLEAN.replace(
            "SEP (cell p)\n", "SEP (cell p; TT)\n")), [])

    def test_unused_private_helper_passes(self):
        self.assertEqual(self.lint(
            "Definition junk : mpred := TT.\n" + CLEAN), [])

    def test_val_eq_does_not_split(self):
        text = ("Definition c (p: val) : mpred :=\n"
                "  if Val.eq p nullval then emp else TT.\n"
                + CLEAN.replace("SEP (cell p).", "SEP (c p)."))
        self.assertEqual(len(self.lint(text)), 1)

    def test_main_needs_mem_mgr(self):
        main = """
Definition main_spec :=
 DECLARE _main
  WITH gv: globals
  PRE [ ] main_pre prog tt gv
  POST [ tint ] EX r: Z, PROP () RETURN (Vint (Int.repr r)) SEP ().
"""
        r = self.lint(main)
        self.assertEqual(len(r), 1)
        self.assertIn("mem_mgr", r[0])
        self.assertEqual(self.lint(main.replace("SEP ()",
                                                "SEP (mem_mgr gv)")), [])
        r = self.lint(main.replace("SEP ()", "SEP (mem_mgr gv; TT)"))
        self.assertEqual(len(r), 1)
        self.assertIn("TT", r[0])


if __name__ == "__main__":
    unittest.main()
