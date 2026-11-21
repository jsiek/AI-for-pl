"""Dry run of the M6 pipeline with no LLM: run_vst.py's setup for
`--bench dllist` (dry run), then m6.check (check_vst.py --bench dllist)
on hand-written proof files standing in for the prover:

  good       body_it_init proved by hand (m6_fixtures/it_init_proof.txt),
             the other five stated exactly and Admitted:
             accepted for it_init (PROVED), the others OPEN, no violation;
  spec_edit  body_get_first proved against an edited funspec, and the
             run directory's spec_dllist.v edited: rejected (wrong
             statement; frozen file changed);
  axiom      an `Axiom`: rejected (lint);
  tt_post    a helper funspec with TT in its postcondition: rejected
             (post_lint).

Runs Coq in the VST image (slow: several minutes per case).

    python3 test_m6_check.py [case ...]
"""
import json
import os
import shutil
import subprocess
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
ARIADNE = os.path.dirname(HERE)
sys.path.insert(0, HERE)
import m6  # noqa: E402

HEAD = """Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import SglibVST.dllist SglibVST.spec_dllist.

Section Proofs.
Variable Rc : globals -> val -> mpred.
"""
IT_INIT = open(os.path.join(HERE, "m6_fixtures", "it_init_proof.txt")).read()


def lemma(f, spec, rc, proof="Admitted."):
    sp = "(%s Rc)" % spec if rc else spec
    return ("Lemma body_%s :\n  semax_body Vprog (Gprog Rc) "
            "f_sglib_dllist_%s %s.\n%s\n" % (f, f, sp,
                                              proof if proof.startswith(
                                                  "Proof") else proof))


def verif(extra="", overrides=None):
    overrides = overrides or {}
    body = []
    for f, spec, rc in m6.FUNCS:
        if f in overrides:
            body.append(overrides[f])
        elif f == "it_init":
            body.append(lemma(f, spec, rc, IT_INIT))
        else:
            body.append(lemma(f, spec, rc))
    return HEAD + extra + "\n".join(body) + "\nEnd Proofs.\n"


WEAK_GET_FIRST = """Definition my_get_first_spec :=
 DECLARE _sglib_dllist_get_first
  WITH p: val
  PRE [ tptr t_dl ] PROP () PARAMS (p) SEP ()
  POST [ tptr t_dl ] PROP () RETURN (p) SEP ().
Lemma body_get_first :
  semax_body Vprog (Gprog Rc) f_sglib_dllist_get_first my_get_first_spec.
Admitted.
"""

TT_HELPER = """Definition helper_spec : funspec :=
  WITH p: val
  PRE [ tptr tint ] PROP () PARAMS (p) SEP ()
  POST [ tvoid ] PROP () RETURN () SEP (TT).
"""

CASES = {
    "good": (verif(), None),
    "spec_edit": (verif(overrides={"get_first": WEAK_GET_FIRST}),
                  "spec_dllist.v"),
    "axiom": (verif(extra="Axiom cheat : False.\n"), None),
    "tt_post": (verif(extra=TT_HELPER), None),
}


def expect(name, cond, detail):
    print(("ok  " if cond else "FAIL") + " " + name, flush=True)
    if not cond:
        print("    " + json.dumps(detail)[:1500])
    return cond


def main(names):
    fails = 0
    for case in names or list(CASES):
        text, edit = CASES[case]
        run = os.path.join(ARIADNE, "runs", "m6", "test-" + case)
        shutil.rmtree(run, ignore_errors=True)
        if os.path.exists(run + ".tool"):
            os.remove(run + ".tool")
        p = subprocess.run([sys.executable, os.path.join(HERE, "run_vst.py"),
                            "--bench", "dllist", "--dry-run", "--run-dir",
                            run], capture_output=True, text=True)
        assert p.returncode == 0, p.stderr
        open(os.path.join(run, "verif_dllist.v"), "w").write(text)
        if edit:
            with open(os.path.join(run, edit), "a") as f:
                f.write("\n(* edited *)\n")
        s = m6.check(run, "dllist")
        v = s["violations"]
        lem = s.get("lemmas", {})
        if case == "good":
            ok = expect("good: no violation; it_init PROVED, the other five "
                        "OPEN", not v and lem.get("body_it_init") == "PROVED"
                        and len([k for k, x in lem.items()
                                 if x.startswith("OPEN")]) == 5, s)
        elif case == "spec_edit":
            ok = expect("spec_edit: rejected (get_first's statement; the "
                        "frozen spec_dllist.v changed)",
                        any("body_get_first" in x for x in v)
                        and any("frozen file" in x for x in v), s)
        elif case == "axiom":
            ok = expect("axiom: rejected by the lint",
                        any("forbidden" in x for x in v), s)
        else:
            ok = expect("tt_post: rejected by post_lint",
                        any("post_lint" in x for x in v)
                        and "helper_spec" in s["post_lint"]["out"], s)
        fails += 0 if ok else 1
    print("%s: %d failed" % ("FAIL" if fails else "PASS", fails))
    return 1 if fails else 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
