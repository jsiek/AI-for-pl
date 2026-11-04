"""Tests of the tier-0 search (tier0.py).  No model calls; the second
part runs Pétanque and coqc in the M0 image on two small goals in B1's
Why3 context: one sauto proves, one that is false (the search must give
up at its time cap, and coqc must never have accepted anything).

    python3 test_tier0.py [--quick]     (--quick: no image)
"""
import os
import shutil
import subprocess
import sys
import tempfile

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import tier0  # noqa: E402

ARIADNE = tier0.ARIADNE
GOAL = os.path.join(ARIADNE, "bench", "b1", "session", "interactive",
                    "lemma_mem_cons.v")
fails = []


def expect(name, cond, detail=""):
    print(("ok  " if cond else "FAIL") + f" {name}")
    if not cond:
        fails.append(name)
        print("    " + str(detail)[:800].replace("\n", "\n    "))


st = ("Theorem wp_goal :\n  forall (t:addr -> addr) (a b:addr)\n"
      "    (l:Init.Datatypes.list addr),\n  P_dll t a b l -> "
      "(a = b <-> b = a) -> P_mem a l.\n")
expect("binders", tier0.binders(st) == [
    ("t", "addr -> addr"), ("a", "addr"), ("b", "addr"),
    ("l", "Init.Datatypes.list addr")], tier0.binders(st))
expect("premises: <-> is not a premise", tier0.premises(st) == 2,
       tier0.premises(st))
prefix = open(GOAL).read().split("(* Why3 goal *)")[0]
c = tier0.candidates(prefix, st)
expect("candidates: unfold the statement's definitions, induction on "
       "the list and the premises",
       "intros; unfold P_mem in *; sauto." in c
       and "induction l; sauto." in c and "induction 2; sauto." in c
       and not any("induction 3" in x for x in c), c)
expect("candidates: library lemmas from the context",
       any(x.startswith("intros; unfold P_mem in *; sauto use: nth_zero, "
                        "nth_cons, length_cons, length_pos") for x in c), c)
expect("reconstructed hammer tactic",
       tier0.reconstructed([[4, "Replace the hammer tactic with:\n"
                             "  srun eauto use: nth_cons."]])
       == "srun eauto use: nth_cons.")

if "--quick" not in sys.argv:
    tmp = tempfile.mkdtemp(dir=os.path.join(ARIADNE, "runs"), prefix="test_")
    try:
        def goal(name, statement):
            p = os.path.join(tmp, name)
            open(p, "w").write(prefix + "(* Why3 goal *)\nTheorem wp_goal :\n"
                               + statement + "\nProof.\nintros.\n\nQed.\n")
            return p

        p = goal("easy.v", "  forall (a:addr) (l:Init.Datatypes.list addr),\n"
                 "  ~ (Init.Datatypes.cons a l = Init.Datatypes.nil) /\\\n"
                 "  (P_mem a l -> P_mem a l).")
        s = tier0.Search(p, 120, 30)
        r = s.run()
        expect("easy goal proved, coqc accepted",
               r["status"] == "proved" and r["tried"][-1]["coqc"][-1]["ok"],
               r)
        s.apply(r["script"] or "")
        text = open(p).read()
        expect("--apply writes the script between Proof. and Qed.",
               f"Proof.\n{r['script']}\nQed." in text, text[-300:])
        p = goal("false.v", "  forall (a b:addr), a = b.")
        r = tier0.Search(p, 10, 30).run()
        expect("false goal: open, stopped by the goal cap",
               r["status"] == "open" and r.get("stopped") == "goal time cap"
               and r["seconds"] < 60
               and not any(t.get("coqc") for t in r["tried"]), r)
    finally:
        shutil.rmtree(tmp)
    left = subprocess.run(["docker", "ps", "-q", "--filter",
                           f"name=ariadne-pet-{os.getpid()}-"],
                          capture_output=True, text=True).stdout.strip()
    expect("no container left", not left, left)

print(f"{'FAIL' if fails else 'PASS'}: {len(fails)} failed")
sys.exit(1 if fails else 0)
