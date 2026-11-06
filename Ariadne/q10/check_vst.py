#!/usr/bin/env python3
"""Plan Q10, VST side: check what a run_vst.py run proved, and its
mutant rejection, against a pristine copy of the C code.

    python3 check_vst.py RUN_DIR

In RUN_DIR/q10-check/<case>/ (case: control, then the C-level mutants
of mutants.py), with ../bench/b1a/b1a.c (mutated for a mutant) and the
run's verif_b1a.v only: clightgen -normalize, coqc of the AST, coqc of
verif_b1a.v, in the VST image.  The control also gets: the lint (no
Admitted, admit, Axiom, Parameter, Conjecture), the list of `semax_body`
lemmas with how each ends (Qed or Admitted), `prog_correct`, and Print
Assumptions against ../vst/smoke/expected_assumptions.txt (VST's
allocator assumptions and the classical axioms).  A mutant is rejected
if coqc fails on verif_b1a.v.  Output: RUN_DIR/q10-check/summary.json.
"""
import hashlib
import json
import os
import re
import shutil
import subprocess
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
ARIADNE = os.path.dirname(HERE)
sys.path.insert(0, HERE)
import mutants  # noqa: E402

RUN = os.path.join(ARIADNE, "vst", "run.sh")
B1A_C = os.path.join(ARIADNE, "bench", "b1a", "b1a.c")
EXPECTED = os.path.join(ARIADNE, "vst", "smoke", "expected_assumptions.txt")
COQC = ["coqc", "-native-compiler", "no", "-Q", ".", "B1a"]
FORBIDDEN = r"\b(Admitted|admit|Axiom|Parameter|Conjecture)\b"


def sh(work, cmd, log):
    with open(os.path.join(work, log), "w") as f:
        return subprocess.run([RUN] + cmd, cwd=work, stdout=f,
                              stderr=subprocess.STDOUT).returncode


def compile_case(work, src, verif):
    shutil.rmtree(work, ignore_errors=True)
    os.makedirs(work)
    open(os.path.join(work, "b1a.c"), "w").write(src)
    shutil.copy(verif, work)
    r = {"clightgen": sh(work, ["clightgen", "-normalize", "b1a.c"],
                         "clightgen.log")}
    r["ast"] = sh(work, COQC + ["b1a.v"], "ast.log")
    r["verif"] = sh(work, COQC + ["verif_b1a.v"], "verif.log")
    text = open(os.path.join(work, "verif.log")).read()
    m = re.search(r'File "\./verif_b1a\.v", line (\d+)', text)
    if r["verif"] and m:
        r["first_error_line"] = int(m.group(1))
        r["first_error_in"] = enclosing(verif, int(m.group(1)))
        r["error"] = text[m.start():m.start() + 600]
    return r


def enclosing(verif, line):
    """The name of the Lemma/Definition/Theorem the line is in."""
    name = None
    for i, l in enumerate(open(verif).read().split("\n"), 1):
        if i > line:
            break
        m = re.match(r"\s*(Lemma|Theorem|Definition|Fixpoint)\s+(\S+)", l)
        if m:
            name = m.group(2)
    return name


def lemmas(verif):
    """Each semax_body / semax_prog lemma and how its proof ends."""
    text = open(verif).read()
    out = {}
    for m in re.finditer(r"(Lemma|Theorem)\s+(\w+)\s*:([^.]*?)\.\s*\n",
                         text, re.S):
        if "semax_body" not in m.group(3) and "semax_prog" not in m.group(3):
            continue
        end = re.search(r"\b(Qed|Admitted|Defined|Abort)\.", text[m.end():])
        out[m.group(2)] = end.group(1) if end else "(none)"
    return out


def main():
    run = os.path.abspath(sys.argv[1])
    verif = os.path.join(run, "verif_b1a.v")
    out = os.path.join(run, "q10-check")
    os.makedirs(out, exist_ok=True)
    pristine = open(B1A_C).read()
    run_c = os.path.join(run, "b1a.c")
    s = {"b1a_c_unchanged": os.path.exists(run_c) and hashlib.sha256(
        open(run_c, "rb").read()).hexdigest() == hashlib.sha256(
        pristine.encode()).hexdigest()}
    if not os.path.exists(verif):
        s["verif"] = "missing"
        json.dump(s, open(os.path.join(out, "summary.json"), "w"), indent=1)
        print(json.dumps(s, indent=1))
        return
    s["verif_lines"] = len(open(verif).read().split("\n"))
    s["forbidden"] = [f"{i}: {l.strip()}" for i, l in
                      enumerate(open(verif).read().split("\n"), 1)
                      if re.search(FORBIDDEN, l)
                      and not l.strip().startswith("(*")]
    s["lemmas"] = lemmas(verif)
    c = compile_case(os.path.join(out, "control"), pristine, verif)
    log = open(os.path.join(out, "control", "verif.log")).read()
    if c["verif"] == 0 and "Axioms:" in log:
        got = log[log.index("Axioms:"):]
        c["assumptions_as_expected"] = (got.strip()
                                        == open(EXPECTED).read().strip())
        c["assumptions"] = got
    s["control"] = c
    print("control:", json.dumps({k: v for k, v in c.items()
                                  if k != "assumptions"}), flush=True)
    s["mutants"] = {}
    for name in mutants.C_LEVEL:
        r = compile_case(os.path.join(out, name),
                         mutants.mutant(name, pristine), verif)
        r["verdict"] = ("rejected" if r["clightgen"] == 0 and r["ast"] == 0
                        and r["verif"] != 0 else "NOT rejected"
                        if r["verif"] == 0 else "error")
        s["mutants"][name] = r
        print(f"{name}: {r['verdict']} (first error in "
              f"{r.get('first_error_in')})", flush=True)
    json.dump(s, open(os.path.join(out, "summary.json"), "w"), indent=1)


if __name__ == "__main__":
    main()
