#!/usr/bin/env python3
"""Plan Q10, Frama-C side: mutant rejection on a harness run's result.

    python3 check_wp.py RUN_DIR [MUTANT ...]

RUN_DIR is a harness run (../runs/q10/wp-<time>): its final source is
RUN_DIR/bench/b1a_frozen.c (the last accepted patch) and its Coq proofs
RUN_DIR/bench/session/interactive/*.v.  For the control (the source
unchanged) and each mutant of mutants.py, WP runs as in
../bench/b1/check.sh (-ariadne, -wp-rte -rte-initialized @all,
-wp-no-filter-init, Alt-Ergo/Z3/CVC5/Coq, 60 s) on the mutant's
function, with the run's Coq scripts in the session.  A mutant is
rejected if WP leaves open a goal of that function that the control
proves (the control should leave none; for a partial result, its open
goals do not count).  Output: RUN_DIR/q10-mutants/ and
RUN_DIR/q10-mutants/summary.json.
"""
import json
import os
import shutil
import subprocess
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
ARIADNE = os.path.dirname(HERE)
sys.path.insert(0, HERE)
import mutants  # noqa: E402

RUN = os.path.join(ARIADNE, "env", "run.sh")
CPP = "-I/ariadne/plugin/share -I/ariadne/bench/b1a/spec"


def wp(work, src, fct):
    open(os.path.join(work, "b1a.c"), "w").write(src)
    cmd = [RUN, "frama-c",
           "-load-module", "/ariadne/plugin/_build/default/ariadne.cmxs",
           f"-cpp-extra-args={CPP}",
           "-generated-spec-custom", "terminates:skip", "-ariadne", "b1a.c",
           "-then", "-wp", "-wp-rte", "-rte-initialized", "@all",
           "-wp-no-filter-init", "-wp-model", "Typed", "-wp-fct", fct,
           "-wp-prover", "alt-ergo,z3,cvc5,coq", "-wp-interactive", "batch",
           "-wp-timeout", "60", "-wp-session", "/work/session",
           "-wp-report-json", "/work/report.json"]
    with open(os.path.join(work, "wp.log"), "w") as log:
        rc = subprocess.run(cmd, cwd=work, stdout=log,
                            stderr=subprocess.STDOUT).returncode
    rep = os.path.join(work, "report.json")
    if rc != 0 or not os.path.exists(rep):
        return {"ok": False, "exit": rc, "error": "WP run failed"}
    goals = json.load(open(rep))
    bad = [g["goal"] for g in goals if g["verdict"] != "valid"]
    return {"ok": True, "goals": len(goals), "open": bad}


def main():
    run = os.path.abspath(sys.argv[1])
    names = sys.argv[2:] or mutants.C_LEVEL + mutants.SPEC_LEVEL
    src = open(os.path.join(run, "bench", "b1a_frozen.c")).read()
    inter = os.path.join(run, "bench", "session", "interactive")
    out = os.path.join(run, "q10-mutants")
    os.makedirs(out, exist_ok=True)
    summary = {}
    for name in ["control"] + names:
        work = os.path.join(out, name)
        shutil.rmtree(work, ignore_errors=True)
        os.makedirs(os.path.join(work, "session"))
        if os.path.isdir(inter):
            shutil.copytree(inter, os.path.join(work, "session",
                                                "interactive"))
        if name == "control":
            fcts = ",".join(sorted(set(mutants.FUNCTION.values())))
            r = wp(work, src, fcts)
            r["verdict"] = ("all proved" if r["ok"] and not r["open"]
                            else "NOT all proved")
        else:
            r = wp(work, mutants.mutant(name, src), mutants.FUNCTION[name])
            # A result that is not fully proved: only goals the control
            # proved count (names are per function and per property).
            base = set(summary["control"].get("open", []))
            r["new_open"] = [g for g in r.get("open", []) if g not in base]
            r["verdict"] = ("rejected" if r["ok"] and r["new_open"]
                            else "NOT rejected" if r["ok"] else "error")
        summary[name] = r
        print(f"{name}: {r['verdict']} {r.get('new_open', r.get('open'))[:4]}",
              flush=True)
    json.dump(summary, open(os.path.join(out, "summary.json"), "w"),
              indent=1)


if __name__ == "__main__":
    main()
