#!/usr/bin/env python3
"""Plan §4: one prover run (cap $10) per musl function; if check()
accepts the proof the function is verified from source, otherwise it
gets a trusted spec the owner approves.

    python3 run_libc.py UNIT --dry-run   # set up a run directory, call nothing
    python3 run_libc.py UNIT             # the paid run, then the check
    python3 run_libc.py --check RUN_DIR  # re-check a run
    python3 run_libc.py isupper --check proofs   # re-check a kept proof

UNIT is a key of UNITS: musl source files (after fetch_musl.py and
musl_clight.py), preprocessed into one self-contained C file as
clightgen does (CompCert's defines, so musl's byte-at-a-time loops).
The run proves `semax_body` for each function of the unit, against the
frozen specs in specs/UNIT.v for the functions picol calls (VST's own
progs64/verif_strlib.v specs where they exist) and against specs the
agent writes for the unit's internal helpers.  The sandbox, the
permission fence and the budget ledger are q10/run_vst.py's.

check() recompiles from pristine copies of UNIT.c and spec_UNIT.v and
the run's verif_UNIT.v only, and requires: each body lemma's statement
(frozen specs by conversion), each proved function's spec in Gprog, no
Admitted/admit/Axiom/Parameter/Conjecture, and Print Assumptions of
every body lemma within vst/smoke/expected_assumptions.txt.
"""
import argparse
import json
import os
import re
import shutil
import subprocess
import sys
import time

HERE = os.path.dirname(os.path.abspath(__file__))
ARIADNE = os.path.dirname(HERE)
M = os.path.join(HERE, "musl-1.2.6")
RUN = os.path.join(ARIADNE, "vst", "run.sh")
EXPECTED = os.path.join(ARIADNE, "vst", "smoke", "expected_assumptions.txt")
sys.path.insert(0, os.path.join(ARIADNE, "q10"))
sys.path.insert(0, os.path.join(ARIADNE, "harness"))
import budget  # noqa: E402
import run_vst  # noqa: E402

# unit: (musl files, functions with frozen specs, internal helpers)
UNITS = {
    "strlen": (["string/strlen.c"], ["strlen"], []),
    "strcmp": (["string/strcmp.c"], ["strcmp"], []),
    "strchr": (["string/strlen.c", "string/strchrnul.c", "string/strchr.c"],
               ["strlen", "strchr"], ["__strchrnul"]),
    "memcpy": (["string/memcpy.c"], ["memcpy"], []),
    "isupper": (["ctype/isupper.c"], ["isupper"], []),
}
INC = ["-I" + p for p in ("obj/shim", "arch/x86_64", "arch/generic",
                          "obj/src/internal", "src/include", "src/internal",
                          "obj/include", "include")]
COQC = ["coqc", "-native-compiler", "no", "-Q", ".", "Libc"]
FORBIDDEN = r"\b(Admitted|admit|Axiom|Parameter|Conjecture)\b"


def source(unit):
    """The unit's musl files, preprocessed into one C file."""
    files = UNITS[unit][0]
    wrapper = os.path.join(M, "obj", "unit_%s.c" % unit)
    open(wrapper, "w").write("".join('#include "../src/%s"\n' % f
                                     for f in files))
    r = subprocess.run([RUN, "clightgen", "-E", "-Wp,-nostdinc,-P",
                        "-D_XOPEN_SOURCE=700"] + INC
                       + [os.path.relpath(wrapper, M)],
                       cwd=M, capture_output=True, text=True)
    if r.returncode:
        sys.exit("preprocessing failed: " + r.stderr[-800:])
    body = "\n".join(l for l in r.stdout.splitlines() if l.strip())
    return ("/* musl 1.2.6: %s, preprocessed with CompCert's defines\n"
            " * (Ariadne/libc/run_libc.py).  Do not edit. */\n%s\n"
            % (", ".join("src/" + f for f in files), body))


def spec_file(unit):
    return ("(* Frozen specs for musl's %s (Ariadne/libc/specs/%s.v).  Do not"
            " edit. *)\nRequire Import VST.floyd.proofauto.\n"
            "Require Import Libc.%s.\n"
            "#[export] Instance CompSpecs : compspecs. make_compspecs prog."
            " Defined.\nDefinition Vprog : varspecs. mk_varspecs prog."
            " Defined.\n\n%s" % (unit, unit, unit,
                                 open(os.path.join(HERE, "specs", unit + ".v"))
                                 .read()))


TASK = """\
# Task: VST proof of memory safety for musl's `{unit}`

You are verifying C code with VST (Verifiable C 2.17, CompCert 3.18
clightgen, Rocq 9.0.1).  Files in this directory:

* `{unit}.c`: musl libc 1.2.6's {files}, preprocessed into one
  self-contained file.  Do not change it.
* `spec_{unit}.v`: `CompSpecs`, `Vprog` and the funspecs {frozen_specs}.
  Do not change it.
* `example/`: a small complete VST proof that is not this code
  (`good.c`, `verif_good.v`), as a reference for the setup and style.

## What to produce

One file, `verif_{unit}.v`, that

1. starts with `Require Import VST.floyd.proofauto. Require Import
   VST.floyd.library. Require Import Libc.{unit} Libc.spec_{unit}.` and
   uses `CompSpecs`, `Vprog` and the funspecs of `spec_{unit}.v`
   (do not redefine them);{helpers_item}
{gprog_n}. defines `Gprog : funspecs` containing {all_specs};
{body_n}. proves, for each function f of {all_funcs},
   `Lemma body_f : semax_body Vprog Gprog f_f f_spec.` (with exactly
   these names), each ending in `Qed.`

No `Axiom`, `Parameter`, `admit` or `Conjecture`.  If you cannot finish
a proof, end it with `Admitted.` so that the file still compiles, and
say which ones are open in your last answer.  Helper lemmas are fine.

## How to run the tools

Your only command is `{tool}`: it runs one command inside the VST image,
with this directory mounted at `/work` (the current directory there):

    {tool} clightgen -normalize {unit}.c
    {tool} coqc -native-compiler no -Q . Libc {unit}.v
    {tool} coqc -native-compiler no -Q . Libc spec_{unit}.v
    {tool} coqc -native-compiler no -Q . Libc verif_{unit}.v

`-native-compiler no` is required.  Each call starts a container (a few
seconds); give the Bash call a long timeout.  `coqtop` works the same
way (pipe a script into it to see a goal).  The VST and Rocq sources
are in the image under `/home/rocq/.opam/4.14.2/lib/coq/user-contrib/VST`
and `/home/rocq/.opam/4.14.2/lib/rocq*/`; read them with the tool.  In
particular `progs64/verif_strlib.v` there proves VST's own string
functions (`progs64/strlib.c`) against specs like these; musl's code
differs (for example it reads through `unsigned char *` casts).

## Rules

* Do not read or search anything outside this directory except the VST
  and Rocq installation inside the image (through the tool).
* Run one command per Bash call (no `&&`, `;`, pipes or newlines outside
  the tool's own argument), and write files with Write or Edit.  Any
  other command is denied; a denial does not end the task.
* You have a budget of about ${usd} for this task.  Work toward a
  complete `verif_{unit}.v`; when you are done (or out of budget),
  answer with one line per function: its name and PROVED or OPEN.
"""


def task(unit, tool, usd):
    files, frozen, helpers = UNITS[unit]
    funcs = frozen + helpers
    q = lambda xs: ", ".join("`%s`" % x for x in xs)
    helpers_item = ("\n2. defines a funspec `h_spec` for each internal function"
                    " h of %s\n   (your choice: what the proofs of the other"
                    " functions need);" % q(helpers)) if helpers else ""
    n = 3 if helpers else 2
    return TASK.format(
        unit=unit, files=", ".join("`src/%s`" % f for f in files),
        frozen_specs=q(f + "_spec" for f in frozen), helpers_item=helpers_item,
        gprog_n=n, body_n=n + 1, all_specs=q(f + "_spec" for f in funcs),
        all_funcs=q(funcs), tool=tool, usd=usd)


def setup(run, unit):
    os.makedirs(os.path.join(run, "example"))
    open(os.path.join(run, unit + ".c"), "w").write(source(unit))
    open(os.path.join(run, "spec_%s.v" % unit), "w").write(spec_file(unit))
    smoke = os.path.join(ARIADNE, "vst", "smoke")
    for f in ("good.c", "verif_good.v", "_CoqProject"):
        shutil.copy(os.path.join(smoke, f), os.path.join(run, "example"))
    tool = run + ".tool"
    open(tool, "w").write(run_vst.tool_script(run))
    os.chmod(tool, 0o755)
    return tool


def sh(work, cmd, log):
    with open(os.path.join(work, log), "w") as f:
        return subprocess.run([RUN] + cmd, cwd=work, stdout=f,
                              stderr=subprocess.STDOUT).returncode


def axiom_names(text):
    """The names in a `Print Assumptions` answer (or the allow-list)."""
    return set(re.findall(r"^([\w.']+) :", text, re.M))


def check(run, unit):
    files, frozen, helpers = UNITS[unit]
    verif = os.path.join(run, "verif_%s.v" % unit)
    work = os.path.join(run, "check")
    shutil.rmtree(work, ignore_errors=True)
    os.makedirs(work)
    s = {"unit": unit}
    if not os.path.exists(verif):
        s["verdict"] = "no verif_%s.v" % unit
        return s
    open(os.path.join(work, unit + ".c"), "w").write(source(unit))
    open(os.path.join(work, "spec_%s.v" % unit), "w").write(spec_file(unit))
    shutil.copy(verif, work)
    text = open(verif).read()
    s["forbidden"] = [f"{i}: {l.strip()}" for i, l in
                      enumerate(text.split("\n"), 1)
                      if re.search(FORBIDDEN, l)
                      and not l.strip().startswith("(*")]
    v, p, sp = ("Libc.verif_%s." % unit, "Libc.%s." % unit,
                "Libc.spec_%s." % unit)
    lines = ["Require Import VST.floyd.proofauto.",
             "Require Import Libc.%s Libc.spec_%s Libc.verif_%s." % ((unit,) * 3)]
    for f in frozen + helpers:
        spec = (sp if f in frozen else v) + f + "_spec"
        lines += ["Definition stmt_%s : semax_body %sVprog %sGprog %sf_%s %s"
                  " := %sbody_%s." % (f, sp, v, p, f, spec, v, f),
                  "Goal VST.veric.initial_world.find_id %s_%s %sGprog ="
                  " Some (snd %s). Proof."
                  " reflexivity. Qed." % (p, f, v, spec),
                  "Print Assumptions %sbody_%s." % (v, f)]
    open(os.path.join(work, "check_%s.v" % unit), "w").write(
        "\n".join(lines) + "\n")
    steps = [("clightgen", ["clightgen", "-normalize", unit + ".c"]),
             ("ast", COQC + [unit + ".v"]),
             ("spec", COQC + ["spec_%s.v" % unit]),
             ("verif", COQC + ["verif_%s.v" % unit]),
             ("check", COQC + ["check_%s.v" % unit])]
    for name, cmd in steps:
        s[name] = sh(work, cmd, name + ".log")
        if s[name]:
            s["error"] = open(os.path.join(work, name + ".log")).read()[-1500:]
            break
    if s.get("check") == 0:
        got = axiom_names(open(os.path.join(work, "check.log")).read())
        s["assumptions"] = sorted(got)
        s["unexpected_assumptions"] = sorted(got - axiom_names(
            open(EXPECTED).read()))
    s["verdict"] = ("PROVED" if s.get("check") == 0 and not s["forbidden"]
                    and not s["unexpected_assumptions"] else "NOT PROVED")
    json.dump(s, open(os.path.join(run, "check.json"), "w"), indent=1)
    return s


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("unit", nargs="?", choices=sorted(UNITS))
    ap.add_argument("--check", metavar="RUN_DIR")
    ap.add_argument("--dry-run", action="store_true")
    ap.add_argument("--usd", type=float, default=10.0)
    ap.add_argument("--turns", type=int, default=600)
    ap.add_argument("--seconds", type=int, default=4 * 3600)
    ap.add_argument("--ledger", default=budget.PATH)
    a = ap.parse_args()
    if a.check:
        run = os.path.abspath(a.check)
        fence = os.path.join(run, "fence.json")
        unit = a.unit or json.load(open(fence))["unit"]
        print(json.dumps(check(run, unit), indent=1))
        return
    if not a.unit:
        ap.error("UNIT or --check RUN_DIR")
    run = os.path.join(ARIADNE, "runs", "libc",
                       a.unit + time.strftime("-%Y%m%d-%H%M%S"))
    tool = setup(run, a.unit)
    text = task(a.unit, tool, a.usd)
    open(os.path.join(run, "TASK.md"), "w").write(text)
    prompt = ("Read TASK.md in this directory and do the task it "
              "describes.\n\n" + text)
    cmd = run_vst.command(run, tool, a.usd, a.turns, prompt, "libc")
    env = dict(os.environ, GIT_CEILING_DIRECTORIES=os.path.dirname(run),
               GIT_DIR=os.path.join(run, ".no-git"))
    fence = {"unit": a.unit, "cwd": run, "tool": tool, "command": cmd,
             "files": sorted(os.path.relpath(os.path.join(d, f), run)
                             for d, _, fs in os.walk(run) for f in fs)}
    json.dump(fence, open(os.path.join(run, "fence.json"), "w"), indent=1)
    if a.dry_run:
        print(json.dumps(fence, indent=1))
        return
    ledger = budget.Ledger(a.ledger)
    gate = ledger.reserve("annotator", run_vst.MODEL, a.usd)
    json.dump(gate, open(os.path.join(run, "budget_gate.json"), "w"), indent=1)
    if not gate["ok"]:
        sys.exit("budget ledger refused the call: %s" % json.dumps(gate))
    t0, out, end = time.time(), None, None
    try:
        p = subprocess.run(cmd, cwd=run, env=env, capture_output=True,
                           text=True, timeout=a.seconds,
                           stdin=subprocess.DEVNULL)
        open(os.path.join(run, "result.json"), "w").write(p.stdout)
        out = json.loads(p.stdout)
        end = out.get("subtype")
    except subprocess.TimeoutExpired:
        end = "timeout"
    except ValueError:
        end = "no JSON result"
    except BaseException:
        ledger.release(gate["id"])
        raise
    mu = budget.by_model(out, run_vst.MODEL) if out else {}
    c = ledger.charge("annotator", mu, est_usd=a.usd, model=run_vst.MODEL,
                      reservation=gate["id"])
    summary = {"unit": a.unit, "end": end,
               "seconds": round(time.time() - t0, 1), "usd": c["usd"],
               "total_cost_usd": out and out.get("total_cost_usd"),
               "num_turns": out and out.get("num_turns"),
               "answer": out and (out.get("result") or "")[-2000:]}
    summary["check"] = check(run, a.unit)
    json.dump(summary, open(os.path.join(run, "summary.json"), "w"), indent=1)
    print(json.dumps(summary, indent=1))


if __name__ == "__main__":
    main()
