#!/usr/bin/env python3
"""Plan Q10, VST side: one fresh Opus 5.5 run that writes VST funspecs
for B1a from the English spec and proves every function.

    python3 run_vst.py --dry-run      # set up a run directory, print the
                                      # prompt and command, call nothing
    python3 run_vst.py                # the paid run (cap: --usd, 15)

The run directory (../runs/q10/vst-<time>/, git-ignored) holds only
  b1a.c        the C code (../bench/b1a/b1a.c),
  SPEC.md      the English spec (../bench/b1a/SPEC.md),
  TASK.md      the task (below),
  example/     VST's smoke test (../vst/smoke: good.c, verif_good.v), a
               minimal VST proof that is not B1.
The model's only command is a tool script next to the run directory
(<run>.tool, outside it, so the model cannot edit it): it runs one
command in the VST image with the run directory mounted at /work, no
network, and nothing else of the host.  File tools are confined to the
run directory (--restricted and the allow rules), git and the existing
VST proofs of B1 (../vst/b1) are denied.  The fence is recorded in
<run>/fence.json.

After the call: result.json (Claude Code's JSON result), and
summary.json (wall time, tokens, USD, turns, denials).  The call's cap
is reserved in the budget ledger (--ledger) first; a refusal stops the
run before the call (budget_gate.json).  check_vst.py
then checks what was proved against a pristine copy of b1a.c.
"""
import argparse
import json
import os
import shutil
import subprocess
import sys
import time

HERE = os.path.dirname(os.path.abspath(__file__))
ARIADNE = os.path.dirname(HERE)
REPO = os.path.dirname(ARIADNE)
sys.path.insert(0, os.path.join(ARIADNE, "harness"))
import budget  # noqa: E402

MODEL = "claude-opus-5-5"
IMAGE = "ariadne-vst:dev"

TASK = """\
# Task: VST proofs of memory safety for B1a

You are verifying C code with VST (Verifiable C 2.17, CompCert 3.18
clightgen, Rocq 9.0.1).  Files in this directory:

* `b1a.c`: the C code (sglib's doubly linked list: `sglib_dllist_add`,
  `sglib_dllist_it_init_on_equal`, `sglib_dllist_it_init`,
  `sglib_dllist_it_next`, a driver `b1`, and `main`).  Do not change it.
* `SPEC.md`: what each function requires and ensures, in English.
* `example/`: a small complete VST proof that is not this benchmark
  (`good.c`, `verif_good.v`: funspecs with malloc/free, `semax_body`
  proofs, `semax_prog`), as a reference for the setup and the style.

## What to produce

One file, `verif_b1a.v`, that

1. defines a representation predicate for the lists of SPEC.md and VST
   funspecs (`DECLARE ... WITH ... PRE ... POST`) for the five functions
   and `main` that say what SPEC.md says (as general as SPEC.md: for
   example `add` accepts any node of a whole list, not only the head;
   the iterator starts at any node; the subcomparator is NULL);
2. proves `semax_body Vprog Gprog f_X X_spec` for each of the six
   functions, each ending in `Qed.`;
3. proves `prog_correct : semax_prog prog tt Vprog Gprog` and ends with
   `Print Assumptions prog_correct.`

No `Axiom`, `Parameter`, `admit` or `Conjecture`.  If you cannot finish
a proof, end it with `Admitted.` so that the file still compiles, and
say which ones are open in your last answer.  Helper lemmas are fine.

## How to run the tools

Your only command is `{tool}`: it runs one command inside the VST image,
with this directory mounted at `/work` (the current directory there).
For example:

    {tool} clightgen -normalize b1a.c
    {tool} coqc -native-compiler no -Q . B1a b1a.v
    {tool} coqc -native-compiler no -Q . B1a verif_b1a.v

(`verif_b1a.v` then starts with `Require Import VST.floyd.proofauto.
Require Import VST.floyd.library. Require Import B1a.b1a.`.)  The
example compiles the same way from `example/` with `-Q . Smoke`
(`{tool} sh -c "cd example && clightgen -normalize good.c && coqc
-native-compiler no -Q . Smoke good.v && coqc -native-compiler no -Q .
Smoke verif_good.v"`).  `-native-compiler no` is required.  Each call
starts a container (a few seconds); `coqc` on a large VST file can take
minutes, so give the Bash call a long timeout.  `coqtop`
works the same way (pipe a script into it to see a goal).  The VST and
Rocq sources are in the image under `/home/rocq/.opam/4.14.2/lib/coq/`
and `/home/rocq/.opam/4.14.2/lib/rocq*/`; you may read them with the
tool (`{tool} grep -rn ... /home/rocq/.opam/4.14.2/lib/coq/user-contrib/VST/floyd`).

## Rules

* Do not read or search anything outside this directory except the VST
  and Rocq installation inside the image (through the tool).  In
  particular do not look for existing proofs of this code.
* Run one command per Bash call (no `&&`, `;`, pipes or newlines outside
  the tool's own argument), and write files with Write or Edit.  Any
  other command is denied; a denial does not end the task.
* You have a budget of about ${usd} for this task.  Work toward a
  complete `verif_b1a.v`; when you are done (or out of budget), answer
  with one line per function: its name and PROVED or OPEN.
"""


def tool_script(run):
    return f"""#!/bin/sh
# Plan Q10: the VST agent's only command.  Runs one command in the VST
# image with {run} (only) mounted at /work, no network.
exec docker run --rm -i --init --network none \\
  --user "$(id -u):$(id -g)" -e HOME=/home/rocq \\
  -v {run}:/work -w /work {IMAGE} bash -lc 'exec "$@"' bash "$@"
"""


def command(run, tool, usd, turns, prompt):
    allowed = [f"Bash({tool} *)", f"Read(/{run}/**)", f"Write(/{run}/**)",
               f"Edit(/{run}/**)"]
    # The existing VST proofs of B1, in this checkout and in the main
    # one (a worktree's parent).  Not the whole repository: the run
    # directory is inside it.  --restricted already confines the file
    # tools to the run directory; these rules are a second fence.
    roots = {REPO, REPO.split("/.claude/worktrees/")[0]}
    denied = ["Bash(git *)", "Bash(git)"] + [
        f"{t}(/{r}/Ariadne/vst/b1/**)" for r in sorted(roots)
        for t in ("Read", "Edit", "Write")]
    # Every other run next to this one (earlier VST runs hold proofs of
    # the same task), and their tool scripts.
    parent = os.path.dirname(run)
    for name in sorted(os.listdir(parent)) if os.path.isdir(parent) else []:
        other = os.path.join(parent, name)
        if other == run or other == run + ".tool":
            continue
        pat = f"/{other}/**" if os.path.isdir(other) else f"/{other}"
        denied += [f"{t}({pat})" for t in ("Read", "Edit", "Write")]
    return ["claude", "-p", prompt, "--model", MODEL,
            "--output-format", "json", "--max-turns", str(turns),
            "--max-budget-usd", str(usd), "--no-session-persistence",
            "--safe-mode", "--restricted", "--strict-mcp-config",
            "--disable-slash-commands", "--tools", "Bash,Read,Write,Edit",
            "--allowedTools", *allowed, "--disallowedTools", *denied,
            "--permission-mode", "dontAsk"]


def setup(run):
    os.makedirs(os.path.join(run, "example"))
    b1a = os.path.join(ARIADNE, "bench", "b1a")
    shutil.copy(os.path.join(b1a, "b1a.c"), run)
    shutil.copy(os.path.join(b1a, "SPEC.md"), run)
    smoke = os.path.join(ARIADNE, "vst", "smoke")
    for f in ("good.c", "verif_good.v", "_CoqProject"):
        shutil.copy(os.path.join(smoke, f), os.path.join(run, "example"))
    tool = run + ".tool"
    open(tool, "w").write(tool_script(run))
    os.chmod(tool, 0o755)
    return tool


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--dry-run", action="store_true")
    ap.add_argument("--run-dir")
    ap.add_argument("--usd", type=float, default=15.0)
    ap.add_argument("--turns", type=int, default=600)
    ap.add_argument("--seconds", type=int, default=4 * 3600)
    ap.add_argument("--ledger", default=budget.PATH,
                    help="the budget ledger the call is reserved in")
    a = ap.parse_args()
    run = os.path.abspath(a.run_dir or os.path.join(
        ARIADNE, "runs", "q10", time.strftime("vst-%Y%m%d-%H%M%S")))
    if os.path.exists(run):
        sys.exit(f"{run} exists")
    tool = setup(run)
    prompt = ("Read TASK.md in this directory and do the task it "
              "describes.\n\n" + TASK.format(tool=tool, usd=a.usd))
    open(os.path.join(run, "TASK.md"), "w").write(
        TASK.format(tool=tool, usd=a.usd))
    cmd = command(run, tool, a.usd, a.turns, prompt)
    env = dict(os.environ, GIT_CEILING_DIRECTORIES=os.path.dirname(run),
               GIT_DIR=os.path.join(run, ".no-git"))
    fence = {"cwd": run, "tool": tool, "tool_script": tool_script(run),
             "command": cmd, "env": {k: env[k] for k in
                                     ("GIT_CEILING_DIRECTORIES", "GIT_DIR")},
             "files": sorted(os.path.relpath(os.path.join(d, f), run)
                             for d, _, fs in os.walk(run) for f in fs)}
    json.dump(fence, open(os.path.join(run, "fence.json"), "w"), indent=1)
    if a.dry_run:
        print(json.dumps(fence, indent=1))
        return
    # As the harness does: the call's cap is reserved in the ledger first,
    # under its weekly cap (--ledger: a calibrated ledger, or one with
    # an explicit cap); a refusal stops here, before any model call.
    ledger = budget.Ledger(a.ledger)
    gate = ledger.reserve("annotator", MODEL, a.usd)
    json.dump(gate, open(os.path.join(run, "budget_gate.json"), "w"),
              indent=1)
    if not gate["ok"]:
        print(json.dumps({"refused": gate}, indent=1))
        sys.exit(f"budget ledger refused the call: "
                 f"{gate['projected_pct']}% would pass the "
                 f"{gate['cap_pct']}% cap")
    t0 = time.time()
    out, end = None, None
    try:
        p = subprocess.run(cmd, cwd=run, env=env, capture_output=True,
                           text=True, timeout=a.seconds,
                           stdin=subprocess.DEVNULL)
        open(os.path.join(run, "result.json"), "w").write(p.stdout)
        if p.stderr:
            open(os.path.join(run, "stderr.txt"), "w").write(p.stderr)
        out = json.loads(p.stdout)
        end = out.get("subtype")
    except subprocess.TimeoutExpired:
        end = "timeout"
    except ValueError:
        end = "no JSON result"
    except BaseException:
        ledger.release(gate["id"])
        raise
    secs = round(time.time() - t0, 1)
    mu = budget.by_model(out, MODEL) if out else {}
    c = ledger.charge("annotator", mu, est_usd=a.usd, model=MODEL,
                      reservation=gate["id"])
    summary = {"end": end, "seconds": secs, "usage": mu,
               "usd": c["usd"], "tokens": c["tokens"],
               "total_cost_usd": out and out.get("total_cost_usd"),
               "num_turns": out and out.get("num_turns"),
               "permission_denials": out and out.get("permission_denials"),
               "answer": out and (out.get("result") or "")[-3000:]}
    json.dump(summary, open(os.path.join(run, "summary.json"), "w"),
              indent=1)
    print(json.dumps({k: v for k, v in summary.items()
                      if k != "permission_denials"}, indent=1))


if __name__ == "__main__":
    main()
