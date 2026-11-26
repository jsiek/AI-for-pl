#!/usr/bin/env python3
"""Plan M8: one prover run that proves picol (picol_vst.c) memory safe and
leak free with VST: semax_prog for the whole program, every internal
funspec chosen by the agent, against the frozen spec_picol.v.

    python3 run_picol.py --dry-run          # set up a run directory, call nothing
    python3 run_picol.py --usd 50           # the paid run, then the check
    python3 run_picol.py --check RUN_DIR    # re-check a run
    python3 run_picol.py --usd 50 --from RUN_DIR   # continue from a run

The run directory (../../runs/picol/run-<time>/, git-ignored) holds
  picol_full.c   picol_vst.c preprocessed into one file (as clightgen
                 does): picol, musl's stdio globals and libc sources, and
                 the main(void) wrapper;
  picol.c, picol_vst.c   the readable sources (with comments);
  spec_picol.v   the frozen specs (trusted, musl, picol_main, main);
  libc_proofs/   the musl proofs (../../libc/proofs/), reusable as is;
  example/       VST's smoke test (../../vst/smoke);
  TASK.md.
The sandbox, permission fence and budget ledger are q10/run_vst.py's.

check() recompiles from pristine picol_full.c and spec_picol.v and the
run's proof files only, and requires: `prog_correct : semax_prog prog tt
Vprog Gprog` with spec_picol's Vprog; each frozen spec in Gprog
(find_id); no Admitted/admit/Axiom/Parameter/Conjecture in the proof
files; Print Assumptions of prog_correct within
../../vst/smoke/expected_assumptions.txt plus the approved trusted items
(FILE_handle and its two facts, the trusted body axioms, VST's
body_exit and malloc_token_valid_pointer); the leak lint (../sglib_vst/lint/post_lint.py) on every
funspec of spec_picol and the proof files.
"""
import argparse
import json
import os
import re
import shutil
import subprocess
import sys
import threading
import time

HERE = os.path.dirname(os.path.abspath(__file__))
ARIADNE = os.path.dirname(os.path.dirname(HERE))
RUN = os.path.join(ARIADNE, "vst", "run.sh")
EXPECTED = os.path.join(ARIADNE, "vst", "smoke", "expected_assumptions.txt")
LINT = os.path.join(ARIADNE, "bench", "sglib_vst", "lint")
sys.path.insert(0, os.path.join(ARIADNE, "q10"))
sys.path.insert(0, os.path.join(ARIADNE, "harness"))
import budget  # noqa: E402
import run_vst  # noqa: E402

M = "libc/musl-1.2.6"
INC = ["-I%s/%s" % (M, p) for p in ("obj/shim", "arch/x86_64", "arch/generic",
                                    "obj/include", "include")]
COQC = ["coqc", "-native-compiler", "no", "-Q", ".", "Picol"]
FORBIDDEN = r"\b(Admitted|admit|Axiom|Parameter|Conjecture)\b"
FROZEN = ["realloc", "fmt_double", "strtod", "fopen", "fclose", "fputs",
          "fflush", "fgets", "fread", "perror", "strlen", "strcmp", "strchr",
          "memcpy", "isupper", "picol_main", "main"]
# malloc_token_valid_pointer: VST's allocator model (floyd/library.v),
# approved by the owner 2026-11-23.
TRUSTED_AXIOMS = {"FILE_handle", "FILE_handle_valid", "FILE_handle_ptr",
                  "body_exit", "malloc_token_valid_pointer"} | {
                      "body_" + f for f in FROZEN[:10]}


def source():
    """picol_vst.c preprocessed into one C file."""
    r = subprocess.run([RUN, "clightgen", "-E", "-Wp,-nostdinc,-P",
                        "-D_XOPEN_SOURCE=700"] + INC
                       + ["bench/picol/picol_vst.c"],
                       cwd=ARIADNE, capture_output=True, text=True)
    if r.returncode:
        sys.exit("preprocessing failed: " + r.stderr[-800:])
    body = "\n".join(l for l in r.stdout.splitlines() if l.strip())
    return ("/* bench/picol/picol_vst.c preprocessed with CompCert's defines"
            " and musl 1.2.6's\n * headers (run_picol.py).  Do not edit. */\n"
            + body + "\n")


def functions(c_ast):
    return re.findall(r"Definition f_(\w+) :=", c_ast)


TASK = """\
# Task: VST proof of memory safety and leak freedom for picol

You are verifying a complete C program with VST (Verifiable C 2.17,
CompCert 3.18 clightgen, Rocq 9.0.1): picol, a small Tcl interpreter.
Files in this directory:

* `picol_full.c`: the program to verify, one self-contained file: picol
  (`picol.c`, with `main` renamed `picol_main`), musl libc's definitions
  of `stdin`/`stdout`/`stderr`, musl's `strlen`, `__strchrnul`,
  `strchr`, `strcmp`, `memcpy`, `isupper`, `__isupper_l`, and a
  `main(void)` that calls `picol_main` in REPL mode and in script mode.
  Do not change it.  `picol.c` and `picol_vst.c` are the readable
  sources (with comments); `picol_full.c` is what is verified.
* `spec_picol.v`: `CompSpecs`, `Vprog`, and frozen funspecs: the
  external functions (`realloc`, `fmt_double`, `strtod`, `fopen`,
  `fclose`, `fputs`, `fflush`, `fgets`, `fread`, `perror`, each with an
  axiom `body_X`; `exit` is VST's library spec, `body_exit`), the musl
  functions, `picol_main_spec` and `main_spec`.  Do not change it.
* `libc_proofs/`: VST proofs of the musl functions against these specs
  for a program containing only them; they replay unchanged against
  `picol_full.c` (drop their `Require Import Libc...` line).
* `example/`: a small complete VST proof (`good.c`, `verif_good.v`).

## What to produce

`verif_picol.v` (you may split the work over more files; then list all
your .v files, in compilation order, one per line, in `proof_files.txt`,
ending with `verif_picol.v`) that

1. starts with `Require Import VST.floyd.proofauto. Require Import
   VST.floyd.library. Require Import Picol.picol_full Picol.spec_picol.
   #[export] Existing Instance NullExtension.Espec.` and uses `CompSpecs`, `Vprog` and the funspecs of `spec_picol.v`
   (do not redefine them);
2. defines a funspec for every other function of `picol_full.c`
   ({internal}): your choice, whatever the proofs need;
3. defines `Gprog : funspecs` (e.g. `ltac:(with_library prog [...])`),
   once, in any of your files, containing every frozen funspec of
   `spec_picol.v` and yours;
4. proves `semax_body Vprog Gprog f_X X_spec` for every function, and
5. proves `Lemma prog_correct : semax_prog prog tt Vprog Gprog.`
   (`prove_semax_prog`, then `semax_func_cons body_X` for each function
   in the order of `prog`'s definitions, the external ones with the
   `body_X` axioms of `spec_picol.v` and VST's `body_exit`).

**Leak freedom.**  No postcondition of yours may contain `TT`, an
existential over `mpred`, or `!! P` outside a conjunction: a function
must give back exactly the memory it owns.  (The check lints every
funspec.)  No `Axiom`, `Parameter`, `admit` or `Conjecture`.  If you
cannot finish a proof, end it with `Admitted.` so that the files still
compile, and say which ones are open in your last answer.

## Notes

* picol calls its commands through function pointers
  (`c->func(i,argc,argv,c)`); VST handles calls through function
  pointers with `func_ptr'` (see VST's `progs64/verif_funcptr.v` and
  `progs64/verif_object.v` in the image).
* String literals are global variables; `main_pre` (and
  `globvars2pred gv (prog_vars prog)` in `picol_main_spec`) holds them
  (see `expand_main_pre` in VST).
* For an external function, `semax_func_cons body_X` may leave a goal
  that the return value is well typed; it follows from the frozen
  postcondition (e.g. `fopen`'s result is NULL or, by
  `FILE_handle_ptr`, a pointer; `realloc`'s is NULL or holds a
  `data_at`).  `eapply semax_func_cons_ext` shows the goals.
* Compiling a large proof file takes a while: split into several files
  if that helps you iterate.  Checking `prog_correct` needs about 6.5 GB
  of memory: run one such build at a time.
{previous}
## How to run the tools

Your only command is `{tool}`: it runs one command inside the VST image,
with this directory mounted at `/work` (the current directory there):

    {tool} clightgen -normalize picol_full.c
    {tool} coqc -native-compiler no -Q . Picol picol_full.v
    {tool} coqc -native-compiler no -Q . Picol spec_picol.v
    {tool} coqc -native-compiler no -Q . Picol verif_picol.v

`-native-compiler no` is required.  Each call starts a container; give
the Bash call a long timeout.  `coqtop` works the same way (pipe a
script into it).  The VST and Rocq sources are in the image under
`/home/rocq/.opam/4.14.2/lib/coq/user-contrib/VST` and
`/home/rocq/.opam/4.14.2/lib/rocq*/`; read them with the tool.

## Rules

* Do not read or search anything outside this directory except the VST
  and Rocq installation inside the image (through the tool).
* Run one command per Bash call (no `&&`, `;`, pipes or newlines outside
  the tool's own argument), and write files with Write or Edit.  Any
  other command is denied; a denial does not end the task.
* **Budget.**  The run is stopped automatically when it has spent
  ${usd:.2f}.  After each call, the tool prints the spend so far, e.g.
  `[spent so far: about $31.40 of ${usd:.2f}]`.  Do not stop early to save
  budget: keep working until everything is proved or the run is
  stopped.  Keep every file listed in `proof_files.txt` compiling at all
  times (develop an unfinished proof in a file not listed there, or end
  it with `Admitted.`), so that a stop loses nothing.
* When you are done, answer with one line per function: its name and
  PROVED or OPEN, then `prog_correct` PROVED or OPEN.
"""

# Prompt for a session started again after the agent stopped with the
# proof unfinished and budget left (the owner, 2026-11-25: "prod it to
# keep going").
MAX_PRODS = 3        # sessions started again, at most
MIN_LEFT_USD = 3.0   # no new session with less than this left
PROD = """\
Read TASK.md in this directory and continue the task it describes.  An
earlier session stopped with about ${spent:.2f} of ${usd:.2f} spent, but
the proof is not finished: `check.json` (the check's result) lists the
open lemmas, and `last_answer.md` is that session's final answer.  Do
not stop to save budget: keep going until everything is proved or the
run is stopped.

"""

# Opus 5.5 list prices, $ per million tokens (fitted exactly to the three
# 2026-11 picol runs' costs; raw input assumed write/2).
PRICES = {"input_tokens": 4.0, "output_tokens": 20.0,
          "cache_read_input_tokens": 0.2, "ephemeral_1h_input_tokens": 8.0,
          "ephemeral_5m_input_tokens": 5.0}


def usage_usd(u):
    """The cost of one response's usage (a stream-json `message.usage`)."""
    cc = u.get("cache_creation") or {}
    w1h = cc.get("ephemeral_1h_input_tokens")
    w5m = cc.get("ephemeral_5m_input_tokens", 0)
    if w1h is None:  # no breakdown: count every cache write as 1h
        w1h, w5m = u.get("cache_creation_input_tokens") or 0, 0
    n = dict(u, ephemeral_1h_input_tokens=w1h, ephemeral_5m_input_tokens=w5m)
    return sum(int(n.get(k) or 0) * p for k, p in PRICES.items()) / 1e6


def run_session(cmd, run, env, meter, before, cap, seconds):
    """One `claude -p` session with stream-json output.  After each
    response, writes the estimated spend (`before` plus this session's)
    to `meter`, which the tool prints after each call.  Returns the
    final result event (None if there is none) and the end reason."""
    usage = {}
    out, end = None, "no JSON result"
    with open(run + ".stderr", "a") as err:
        p = subprocess.Popen(cmd, cwd=run, env=env, stdin=subprocess.DEVNULL,
                             stdout=subprocess.PIPE, stderr=err, text=True)
        timer = threading.Timer(seconds, p.kill)
        timer.start()
        try:
            for line in p.stdout:
                try:
                    ev = json.loads(line)
                except ValueError:
                    continue
                if ev.get("type") == "assistant":
                    m = ev.get("message") or {}
                    if m.get("id") and m.get("usage"):
                        usage[m["id"]] = m["usage"]
                        spent = before + sum(map(usage_usd, usage.values()))
                        open(meter, "w").write(
                            "[spent so far: about $%.2f of $%.2f]\n" % (spent, cap))
                elif ev.get("type") == "result":
                    out, end = ev, ev.get("subtype")
            p.wait()
        finally:
            timer.cancel()
    if out is None and p.returncode == -9:
        end = "timeout"
    return out, end


def merge_usage(total, mu):
    for m, u in mu.items():
        t = total.setdefault(m, {})
        for k, v in u.items():
            if isinstance(v, (int, float)) and not isinstance(v, bool):
                t[k] = t.get(k, 0) + v
    return total

PREVIOUS = """
## Continuing a previous run

Previous runs left their proof files here (listed in `proof_files.txt`),
and the last run's final answer in `previous_answer.md`: 44 functions
and `prog_correct` proved; open (`Admitted`, in `verif_open.v`):
`picolEval` and `picolExpr`.  **Prove only these two.**  The other
proofs are done: change them only if a spec change forces it, and do
not rebuild files you have not changed more often than needed.

* **`picolEval`:** the last run built the argument-buffer lemmas
  (`verif_evalutil.v`) and the loop invariant, and proved the steps up
  to reading the token; its draft is `picolEval_draft.txt`.  Left: the
  unescape loop, appending to the last argument, the call through the
  command's function pointer, freeing the arguments.
* **`picolExpr`:** since the last run, its operator `switch` ends with
  `default: break;` (fix 7; unreached), so the proof need not show that
  `op` is one of the cases.  No other function changed.
* **Tidy up:** `verif_callproc.v` line 339 has an `all: admit.` that
  applies to no goal; remove it (the check rejects the word).

The owner approved the spec choices of the earlier runs (the `int`
bounds, the function pointers of the commands); keep them.
"""


def setup(run, previous=None):
    os.makedirs(os.path.join(run, "example"))
    os.makedirs(os.path.join(run, "libc_proofs"))
    open(os.path.join(run, "picol_full.c"), "w").write(source())
    for f in ("picol.c", "picol_vst.c", "spec_picol.v"):
        shutil.copy(os.path.join(HERE, f), run)
    proofs = os.path.join(ARIADNE, "libc", "proofs")
    for f in sorted(os.listdir(proofs)):
        if f.endswith(".v"):
            shutil.copy(os.path.join(proofs, f), os.path.join(run, "libc_proofs"))
    smoke = os.path.join(ARIADNE, "vst", "smoke")
    for f in ("good.c", "verif_good.v", "_CoqProject"):
        shutil.copy(os.path.join(smoke, f), os.path.join(run, "example"))
    if previous:
        drafts = [f for f in os.listdir(previous) if f.endswith("_draft.txt")]
        for f in proof_files(previous) + ["proof_files.txt"] + drafts:
            shutil.copy(os.path.join(previous, f), run)
        answer = json.load(open(os.path.join(previous, "summary.json")))["answer"]
        open(os.path.join(run, "previous_answer.md"), "w").write(answer + "\n")
    # The tool prints the spend meter (outside the run directory, so the
    # agent cannot write it) after the command's own output.
    tool = run + ".tool"
    script = run_vst.tool_script(run).replace("exec docker run", "docker run", 1)
    script += 'rc=$?\ncat "%s" 2>/dev/null\nexit $rc\n' % (run + ".spend")
    open(tool, "w").write(script)
    os.chmod(tool, 0o755)
    return tool


def sh(work, cmd, log):
    with open(os.path.join(work, log), "w") as f:
        return subprocess.run([RUN] + cmd, cwd=work, stdout=f,
                              stderr=subprocess.STDOUT).returncode


def axiom_names(text):
    names = re.findall(r"^([\w.']+) :", text, re.M)
    return {re.sub(r"^(Picol\.)?spec_picol\.", "", n) for n in names}


def proof_files(run):
    p = os.path.join(run, "proof_files.txt")
    if os.path.exists(p):
        return [l.strip() for l in open(p) if l.strip()]
    return ["verif_picol.v"]


def check(run):
    run = os.path.abspath(run)
    work = os.path.join(run, "check")
    shutil.rmtree(work, ignore_errors=True)
    os.makedirs(os.path.join(work, "lint"))
    files = proof_files(run)
    s = {"proof_files": files, "violations": []}
    bad = [f for f in files if not re.fullmatch(r"[\w]+\.v", f)
           or f in ("picol_full.v", "spec_picol.v")
           or not os.path.exists(os.path.join(run, f))]
    if bad or files[-1] != "verif_picol.v":
        s["violations"].append("proof_files.txt: bad or missing %s" % bad)
        return finish(run, s)
    open(os.path.join(work, "picol_full.c"), "w").write(source())
    shutil.copy(os.path.join(HERE, "spec_picol.v"), work)
    shutil.copy(os.path.join(LINT, "PostLint.v"), os.path.join(work, "lint"))
    s["forbidden"], s["lemmas"] = [], {}
    for f in files:
        shutil.copy(os.path.join(run, f), work)
        text = open(os.path.join(run, f)).read()
        s["forbidden"] += ["%s:%d: %s" % (f, i, l.strip())
                           for i, l in enumerate(text.split("\n"), 1)
                           if re.search(FORBIDDEN, l)
                           and not l.strip().startswith("(*")]
        for m in re.finditer(r"Lemma\s+(body_\w+|prog_correct)\b", text):
            end = re.search(r"\b(Qed|Admitted|Defined|Abort)\.", text[m.end():])
            s["lemmas"][m.group(1)] = end.group(1) if end else "(none)"
    if s["forbidden"]:
        s["violations"].append("forbidden keywords (%d)" % len(s["forbidden"]))
    steps = [("clightgen", ["clightgen", "-normalize", "picol_full.c"]),
             ("ast", COQC + ["picol_full.v"]), ("spec", COQC + ["spec_picol.v"])]
    steps += [(f, COQC + [f]) for f in files]
    c = {}
    for name, cmd in steps:
        c[name] = sh(work, cmd, name + ".log")
        if c[name]:
            s["error"] = open(os.path.join(work, name + ".log")).read()[-1500:]
            s["violations"].append("does not compile: %s" % name)
            s["compile"] = c
            return finish(run, s)
    s["compile"] = c
    s["functions"] = functions(open(os.path.join(work, "picol_full.v")).read())
    # Gprog may be defined in any proof file: the statement pins it to the
    # one prog_correct is about.
    v, sp, p = "Picol.verif_picol.", "Picol.spec_picol.", "Picol.picol_full."
    lines = ["Require Import VST.floyd.proofauto.",
             "Require Import VST.floyd.library.",
             "Require Import Picol.picol_full Picol.spec_picol %s."
             % " ".join("Picol." + f[:-2] for f in files),
             "#[local] Existing Instance NullExtension.Espec.",
             "Definition stmt : semax_prog %sprog tt %sVprog Gprog := "
             "%sprog_correct." % (p, sp, v)]
    lines += ["Goal VST.veric.initial_world.find_id %s_%s Gprog = "
              "Some (snd %s%s_spec). Proof. reflexivity. Qed." % (p, f, sp, f)
              for f in FROZEN]
    lines += ["Print Assumptions %sprog_correct." % v]
    open(os.path.join(work, "check_picol.v"), "w").write("\n".join(lines) + "\n")
    rc = sh(work, COQC + ["check_picol.v"], "check.log")
    log = open(os.path.join(work, "check.log")).read()
    if rc:
        s["violations"].append("prog_correct missing or not the statement, "
                               "or a frozen spec missing from Gprog")
        s["error"] = log[-1500:]
        return finish(run, s)
    got = axiom_names(log)
    allowed = axiom_names(open(EXPECTED).read()) | TRUSTED_AXIOMS
    s["assumptions"] = sorted(got)
    s["unexpected_assumptions"] = sorted(got - allowed)
    if s["unexpected_assumptions"]:
        s["violations"].append("assumptions outside the allow-list: %s"
                               % s["unexpected_assumptions"])
    mods = ["Picol.spec_picol"] + ["Picol." + f[:-2] for f in files]
    pl = subprocess.run(["python3", "-I", os.path.join(LINT, "post_lint.py"),
                         "--root", work, "--lib", "Picol"] + mods,
                        capture_output=True, text=True)
    s["post_lint"] = {"rc": pl.returncode, "out": pl.stdout[-3000:]}
    if pl.returncode:
        s["violations"].append("post_lint failed (leak freedom)")
    return finish(run, s)


def finish(run, s):
    s["verdict"] = "PROVED" if not s["violations"] else "NOT PROVED"
    json.dump(s, open(os.path.join(run, "check.json"), "w"), indent=1)
    return s


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--check", metavar="RUN_DIR")
    ap.add_argument("--dry-run", action="store_true")
    ap.add_argument("--from", dest="from_run", metavar="RUN_DIR",
                    help="start from that run's proof files")
    ap.add_argument("--usd", type=float, default=50.0)
    ap.add_argument("--turns", type=int, default=2000)
    ap.add_argument("--seconds", type=int, default=10 * 3600)
    ap.add_argument("--ledger", default=budget.PATH)
    a = ap.parse_args()
    if a.check:
        print(json.dumps(check(a.check), indent=1))
        return
    run = os.path.join(ARIADNE, "runs", "picol", time.strftime("run-%Y%m%d-%H%M%S"))
    previous = a.from_run and os.path.abspath(a.from_run)
    tool = setup(run, previous)
    subprocess.run([RUN, "clightgen", "-normalize", "picol_full.c"], cwd=run,
                   capture_output=True)
    ast = open(os.path.join(run, "picol_full.v")).read()
    for f in ("picol_full.v",):
        os.remove(os.path.join(run, f))
    frozen = set(FROZEN)
    internal = [f for f in functions(ast) if f not in frozen]
    text = TASK.format(tool=tool, usd=a.usd, previous=PREVIOUS if previous else "",
                       internal=", ".join("`%s`" % f for f in internal))
    open(os.path.join(run, "TASK.md"), "w").write(text)
    prompt = ("Read TASK.md in this directory and do the task it "
              "describes.\n\n" + text)
    def agent_cmd(prompt, usd):
        c = run_vst.command(run, tool, round(usd, 2), a.turns, prompt, "picol")
        c[c.index("--output-format") + 1] = "stream-json"
        return c + ["--verbose"]

    cmd = agent_cmd(prompt, a.usd)
    env = dict(os.environ, GIT_CEILING_DIRECTORIES=os.path.dirname(run),
               GIT_DIR=os.path.join(run, ".no-git"))
    fence = {"cwd": run, "tool": tool, "command": cmd,
             "files": sorted(os.path.relpath(os.path.join(d, f), run)
                             for d, _, fs in os.walk(run) for f in fs)}
    json.dump(fence, open(os.path.join(run, "fence.json"), "w"), indent=1)
    if a.dry_run:
        print(json.dumps({k: v for k, v in fence.items() if k != "command"},
                         indent=1))
        print("internal functions (%d): %s" % (len(internal), internal))
        return
    ledger = budget.Ledger(a.ledger)
    gate = ledger.reserve("annotator", run_vst.MODEL, a.usd)
    json.dump(gate, open(os.path.join(run, "budget_gate.json"), "w"), indent=1)
    if not gate["ok"]:
        sys.exit("budget ledger refused the call: %s" % json.dumps(gate))
    # Sessions: the first with the task; then, while the agent stops by
    # itself with the proof unfinished and money left, another with PROD.
    t0, spent, mu, sessions, s = time.time(), 0.0, {}, [], None
    meter = run + ".spend"
    try:
        while True:
            left_s = a.seconds - (time.time() - t0)
            out, end = run_session(cmd, run, env, meter, spent, a.usd, left_s)
            n = len(sessions) + 1
            json.dump(out, open(os.path.join(run, "result_%d.json" % n), "w"))
            cost = out and out.get("total_cost_usd")
            sessions.append({"end": end, "usd": cost,
                             "estimate": open(meter).read().strip()
                             if os.path.exists(meter) else None,
                             "num_turns": out and out.get("num_turns")})
            if out:
                merge_usage(mu, budget.by_model(out, run_vst.MODEL))
                spent += cost or 0
            answer = out and (out.get("result") or "")
            s = check(run)
            left = a.usd - spent
            if (s["verdict"] == "PROVED" or end != "success" or out is None
                    or left < MIN_LEFT_USD or len(sessions) > MAX_PRODS
                    or a.seconds - (time.time() - t0) < 600):
                break
            open(os.path.join(run, "last_answer.md"), "w").write((answer or "") + "\n")
            cmd = agent_cmd(PROD.format(spent=spent, usd=a.usd) + text, left)
    except BaseException:
        if not sessions:
            ledger.release(gate["id"])
        raise
    c = ledger.charge("annotator", mu, est_usd=a.usd, model=run_vst.MODEL,
                      reservation=gate["id"])
    summary = {"end": sessions[-1]["end"], "seconds": round(time.time() - t0, 1),
               "usd": c["usd"], "total_cost_usd": round(spent, 6),
               "sessions": sessions,
               "answer": (answer or "")[-4000:]}
    summary["check"] = s
    json.dump(summary, open(os.path.join(run, "summary.json"), "w"), indent=1)
    print(json.dumps({k: v for k, v in summary.items() if k != "check"}, indent=1))
    print("verdict:", summary["check"]["verdict"], summary["check"]["violations"])


if __name__ == "__main__":
    main()
