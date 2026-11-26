"""A prover run: one fenced `claude -p` agent proving a target, with a
spend meter it sees, restarts while it stops early, the budget ledger,
and the check at the end.

The run directory (runs/<target>/run-<time>/, git-ignored) holds the
target's frozen files (write-denied), `example/` (VST's smoke proof),
TASK.md, and, with --from, the previous run's proof files.  The agent's
only command is a tool script next to the run directory (<run>.tool,
outside it): one command in the VST image with the run directory (only)
mounted, no network, limited memory and time; after the command it
prints the meter, `[spent so far: about $X of $Y]`.  File tools are
confined to the run directory (--restricted and the allow rules); git,
the benchmarks, other runs and kept proofs are denied.

The meter prices each response's usage from the stream (stream-json
with --include-partial-messages: a response's output tokens arrive in
its message_delta event).  The raw events, without the per-token
deltas, are kept in <run>/stream_N.jsonl.
"""
import glob
import json
import os
import shutil
import subprocess
import sys
import threading
import time

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import check as checker  # noqa: E402
import targets  # noqa: E402

ARIADNE = targets.ARIADNE
REPO = os.path.dirname(ARIADNE)
sys.path.insert(0, os.path.join(ARIADNE, "harness"))
import budget  # noqa: E402

MODEL = "claude-opus-5-5"
IMAGE = os.environ.get("ARIADNE_VST_IMAGE", "ariadne-vst:dev")
# per-command limits for the agent's tool (2026-11-18: a coqc run
# exhausted the host's memory and wedged it)
MEM = os.environ.get("ARIADNE_MEM", "16g")
TIMEOUT = int(os.environ.get("ARIADNE_TIMEOUT", "1800"))
MAX_PRODS = 3        # sessions started again, at most
MIN_LEFT_USD = 3.0   # no new session with less than this left
# Opus 5.5 list prices, $ per million tokens (fitted exactly to the 2026-11
# picol runs' costs; raw input assumed write/2)
PRICES = {"input_tokens": 4.0, "output_tokens": 20.0,
          "cache_read_input_tokens": 0.2, "ephemeral_1h_input_tokens": 8.0,
          "ephemeral_5m_input_tokens": 5.0}

COMMON = """
## How to run the tools

Your only command is `{tool}`: it runs one command inside the VST image,
with this directory mounted at `/work` (the current directory there):

{compile}

`-native-compiler no` is required.  Each call starts a container; give
the Bash call a long timeout.  `coqtop` works the same way (pipe a
script into it).  The VST and Rocq sources are in the image under
`/home/rocq/.opam/4.14.2/lib/coq/user-contrib/VST` and
`/home/rocq/.opam/4.14.2/lib/rocq*/`; read them with the tool.
`example/` is a small complete VST proof (`good.c`, `verif_good.v`).

## Rules

* Do not read or search anything outside this directory except the VST
  and Rocq installation inside the image (through the tool).  Do not
  look for existing proofs of this code.
* Do not change the files given to you (they are write-protected and
  compared with the originals by the check).
* No `Axiom`, `Parameter`, `admit`, `Conjecture`, or `Hypothesis` /
  `Variable` outside a `Section`.  If you cannot finish a proof, end it
  with `Admitted.` so that the files still compile, and say which ones
  are open in your last answer.
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
* If you choose a spec for one of the program's own functions that
  rests on an assumption about its inputs (a size bound, which
  functions a pointer may hold), say so in your last answer; no one
  needs to approve it.
* When you are done, answer with one line per goal: its name and PROVED
  or OPEN.
"""

PROD = """\
Read TASK.md in this directory and continue the task it describes.  An
earlier session stopped with about ${spent:.2f} of ${usd:.2f} spent, but
the proof is not finished: `{check}` (the check's result) lists the
open goals, and `last_answer.md` is that session's final answer.  Do
not stop to save budget: keep going until everything is proved or the
run is stopped.

"""


def tool_script(run):
    return f"""#!/bin/sh
# The prover's only command (ariadne/session.py): one command in the VST
# image with {run} (only) mounted at /work, no network, {MEM} of memory
# (no extra swap) and {TIMEOUT} s; then the spend meter.
docker run --rm -i --init --network none \\
  --memory {MEM} --memory-swap {MEM} --pids-limit 1024 \\
  --user "$(id -u):$(id -g)" -e HOME=/home/rocq \\
  -v {run}:/work -w /work {IMAGE} timeout -s KILL {TIMEOUT} \\
  bash -lc 'exec "$@"' bash "$@"
rc=$?
cat "{run}.spend" 2>/dev/null
exit $rc
"""


def command(run, tool, usd, turns, prompt, frozen):
    allowed = [f"Bash({tool} *)", f"Read(/{run}/**)", f"Write(/{run}/**)",
               f"Edit(/{run}/**)"]
    roots = {REPO, REPO.split("/.claude/worktrees/")[0]}
    denied = ["Bash(git *)", "Bash(git)"]
    for r in sorted(roots):
        for d in ("Ariadne/bench", "Ariadne/libc", "Ariadne/vst",
                  "Ariadne/q10"):
            denied += [f"{t}(/{r}/{d}/**)" for t in ("Read", "Edit", "Write")]
    parent = os.path.dirname(run)
    for name in sorted(os.listdir(parent)) if os.path.isdir(parent) else []:
        other = os.path.join(parent, name)
        if other.startswith(run):     # the run, its tool, meter, stderr
            continue
        pat = f"/{other}/**" if os.path.isdir(other) else f"/{other}"
        denied += [f"{t}({pat})" for t in ("Read", "Edit", "Write")]
    denied += [f"{t}(/{run}/{f})" for f in frozen for t in ("Edit", "Write")]
    return ["claude", "-p", prompt, "--model", MODEL,
            "--output-format", "stream-json", "--verbose",
            "--include-partial-messages", "--max-turns", str(turns),
            "--max-budget-usd", "%.2f" % usd, "--no-session-persistence",
            "--safe-mode", "--restricted", "--strict-mcp-config",
            "--disable-slash-commands", "--tools", "Bash,Read,Write,Edit",
            "--allowedTools", *allowed, "--disallowedTools", *denied,
            "--permission-mode", "dontAsk"]


def usage_usd(u):
    """The cost of one response's usage."""
    cc = u.get("cache_creation") or {}
    w1h = cc.get("ephemeral_1h_input_tokens")
    w5m = cc.get("ephemeral_5m_input_tokens", 0)
    if w1h is None:  # no breakdown: count every cache write as 1h
        w1h, w5m = u.get("cache_creation_input_tokens") or 0, 0
    n = dict(u, ephemeral_1h_input_tokens=w1h, ephemeral_5m_input_tokens=w5m)
    return sum(int(n.get(k) or 0) * p for k, p in PRICES.items()) / 1e6


def run_session(cmd, run, n, env, meter, before, cap, seconds):
    """One session.  Returns (the result event or None, the end reason)."""
    usage, current = {}, None
    out, end = None, "no JSON result"
    keep = open(os.path.join(run, "stream_%d.jsonl" % n), "w")
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
                t, e = ev.get("type"), ev.get("event") or {}
                if t == "stream_event" and e.get("type") not in (
                        "message_start", "message_delta"):
                    continue
                keep.write(line)
                if t == "stream_event" and e["type"] == "message_start":
                    m = e.get("message") or {}
                    current = m.get("id")
                    if current:
                        usage[current] = dict(m.get("usage") or {})
                elif t == "stream_event" and current:
                    u = e.get("usage") or {}
                    if u.get("output_tokens") is not None:
                        usage[current]["output_tokens"] = u["output_tokens"]
                elif t == "assistant":
                    m = ev.get("message") or {}
                    if m.get("id") and m.get("usage") and m["id"] not in usage:
                        usage[m["id"]] = dict(m["usage"])
                elif t == "result":
                    out, end = ev, ev.get("subtype")
                spent = before + sum(map(usage_usd, usage.values()))
                open(meter, "w").write(
                    "[spent so far: about $%.2f of $%.2f]\n" % (spent, cap))
            p.wait()
        finally:
            timer.cancel()
            keep.close()
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


def compile_lines(t, tool, files):
    c = t["c"]
    lines = ["    %s clightgen -normalize %s" % (tool, c),
             "    %s coqc -native-compiler no -Q . %s %s.v" % (tool, t["lib"],
                                                              c[:-2])]
    lines += ["    %s coqc -native-compiler no -Q . %s %s" % (tool, t["lib"], f)
              for f in files + [t["proof"]]]
    return "\n".join(lines)


def setup(t, run, previous=None):
    os.makedirs(run)
    frozen = targets.frozen_files(t)
    for name, text in frozen.items():
        os.makedirs(os.path.dirname(os.path.join(run, name)), exist_ok=True)
        open(os.path.join(run, name), "w").write(text)
    dirs = dict({"example": ["vst/smoke/good.c", "vst/smoke/verif_good.v",
                             "vst/smoke/_CoqProject"]}, **t.get("dirs", {}))
    for name, pats in dirs.items():
        os.makedirs(os.path.join(run, name))
        for pat in pats:
            for f in sorted(glob.glob(os.path.join(ARIADNE, pat))):
                shutil.copy(f, os.path.join(run, name))
    if previous:
        for f in checker.proof_list(t, previous) + [
                f for f in os.listdir(previous)
                if f == "proof_files.txt" or f.endswith("_draft.txt")]:
            if os.path.exists(os.path.join(previous, f)):
                shutil.copy(os.path.join(previous, f), run)
        s = os.path.join(previous, "summary.json")
        if os.path.exists(s):
            open(os.path.join(run, "previous_answer.md"), "w").write(
                (json.load(open(s)).get("answer") or "") + "\n")
    tool = run + ".tool"
    open(tool, "w").write(tool_script(run))
    os.chmod(tool, 0o755)
    return tool, sorted(frozen)


def task_text(t, tool, usd, note):
    body = targets._fill(open(os.path.join(ARIADNE, t["task"])).read(),
                         {k: v for k, v in t.items() if isinstance(v, str)})
    files = [f for f in targets.checked_files(t) if f.endswith(".v")]
    common = COMMON.replace("{usd:.2f}", "%.2f" % usd).replace(
        "{compile}", compile_lines(t, tool, files)).replace("{tool}", tool)
    return body.replace("{tool}", tool) + (note or "") + common


def run(name, usd=None, previous=None, note=None, turns=2000,
        seconds=10 * 3600, ledger_path=budget.PATH, dry_run=False):
    t = targets.load(name)
    usd = usd or t["cap_usd"]
    run = os.path.join(ARIADNE, "runs", name.replace("/", "_"),
                       time.strftime("run-%Y%m%d-%H%M%S"))
    previous = previous and os.path.abspath(previous)
    tool, frozen = setup(t, run, previous)
    text = task_text(t, tool, usd, note)
    open(os.path.join(run, "TASK.md"), "w").write(text)
    prompt = "Read TASK.md in this directory and do the task it describes.\n\n"
    cmd = command(run, tool, usd, turns, prompt + text, frozen)
    env = dict(os.environ, GIT_CEILING_DIRECTORIES=os.path.dirname(run),
               GIT_DIR=os.path.join(run, ".no-git"))
    fence = {"target": name, "cwd": run, "tool": tool,
             "tool_script": tool_script(run), "command": cmd,
             "files": sorted(os.path.relpath(os.path.join(d, f), run)
                             for d, _, fs in os.walk(run) for f in fs)}
    json.dump(fence, open(os.path.join(run, "fence.json"), "w"), indent=1)
    if dry_run:
        return {"run": run, "fence": {k: v for k, v in fence.items()
                                      if k != "command"}}
    ledger = budget.Ledger(ledger_path)
    gate = ledger.reserve("prover", MODEL, usd)
    json.dump(gate, open(os.path.join(run, "budget_gate.json"), "w"), indent=1)
    if not gate["ok"]:
        return {"run": run, "refused": gate}
    t0, spent, mu, sessions, s, answer = time.time(), 0.0, {}, [], None, ""
    meter = run + ".spend"
    try:
        while True:
            left_s = seconds - (time.time() - t0)
            out, end = run_session(cmd, run, len(sessions) + 1, env, meter,
                                   spent, usd, left_s)
            cost = out and out.get("total_cost_usd")
            sessions.append({"end": end, "usd": cost,
                             "meter": open(meter).read().strip()
                             if os.path.exists(meter) else None,
                             "num_turns": out and out.get("num_turns")})
            if out:
                merge_usage(mu, budget.by_model(out, MODEL))
                spent += cost or 0
                answer = out.get("result") or ""
            s = checker.check(name, run)
            left = usd - spent
            if (s["verdict"] == "PROVED" or end != "success" or out is None
                    or left < MIN_LEFT_USD or len(sessions) > MAX_PRODS
                    or seconds - (time.time() - t0) < 600):
                break
            open(os.path.join(run, "last_answer.md"), "w").write(answer + "\n")
            cmd = command(run, tool, left, turns,
                          PROD.format(spent=spent, usd=usd,
                                      check="check_%s.json" % name) + text, frozen)
    except BaseException:
        if not sessions:
            ledger.release(gate["id"])
        raise
    c = ledger.charge("prover", mu, est_usd=usd, model=MODEL,
                      reservation=gate["id"])
    summary = {"target": name, "end": sessions[-1]["end"],
               "seconds": round(time.time() - t0, 1), "usd": c["usd"],
               "total_cost_usd": round(spent, 6), "sessions": sessions,
               "answer": answer[-4000:], "check": s}
    json.dump(summary, open(os.path.join(run, "summary.json"), "w"), indent=1)
    return summary
