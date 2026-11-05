#!/usr/bin/env python3
"""The annotator's oracle (plan section 12.2: "the annotator's oracle
re-runs Frama-C/WP"), as the only commands its headless Claude Code may
run:

  annotator_cli.py check SOURCE.c          the guardrails of plan 7.1-7.3a
                                           against the frozen baseline
  annotator_cli.py wp SOURCE.c TARGET      the guardrails, then WP with the
                                           SMT provers (no Coq) on one
                                           function of the selection, or on
                                           `lemmas`; prints the census and
                                           WP's text of every open goal

Frama-C never sees a SOURCE.c the guardrails reject.  Configuration from
the environment (set by annotator.py): ANNOTATOR_BASELINE (the frozen
baseline source), ANNOTATOR_CONFIG (the benchmark's harness config),
ANNOTATOR_SCRATCH (a directory under Ariadne/ for Frama-C's files),
ANNOTATOR_LOG (one JSON line per call), ANNOTATOR_MAX_CALLS (cap on `wp`
calls; past it a call is refused, exit 2), ANNOTATOR_WP_TIMEOUT
(seconds per SMT attempt, default 20).
"""
import json
import os
import re
import shutil
import subprocess
import sys
import tempfile
import time

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import guardrails  # noqa: E402

RUN = guardrails.RUN


def check(cfg, baseline, text, scratch):
    """The guardrails, as (ok, report lines)."""
    log = os.path.join(scratch, "overlay.log")
    v = {"frozen_spec": guardrails.frozen(baseline, text),
         "lint_acsl": guardrails.lint_acsl(baseline, text),
         "lint_ghost": guardrails.lint_ghost(baseline, text)}
    if all(x["ok"] for x in v.values()):  # Frama-C only on a clean file
        v["overlay"] = guardrails.overlay(scratch, baseline, text,
                                          cfg["cpp_args"], log)
    return all(x["ok"] for x in v.values()), v


def explain(v):
    """Guardrail verdicts as short lines for a model."""
    out = []
    for k, x in v.items():
        if x["ok"]:
            out.append(f"{k}: pass")
            continue
        d = {a: b for a, b in x.items() if a != "ok" and b}
        out.append(f"{k}: REJECTED {json.dumps(d)[:600]}")
    hints = {"frozen_spec": "function contracts and predicate/logic/"
             "inductive/axiomatic/type definitions are frozen: restore "
             "them exactly, and add no contract to a function without one",
             "lint_acsl": "no new axiom, axiomatic, admit, logic, "
             "predicate, inductive or type; use lemmas (they are proved)",
             "lint_ghost": "ghost code may only declare and assign ghost "
             "variables (no loops, jumps, returns, calls, __heap)",
             "overlay": "only ACSL comments and ghost code may change; "
             "the C code must stay byte-identical"}
    for k, x in v.items():
        if not x["ok"]:
            out.append(f"  hint: {hints[k]}")
    return out


def goal_blocks(log_text):
    """WP's printed text of each goal it did not prove, by function:
    [(function, header line, text)]."""
    out, fct = [], "(lemma)"
    lines = log_text.splitlines()
    i = 0
    while i < len(lines):
        m = re.match(r"\s+Function (\S+)", lines[i])
        if m:
            fct = m.group(1)
        if lines[i].startswith("Goal "):
            j = i + 1
            while j < len(lines) and not lines[j].startswith("----"):
                j += 1
            body = [x for x in lines[i:j] if x.strip()]
            out.append((fct, lines[i], "\n".join(body)))
            i = j
            continue
        if lines[i].startswith("  Global"):
            fct = "(lemma)"
        i += 1
    return out


def selection(cfg):
    """The functions the config's passes select with -wp-fct."""
    out = set()
    for p in cfg["passes"]:
        o = p["options"]
        if "-wp-fct" in o:
            out |= set(o[o.index("-wp-fct") + 1].split(","))
    return out


def wp(cfg, text, target, scratch, timeout):
    """WP (SMT only) on one target; (census line, open goals, blocks)."""
    known = selection(cfg)
    passes = {p["name"]: p["options"] for p in cfg["passes"]}
    if target == "lemmas":
        opts = passes.get("lemmas", ["-wp-prop=@lemma"])
    elif target in known:
        opts = ["-wp-rte", "-rte-initialized", "@all", "-wp-fct", target]
    else:
        return None, f"unknown target {target}; one of: lemmas, " + \
            ", ".join(sorted(known)), []
    d = tempfile.mkdtemp(dir=scratch, prefix="wp_")
    src = os.path.join(d, cfg["source"])
    open(src, "w").write(text)
    wpo = list(cfg["wp"])
    k = wpo.index("-wp-prover")
    wpo[k + 1] = ",".join(x for x in wpo[k + 1].split(",") if x != "coq")
    k = wpo.index("-wp-timeout")
    wpo[k + 1] = str(timeout)
    cmd = [RUN, "frama-c"] + cfg["frama_c"] + [cfg["source"], "-then",
                                               "-wp"] + wpo + opts + [
        "-wp-status", "-wp-report-json", "/work/report.json"]
    p = subprocess.run(cmd, cwd=d, capture_output=True, text=True)
    log = p.stdout + p.stderr
    open(os.path.join(d, "wp.log"), "w").write(log)
    rep = os.path.join(d, "report.json")
    if not os.path.exists(rep):
        errs = [x for x in log.splitlines()
                if re.search(r"error|Error|warning: .*ignor", x)]
        return None, "Frama-C failed:\n" + "\n".join(errs[-30:] or
                                                     log.splitlines()[-30:]), []
    goals = json.load(open(rep))
    opened = [g for g in goals if g["verdict"] != "valid"]
    line = f"{len(goals) - len(opened)} / {len(goals)} goals proved"
    return line, opened, goal_blocks(log)


def main():
    if len(sys.argv) < 3 or sys.argv[1] not in ("check", "wp") or \
            (sys.argv[1] == "wp" and len(sys.argv) < 4):
        sys.exit(__doc__)
    cmd, path = sys.argv[1], sys.argv[2]
    cfg = json.load(open(os.environ["ANNOTATOR_CONFIG"]))
    baseline = open(os.environ["ANNOTATOR_BASELINE"]).read()
    scratch = os.environ["ANNOTATOR_SCRATCH"]
    logp = os.environ.get("ANNOTATOR_LOG")
    cap = os.environ.get("ANNOTATOR_MAX_CALLS")
    os.makedirs(scratch, exist_ok=True)
    if cmd == "wp" and cap and logp and os.path.exists(logp):
        used = sum(json.loads(x)["cmd"] == "wp" for x in open(logp)
                   if x.strip())
        if used >= int(cap):
            print(f"Budget used up: {cap} wp calls.  Stop now and answer.")
            sys.exit(2)
    t = time.time()
    text = open(path).read()
    ok, v = check(cfg, baseline, text, scratch)
    out = explain(v)
    entry = {"cmd": cmd, "guardrails_ok": ok}
    if cmd == "wp" and ok:
        target = sys.argv[3]
        line, opened, blocks = wp(
            cfg, text, target, scratch,
            int(os.environ.get("ANNOTATOR_WP_TIMEOUT", "20")))
        entry["target"] = target
        if line is None:
            out.append(opened)
            entry["ok"] = False
        else:
            entry.update(ok=not opened, open=len(opened))
            out.append(f"WP on {target}: {line}")
            for g in opened:
                out.append(f"  open: {g['goal']} (line {g.get('line')}, "
                           f"{g['verdict']})")
            shown = 0
            for fct, head, body in blocks:
                if shown >= 12:
                    out.append(f"(... {len(blocks) - shown} more goals not "
                               "shown)")
                    break
                b = body.splitlines()
                if len(b) > 60:
                    b = b[:40] + ["  (...)"] + b[-15:]
                out.append("")
                out += b
                shown += 1
    elif cmd == "wp":
        out.append("WP not run: the guardrails rejected SOURCE.c.")
        entry["ok"] = False
    else:
        entry["ok"] = ok
    entry["seconds"] = round(time.time() - t, 1)
    if logp:
        with open(logp, "a") as f:
            f.write(json.dumps(entry) + "\n")
    print("\n".join(out))
    sys.exit(0 if entry.get("ok") else 1)


if __name__ == "__main__":
    main()
