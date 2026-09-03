#!/usr/bin/env python3
"""
Grind every hole in an Agda file with REALLMS, one hole at a time.

Finds each `{!!}` (or `{! … !}`) line in the target file, and for each one
runs reallms_agent.py on that single line with --apply, so a verified solution
is written into the file before the next hole is attempted (line numbers are
re-scanned after every hole).  reallms_agent.py tolerates the OTHER holes still
present in the file, so no file splitting is needed.

Holes that the model cannot close are left as they were; the summary says
which.  Nothing outside the target file is ever written.

Usage:
  reallms_holes.py --file PATH [--model glm-5.2] [--repo-root DIR]
                   [--agda-root DIR] [--goal-prefix TEXT] [--hint TEXT]
                   [--only NAME[,NAME…]] [--max-steps 24] [--log-dir DIR]
                   [--escalate gpt-oss-120b]

--goal-prefix is prepended to the per-hole goal (which is otherwise just
"Fill the hole in the clause of <name>: <the hole line>").  --escalate names a
second model to try on holes the first one gives up on.
"""
import argparse
import json
import os
import re
import subprocess
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
AGENT = os.path.join(HERE, "reallms_agent.py")
HOLE = re.compile(r"\{!.*?!\}")


def find_holes(path):
    """[(lineno, line, decl-name)] for every line containing a hole."""
    out = []
    with open(path, encoding="utf-8") as f:
        lines = f.readlines()
    for i, ln in enumerate(lines, 1):
        if HOLE.search(ln):
            # the declaration name is the first token of the nearest
            # non-indented clause at or above this line
            name = None
            for j in range(i - 1, -1, -1):
                s = lines[j]
                if s.strip() and not s[0].isspace() and not s.startswith("--"):
                    name = s.split()[0]
                    break
            out.append((i, ln.rstrip("\n"), name))
    return out


def run_agent(model, path, lineno, goal, hint, repo_root, agda_root,
              max_steps, log):
    cmd = [sys.executable, AGENT, "--model", model, "--file", path,
           "--start", str(lineno), "--end", str(lineno), "--goal", goal,
           "--repo-root", repo_root, "--max-steps", str(max_steps), "--apply"]
    if hint:
        cmd += ["--hint", hint]
    if agda_root:
        cmd += ["--agda-root", agda_root]
    if log:
        cmd += ["--log", log]
    proc = subprocess.run(cmd, capture_output=True, text=True)
    try:
        return json.loads(proc.stdout)
    except json.JSONDecodeError:
        return {"status": "harness_error", "solved": False,
                "short_error": (proc.stdout + proc.stderr)[-600:]}


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--file", required=True)
    ap.add_argument("--model", default="glm-5.2")
    ap.add_argument("--escalate", default=None,
                    help="second model to try on holes the first gives up on")
    ap.add_argument("--repo-root", default=os.getcwd())
    ap.add_argument("--agda-root", default=None)
    ap.add_argument("--goal-prefix", default="")
    ap.add_argument("--hint", default="")
    ap.add_argument("--only", default=None,
                    help="comma-separated declaration names to restrict to")
    ap.add_argument("--max-steps", type=int, default=24)
    ap.add_argument("--log-dir", default=None)
    args = ap.parse_args()

    path = os.path.abspath(args.file)
    only = set(args.only.split(",")) if args.only else None
    if args.log_dir:
        os.makedirs(args.log_dir, exist_ok=True)

    results = []
    attempted = set()          # (name, hole text) already tried
    while True:
        holes = [h for h in find_holes(path)
                 if (only is None or h[2] in only)
                 and (h[2], h[1].strip()) not in attempted]
        if not holes:
            break
        lineno, line, name = holes[0]
        attempted.add((name, line.strip()))
        goal = (args.goal_prefix + " " if args.goal_prefix else "") + \
            f"Fill the hole in this clause of `{name}`:\n{line}\n" \
            "Replace exactly this one line (you may split it into several " \
            "clauses / add a local `where` block within the replacement)."
        log = (os.path.join(args.log_dir, f"{name or 'hole'}-{lineno}.log")
               if args.log_dir else None)
        rep = run_agent(args.model, path, lineno, goal, args.hint,
                        args.repo_root, args.agda_root, args.max_steps, log)
        model_used = args.model
        if not rep.get("solved") and args.escalate:
            log2 = (log[:-4] + f"-{args.escalate}.log") if log else None
            rep = run_agent(args.escalate, path, lineno, goal, args.hint,
                            args.repo_root, args.agda_root, args.max_steps,
                            log2)
            model_used = args.escalate
        results.append({"name": name, "line": lineno, "model": model_used,
                        "solved": bool(rep.get("solved")),
                        "status": rep.get("status"),
                        "steps": rep.get("steps"),
                        "short_error": (rep.get("short_error") or "")[:300]})
        print(f"[{'OK ' if rep.get('solved') else 'FAIL'}] {name} "
              f"(line {lineno}, {model_used}, {rep.get('status')})",
              file=sys.stderr, flush=True)

    remaining = find_holes(path)
    print(json.dumps({"file": os.path.relpath(path, args.repo_root),
                      "results": results,
                      "remaining_holes": [(l, n) for l, _, n in remaining]},
                     indent=2, ensure_ascii=False))


if __name__ == "__main__":
    main()
