#!/usr/bin/env python3.13
"""
Agentic REALLMS Agda worker.

Give a REALLMS model its own tools (grep, read_file, check_solution) so it
explores the repo, finds its OWN context, and iterates against `agda` feedback
-- all on free REALLMS tokens, in its own context. Only a COMPACT result comes
back on stdout (final code + pass/fail + short error), so the orchestrator's
(Claude's) scarce token budget is barely touched. The full blow-by-blow
transcript goes to --log for optional inspection.

The worker's job: produce replacement Agda code for a region [start,end] of a
target file so the whole file type-checks (no errors, no holes).

Tools exposed to the model:
  grep(pattern, path?, max_results?)   ripgrep over the repo (read-only)
  read_file(path, start?, end?)        read a slice of any repo file
  check_solution(code)                 splice code into the target region,
                                       run agda, return ok + trimmed errors
                                       (repeatable: this IS the feedback loop)

Key lookup and the chat/tool loop are in reallms_client.py; the key is never printed.
"""
import argparse
import json
import os
import re
import subprocess
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from reallms_client import read_key, tool_loop  # noqa: E402


def detect_agda_root(file_path: str) -> str:
    mod = None
    with open(file_path) as f:
        for line in f:
            m = re.match(r'\s*module\s+([\w.Ā-￿]+)\s+where', line)
            if m:
                mod = m.group(1)
                break
    d = os.path.dirname(os.path.abspath(file_path))
    if mod:
        for _ in range(mod.count(".")):
            d = os.path.dirname(d)
    return d


# ---------- Tools ----------

def trim_agda(out: str) -> str:
    lines = [ln for ln in out.splitlines() if not ln.lstrip().startswith("Checking ")]
    return "\n".join(lines).strip()[:2500]


class Worker:
    def __init__(self, repo_root, target, start, end, agda_root, log):
        self.repo_root = os.path.abspath(repo_root)
        self.target = os.path.abspath(target)
        self.start, self.end = start, end
        self.agda_root = agda_root
        self.log = log
        with open(self.target) as f:
            self.original = f.read()
        self.src_lines = self.original.splitlines(keepends=True)
        self.counts = {"grep": 0, "read_file": 0, "check_solution": 0}
        self.last_code = None
        self.last_ok = False
        self.last_errors = None
        # Pre-existing holes OUTSIDE the target region are tolerated: a
        # candidate passes iff agda reports no error other than unsolved
        # interaction metas at (line-shifted) baseline locations.  This lets a
        # multi-hole file be ground one hole at a time.
        self.baseline_metas = self._meta_lines(self._run_agda()) - set(
            range(self.start, self.end + 1))

    def _run_agda(self):
        proc = subprocess.run(["agda", self.target], cwd=self.agda_root,
                              capture_output=True, text=True)
        return proc.returncode, proc.stdout + proc.stderr

    def _meta_lines(self, res):
        """Line numbers of unsolved interaction metas in the TARGET file
        (the indented location lines under the UnsolvedInteractionMetas
        header)."""
        _, out = res
        base = re.escape(os.path.basename(self.target))
        pat = re.compile(r"^\s+\S*" + base + r":(\d+)\.\d+-")
        return {int(m.group(1)) for ln in out.splitlines()
                for m in [pat.match(ln)] if m}

    def _only_baseline_metas(self, res, code_nlines):
        """True iff the only problem agda reports is unsolved interaction
        metas, all of which are pre-existing holes outside the region."""
        rc, out = res
        if rc == 0:
            return True
        errs = re.findall(r"error: \[(\w+)\]", out)
        if not errs or any(e != "UnsolvedInteractionMetas" for e in errs):
            return False
        if "Unsolved metas" in out:
            return False
        delta = code_nlines - (self.end - self.start + 1)
        new_end = self.start + code_nlines - 1
        for ln in self._meta_lines(res):
            if self.start <= ln <= new_end:
                return False           # a hole inside the candidate itself
            orig = ln - delta if ln > new_end else ln
            if orig not in self.baseline_metas:
                return False
        return True

    def _safe(self, path):
        # Resolve symlinks and use component-aware containment so a sibling
        # like `<repo>-secret` or a symlink cannot escape the repo root.
        root = os.path.realpath(self.repo_root)
        p = os.path.realpath(os.path.join(root, path))
        if p != root and os.path.commonpath([root, p]) != root:
            raise ValueError("path escapes repo root")
        return p

    def grep(self, pattern, path=None, max_results=40):
        self.counts["grep"] += 1
        target = self._safe(path) if path else self.repo_root
        try:
            proc = subprocess.run(
                ["rg", "-n", "--no-heading", "-g", "*.agda", pattern, target],
                capture_output=True, text=True, timeout=60)
            lines = proc.stdout.splitlines()[:max_results]
            rel = [ln.replace(self.repo_root + "/", "") for ln in lines]
            return "\n".join(rel) if rel else "(no matches)"
        except Exception as e:
            return f"(grep error: {e})"

    def read_file(self, path, start=None, end=None):
        self.counts["read_file"] += 1
        p = self._safe(path)
        try:
            with open(p) as f:
                lines = f.readlines()
        except Exception as e:
            return f"(read error: {e})"
        s = max(1, start or 1)
        e = min(len(lines), end or len(lines))
        chunk = "".join(f"{i}\t{lines[i-1]}" for i in range(s, e + 1))
        return chunk[:6000]

    def check_solution(self, code):
        self.counts["check_solution"] += 1
        self.last_code = code
        new_lines = (self.src_lines[:self.start - 1] + [code + "\n"]
                     + self.src_lines[self.end:])
        try:
            with open(self.target, "w") as f:
                f.write("".join(new_lines))
            res = self._run_agda()
            out = res[1]
        finally:
            with open(self.target, "w") as f:
                f.write(self.original)
        ok = self._only_baseline_metas(res, code.count("\n") + 1)
        self.last_ok = ok
        if ok:
            self.solution_text = "".join(new_lines)
        self.last_errors = "" if ok else trim_agda(out)
        return {"ok": ok, "errors": self.last_errors}

    def dispatch(self, name, args):
        if name == "grep":
            return self.grep(args.get("pattern", ""), args.get("path"),
                             int(args.get("max_results", 40)))
        if name == "read_file":
            return self.read_file(args["path"], args.get("start"), args.get("end"))
        if name == "check_solution":
            return self.check_solution(args["code"])
        return f"(unknown tool: {name})"


TOOLS = [
    {"type": "function", "function": {
        "name": "grep",
        "description": "Search *.agda files in the repo for a regex pattern (ripgrep). "
                       "Returns matching 'relpath:line:text' lines. Use to find "
                       "datatypes, lemmas, reduction rules, and usage examples.",
        "parameters": {"type": "object", "properties": {
            "pattern": {"type": "string"},
            "path": {"type": "string", "description": "optional subdir/file to limit search"},
            "max_results": {"type": "integer"}},
            "required": ["pattern"]}}},
    {"type": "function", "function": {
        "name": "read_file",
        "description": "Read a slice of a repo file (relative path). Returns "
                       "line-numbered text. Use start/end to read just the region "
                       "you need (definitions, sibling proofs, helper signatures).",
        "parameters": {"type": "object", "properties": {
            "path": {"type": "string"},
            "start": {"type": "integer"}, "end": {"type": "integer"}},
            "required": ["path"]}}},
    {"type": "function", "function": {
        "name": "check_solution",
        "description": "Splice your candidate Agda code into the target region and "
                       "type-check the whole file with agda. Returns {ok, errors}. "
                       "Call this as many times as needed -- it is your feedback "
                       "loop. When ok is true you are DONE.",
        "parameters": {"type": "object", "properties": {
            "code": {"type": "string", "description": "replacement code for the target region"}},
            "required": ["code"]}}},
]


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--model", required=True)
    ap.add_argument("--file", required=True, help="target file (absolute)")
    ap.add_argument("--start", type=int, required=True)
    ap.add_argument("--end", type=int, required=True)
    ap.add_argument("--goal", required=True, help="what to prove/produce")
    ap.add_argument("--hint", default="", help="optional cheap steer from orchestrator")
    ap.add_argument("--repo-root", default=os.getcwd())
    ap.add_argument("--agda-root", default=None)
    ap.add_argument("--max-steps", type=int, default=24)
    ap.add_argument("--temperature", type=float, default=0.2)
    ap.add_argument("--log", default=None)
    ap.add_argument("--apply", action="store_true",
                    help="on success, write the verified solution into the "
                         "target file (default: leave the file untouched)")
    args = ap.parse_args()

    key = read_key()
    target = os.path.abspath(args.file)
    agda_root = args.agda_root or detect_agda_root(target)
    w = Worker(args.repo_root, target, args.start, args.end, agda_root, args.log)
    fh = open(args.log, "w") if args.log else None

    region = "".join(w.src_lines[args.start - 1:args.end])
    system = (
        "You are an autonomous Agda proof engineer working inside a repository. "
        "You have tools to grep and read any file, and a check_solution tool that "
        "type-checks your candidate against the real agda compiler. Your job: "
        "replace the indicated region of the target file so the whole file "
        "type-checks with NO errors and NO holes in YOUR region (holes that "
        "already exist elsewhere in the file are tolerated). Explore the repo to find the "
        "definitions, reduction rules, and sibling proofs you need -- do not guess "
        "when you can look. Iterate with check_solution until ok=true. Be "
        "thorough; token cost is not a concern. When check_solution returns "
        "ok=true, stop and give a one-line summary."
    )
    user = (
        f"Target file: {os.path.relpath(target, w.repo_root)}\n"
        f"Region to replace: lines {args.start}-{args.end}, currently:\n\n"
        f"```agda\n{region}\n```\n\n"
        f"Goal: {args.goal}\n"
        + (f"\nOrchestrator hint: {args.hint}\n" if args.hint else "")
        + "\nProduce replacement code for exactly that region and verify it with "
          "check_solution."
    )
    loop = tool_loop(
        args.model, key, system, user, TOOLS, w.dispatch,
        solved=lambda: w.last_ok, check_tool="check_solution",
        nudge="You did not call a tool. Reasoning alone does not count: "
              "submit your complete replacement code for the target region "
              "NOW via check_solution(code), then fix whatever Agda reports.",
        max_steps=args.max_steps, temperature=args.temperature, fh=fh)
    status, step = loop["status"], loop["steps"]

    # Compact report to stdout (this is all the orchestrator ingests).
    report = {
        "model": args.model,
        "status": status,
        "solved": w.last_ok,
        "steps": step,
        "tool_calls": w.counts,
        "final_code": w.last_code,
        "short_error": (w.last_errors or "")[:600] if not w.last_ok else "",
        "usage": loop["usage"],
        "seconds": loop["seconds"],
        "log": args.log,
    }
    if args.apply and w.last_ok:
        with open(w.target, "w") as f:
            f.write(w.solution_text)
        report["applied"] = True
    print(json.dumps(report, indent=2, ensure_ascii=False))
    if fh:
        fh.write("\n===== REPORT =====\n" + json.dumps(report, indent=2, ensure_ascii=False) + "\n")
        fh.close()


if __name__ == "__main__":
    main()
