#!/usr/bin/env python3
"""Prover tiers 1 and 2 for step 4 (plan section 12.2), and the chain
that runs them on a goal tier 0 left open.

  tier 1  GLM 5.3 Flash on REALLMS (`../prover/reallms_coq.py --blank`),
          a working-time budget (default 120 s); free, its tokens are
          logged in the ledger but not charged;
  tier 2  Claude Sonnet 5.5 as headless Claude Code (`claude -p`, billed
          to the owner's subscription), with only the `prover_cli.py`
          commands on its own goal copy and script, and Read/Write in its
          own work directory; a per-goal cap on calls, turns, seconds
          and dollars; the ledger must allow the call first.

A tier's proof counts only once `confirm` (coqc on the real goal file,
plus the forbidden-command check) accepts it; the harness then reruns
WP, which checks it again.

    python3 tiers.py GOAL.v [--tiers 1,2] [--work DIR]   (one goal)
"""
import argparse
import json
import os
import re
import subprocess
import sys
import time

HERE = os.path.dirname(os.path.abspath(__file__))
ARIADNE = os.path.dirname(HERE)
PROVER = os.path.join(ARIADNE, "prover")
sys.path.insert(0, HERE)
sys.path.insert(0, PROVER)
import ledger as ledger_mod  # noqa: E402
from reallms_coq import FORBIDDEN, normalise, split_goal  # noqa: E402

CLI = os.path.join(PROVER, "prover_cli.py")
REALLMS = os.path.join(PROVER, "reallms_coq.py")
SONNET = "claude-sonnet-5-5"


class Tier1:
    """GLM 5.3 Flash through reallms_coq.py."""
    tier, name = 1, "glm"

    def __init__(self, logs, seconds=120, model="glm-5.3-flash",
                 hide=(), keep=(), ledger=None):
        self.logs, self.seconds, self.model = logs, seconds, model
        self.hide, self.keep, self.ledger = hide, keep, ledger

    def run(self, path, goal):
        log = os.path.join(self.logs, f"step4_tier1_{goal}.log")
        cmd = [sys.executable, REALLMS, "--file", path, "--blank",
               "--model", self.model, "--max-seconds", str(self.seconds),
               "--log", log]
        for h in self.hide:
            cmd += ["--hide", h]
        for k in self.keep:
            cmd += ["--keep", k]
        t = time.time()
        try:
            p = subprocess.run(cmd, capture_output=True, text=True,
                               timeout=self.seconds * 5 + 600,
                               stdin=subprocess.DEVNULL)
            rep = json.loads(p.stdout)
        except subprocess.TimeoutExpired:
            return {"tier": 1, "model": self.model, "status": "timeout",
                    "seconds": round(time.time() - t, 1)}
        except ValueError:
            return {"tier": 1, "model": self.model, "status": "error",
                    "error": (p.stderr or p.stdout)[-600:],
                    "seconds": round(time.time() - t, 1)}
        usage = rep.get("usage") or {}
        if self.ledger:
            self.ledger.log_free(self.model, usage)
        return {"tier": 1, "model": self.model,
                "status": "proved" if rep.get("solved") else "open",
                "script": rep.get("script"), "steps": rep.get("steps"),
                "seconds": round(time.time() - t, 1),
                "working_seconds": rep.get("seconds"),
                "end": rep.get("status"),
                "tokens": sum(v for v in usage.values()
                              if isinstance(v, int)),
                "usage": usage, "charged": False}


PROMPT = """\
You are a Coq/Rocq 9 proof engineer.  Prove one goal that Frama-C/WP
generated through Why3.  Your directory holds GOAL.v (the Why3 context,
then `Theorem wp_goal`, with an empty proof) and nothing else of use.

Write the proof script, the text between `Proof.` and `Qed.` (write
neither), into SCRIPT.v in this directory, and use only these commands:

  python3 {cli} statement GOAL.v
  python3 {cli} query GOAL.v 'Check nth_cons.'      (one Search, Check,
                                                    Print, About or Locate)
  python3 {cli} goals GOAL.v SCRIPT.v               (goals after a partial
                                                    script)
  python3 {cli} check GOAL.v SCRIPT.v               (the whole proof)

You may Read GOAL.v and Read/Write files in this directory; nothing else
is allowed.  You have {calls} `goals`/`check` calls in all.  `check`
prints "OK: proof accepted by coqc" when the proof is accepted: stop
right after it.  admit, Admitted, Abort, Defined and new axioms or
definitions are refused.

How Why3 encodes goals: integers are Z; `nth` and `Length.length` are
opaque functions axiomatised by lemmas in GOAL.v, which usually have
hypotheses and conjunctions, so `rewrite L` alone fails: use `destruct
(L args) as [H1 H2]` (prove the hypothesis with lia) or `pose proof`.
lia does not know these functions: rewrite `Length.length (x :: w)` with
the length lemma first, and give lia the length_pos lemma.  Do not use
simpl, cbn, compute or unfold on goals with Z comparisons.  Lia and
CoqHammer (hammer, sauto) are loaded.

When done, answer with one line: SOLVED or GAVE UP.
"""


def sonnet_command(work, model=SONNET, calls=30, turns=60, usd=2.0,
                   prompt=None):
    """The `claude -p` command line for one tier-2 goal in `work`."""
    rule = f"python3 {CLI}"
    allowed = [f"Bash({rule} statement GOAL.v)",
               f"Bash({rule} query GOAL.v *)",
               f"Bash({rule} goals GOAL.v SCRIPT.v)",
               f"Bash({rule} check GOAL.v SCRIPT.v)",
               f"Read(/{work}/**)", f"Write(/{work}/**)",
               f"Edit(/{work}/**)"]
    return ["claude", "-p", prompt or PROMPT.format(cli=CLI, calls=calls),
            "--model", model, "--output-format", "json",
            "--max-turns", str(turns), "--max-budget-usd", str(usd),
            "--no-session-persistence", "--safe-mode", "--restricted",
            "--strict-mcp-config", "--disable-slash-commands",
            "--tools", "Bash,Read,Write,Edit",
            "--allowedTools", *allowed,
            # Claude Code lets read-only git commands run unasked; the
            # repository's history holds the benchmark's proofs.
            "--disallowedTools", "Bash(git *)", "Bash(git)",
            "--permission-mode", "dontAsk"]


def sonnet_env(work, calls_log, calls):
    """The environment of a tier-2 run: the call log and cap of
    prover_cli.py, and git kept from finding the repository above
    `work` (a second fence behind the deny rule)."""
    return dict(os.environ, PROVER_CLI_LOG=calls_log,
                PROVER_CLI_MAX_CALLS=str(calls),
                GIT_CEILING_DIRECTORIES=os.path.dirname(work),
                GIT_DIR=os.path.join(work, ".no-git"))


class Tier2:
    """Sonnet 5.5 as headless Claude Code, charged to the ledger."""
    tier, name = 2, "sonnet"

    def __init__(self, root, ledger, model=SONNET, calls=30, turns=60,
                 seconds=600, usd=2.0, est_tokens=200_000, role="prover"):
        self.root, self.ledger, self.model = root, ledger, model
        self.calls, self.turns, self.seconds = calls, turns, seconds
        self.usd, self.est_tokens, self.role = usd, est_tokens, role

    def run(self, path, goal):
        t = time.time()
        res = {"tier": 2, "model": self.model}
        gate = self.ledger.reserve(self.role, self.model, self.est_tokens)
        res["budget"] = gate
        if not gate["ok"]:
            res.update(status="refused", seconds=0.0,
                       error=f"budget: {gate['projected_pct']}% would pass "
                       f"the {gate['cap_pct']}% cap")
            return res
        work = os.path.join(self.root, goal)
        os.makedirs(work)
        prefix, _, suffix = split_goal(open(path).read())
        with open(os.path.join(work, "GOAL.v"), "w") as f:
            f.write(prefix + "\n" + suffix)  # the statement, no proof
        calls_log = os.path.join(work, "calls.jsonl")
        env = sonnet_env(work, calls_log, self.calls)
        cmd = sonnet_command(work, self.model, self.calls, self.turns,
                             self.usd)
        out = None
        try:
            p = subprocess.run(cmd, cwd=work, env=env, capture_output=True,
                               text=True, timeout=self.seconds,
                               stdin=subprocess.DEVNULL)
            with open(os.path.join(work, "result.json"), "w") as f:
                f.write(p.stdout)
            if p.stderr:
                open(os.path.join(work, "stderr.txt"), "w").write(p.stderr)
            out = json.loads(p.stdout)
        except subprocess.TimeoutExpired:
            res["end"] = "timeout"
        except ValueError:
            res["end"] = "no JSON result"
        mu = ledger_mod.by_model(out, self.model) if out else {}
        c = self.ledger.charge(self.role, mu, est_tokens=self.est_tokens,
                               note=self.model)
        res.update(tokens=c["tokens"], pct_after=c["pct"],
                   warning=c["warning"], charged=True,
                   estimated=not mu, usage=mu)
        if out:
            res.update(end=out.get("subtype"), turns=out.get("num_turns"),
                       cost_usd=out.get("total_cost_usd"),
                       answer=(out.get("result") or "")[-200:],
                       permission_denials=len(
                           out.get("permission_denials") or []))
        res["cli_calls"] = cli_calls(calls_log)
        sp = os.path.join(work, "SCRIPT.v")
        script = open(sp).read() if os.path.exists(sp) else None
        ok = any(c["cmd"] == "check" and c["ok"]
                 for c in res["cli_calls"]["log"])
        res["cli_calls"].pop("log")
        res.update(status="proved" if ok and script else "open",
                   script=normalise(script).strip("\n") if script else None,
                   seconds=round(time.time() - t, 1))
        return res


def cli_calls(path):
    log = [json.loads(x) for x in open(path)] if os.path.exists(path) \
        else []
    n = {}
    for c in log:
        n[c["cmd"]] = n.get(c["cmd"], 0) + 1
    return {"counts": n, "log": log}


def confirm(path, script, coqc, timeout=120):
    """Accept a tier's script for the goal file at `path` iff it has no
    forbidden command and coqc accepts the real file with it; then write
    it into the file.  `coqc(prefix, script, suffix, timeout)` gives
    (ok, output)."""
    if not script:
        return False, "no script"
    script = normalise(script).strip("\n")
    bad = FORBIDDEN.search(script)
    if bad:
        return False, f"forbidden: {bad.group(1)}"
    prefix, _, suffix = split_goal(open(path).read())
    ok, out = coqc(prefix, script, suffix, timeout)
    if ok:
        with open(path, "w") as f:
            f.write(prefix + "\n" + script + suffix)
    return ok, out[-600:]


def chain(path, goal, tiers, coqc, stop=lambda: False):
    """Run the tiers in order on one goal until one's proof is confirmed.
    A refusal by the budget ends the chain (and is reported, so the
    caller stops asking).  {goal, status, tier, model, script, seconds,
    tokens, attempts}."""
    attempts, t = [], time.time()
    out = {"goal": goal, "status": "open", "tier": None, "model": None,
           "script": None, "attempts": attempts}
    for tier in tiers:
        if stop():
            out["stopped"] = "total time cap"
            break
        r = tier.run(path, goal)
        attempts.append(r)
        if r["status"] == "refused":
            out["status"] = "refused"
            break
        if r["status"] != "proved":
            continue
        ok, detail = confirm(path, r["script"], coqc)
        r["coqc_confirmed"] = ok
        if not ok:
            r["status"], r["confirm_error"] = "rejected", detail
            continue
        out.update(status="proved", tier=r["tier"], model=r["model"],
                   script=normalise(r["script"]).strip("\n"))
        break
    out["seconds"] = round(time.time() - t, 1)
    out["tokens"] = sum(a.get("tokens") or 0 for a in attempts)
    out["charged_tokens"] = sum(a.get("tokens") or 0 for a in attempts
                                if a.get("charged"))
    return out


def main():
    import tier0
    ap = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    ap.add_argument("goal")
    ap.add_argument("--tiers", default="1,2")
    ap.add_argument("--work", default=os.path.join(
        ARIADNE, "runs", time.strftime("tiers-%Y%m%d-%H%M%S")))
    ap.add_argument("--glm-seconds", type=int, default=120)
    ap.add_argument("--sonnet-calls", type=int, default=30)
    ap.add_argument("--sonnet-seconds", type=int, default=600)
    a = ap.parse_args()
    os.makedirs(a.work)
    L = ledger_mod.Ledger()
    want = {int(x) for x in a.tiers.split(",")}
    ts = []
    if 1 in want:
        ts.append(Tier1(a.work, a.glm_seconds, ledger=L,
                        hide=hidden_paths(), keep=[os.path.dirname(
                            os.path.abspath(a.goal))]))
    if 2 in want:
        ts.append(Tier2(os.path.join(a.work, "tier2"), L,
                        calls=a.sonnet_calls, seconds=a.sonnet_seconds))
    goal = re.sub(r"\.v$", "", os.path.basename(a.goal))
    print(json.dumps(chain(os.path.abspath(a.goal), goal, ts, tier0.coqc),
                     indent=1))


def hidden_paths():
    """What tier 1's read_file and grep refuse: every other place a proof
    of a benchmark goal is kept."""
    out = [os.path.join(ARIADNE, "runs"),
           os.path.join(ARIADNE, "prover", "results"),
           os.path.join(ARIADNE, "harness", "results")]
    bench = os.path.join(ARIADNE, "bench")
    for b in sorted(os.listdir(bench)):
        if os.path.isdir(os.path.join(bench, b, "session")):
            out.append(os.path.join(bench, b, "session"))
    return out


if __name__ == "__main__":
    main()
