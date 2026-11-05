#!/usr/bin/env python3
"""Prover escalation strategies on a fixed goal set (plan section 12.3).

    python3 escalation.py [--goals results/escalation/goals]
        [--out results/escalation/attempts.jsonl] [--usd 15]
        [--glm-k 16] [--jobs 3] [--phases s1,s4,s3]

The goal set is fixed (so only the prover varies): WP goal files with
their proofs removed, in --goals.  Every attempt runs through
`tiers.chain` on a fresh copy of the goal file (coqc confirms a proof;
the fence retry applies) and is appended to --out, so a rerun resumes
where it stopped.  Phases:

  s1  each model alone, one attempt per goal: GLM 5.3 Flash,
      gpt-oss-120b, qwen3.8-27b (REALLMS, 120 s of working time each),
      Sonnet 5.5 and Opus 5.5 (headless Claude Code, tier 2's fence);
  s4  GLM attempts 2..k on each goal GLM has not proved yet (attempt 1
      is s1's);
  s3  linear escalation with hand-off: on each goal GLM's attempt 1
      missed, Sonnet with GLM's best partial script (the longest prefix
      show_goals ran without an error, with its goals); where Sonnet
      misses too, Opus with Sonnet's last script.

S2 (GLM -> Sonnet -> Opus) and S4 (k GLM attempts, then Sonnet, then
Opus) are composed from the s1 and s4 attempts: a goal's result is the
first success in that order, its cost and time the sum of the attempts
up to it.  `table` prints the comparison: goals closed, Anthropic USD
per closed goal, wall clock per closed goal.

The Anthropic spending of the whole comparison is capped by --usd: an
attempt is not started when what the ledger charged the comparison's
attempts so far, plus the attempt's own cap, would pass it.
"""
import argparse
import concurrent.futures as cf
import json
import os
import shutil
import sys
import threading
import time

HERE = os.path.dirname(os.path.abspath(__file__))
ARIADNE = os.path.dirname(HERE)
sys.path.insert(0, HERE)
import budget  # noqa: E402
import tier0  # noqa: E402
import tiers  # noqa: E402
from reallms_coq import split_goal  # noqa: E402

OPUS = "claude-opus-5-5"
FREE = ("glm-5.3-flash", "gpt-oss-120b", "qwen3.8-27b")
CAPS = {tiers.SONNET: 0.75, OPUS: 1.5}  # --max-budget-usd per attempt
LOCK = threading.Lock()


class HandOff:
    """A tier whose prompt starts with a lower tier's partial proof."""

    def __init__(self, tier, partial, goals=None):
        self.tier, self.inner = tier.tier, tier
        self.note = ("A weaker prover's best partial proof script (it runs "
                     "without an error up to its end):\n\n" + partial
                     + ("\n\nGoals left after it:\n" + goals if goals else "")
                     + "\n\nYou may continue it or start over.\n")

    def run(self, path, goal, note=None):
        return self.inner.run(path, goal, note=self.note + (
            "\n" + note if note else ""))


class Runner:
    def __init__(self, a):
        self.a = a
        self.goals = sorted(f[:-2] for f in os.listdir(a.goals)
                            if f.endswith(".v"))
        self.work = os.path.join(ARIADNE, "runs", "escalation")
        os.makedirs(self.work, exist_ok=True)
        self.ledger = budget.Ledger(a.ledger)
        self.rows = [json.loads(x) for x in open(a.out)] \
            if os.path.exists(a.out) else []

    def done(self, phase, model, goal, k=1):
        return next((r for r in self.rows if r["phase"] == phase
                     and r["model"] == model and r["goal"] == goal
                     and r["k"] == k), None)

    def spent(self):
        """The comparison's Anthropic USD so far: the sum of what the
        ledger charged its attempts (other runs may use the ledger too)."""
        return round(sum(r.get("usd") or 0 for r in self.rows), 6)

    def tier(self, model, root):
        if model in FREE:
            return tiers.Tier1(os.path.join(root, "logs"), seconds=120,
                               model=model, ledger=self.ledger,
                               hide=tiers.hidden_paths(), keep=[root])
        return tiers.Tier2(os.path.join(root, "tier2"), self.ledger,
                           model=model, usd=CAPS[model])

    def attempt(self, phase, model, goal, k=1, handoff=None):
        """One attempt (or the cached one)."""
        r = self.done(phase, model, goal, k)
        if r:
            return r
        if model not in FREE:
            with LOCK:
                if self.spent() + CAPS[model] > self.a.usd:
                    return {"phase": phase, "model": model, "goal": goal,
                            "k": k, "status": "skipped: comparison budget"}
        root = os.path.join(self.work, f"{phase}-{model}-{goal}-{k}")
        if os.path.exists(root):
            shutil.rmtree(root)
        os.makedirs(os.path.join(root, "logs"))
        path = os.path.join(root, goal + ".v")
        shutil.copy(os.path.join(self.a.goals, goal + ".v"), path)
        t = self.tier(model, root)
        if handoff:
            t = HandOff(t, *handoff)
        before = self.ledger.summary()["usd"]
        c = tiers.chain(path, goal, [t], tier0.coqc)
        a = c["attempts"]
        r = {"phase": phase, "model": model, "goal": goal, "k": k,
             "handoff": bool(handoff), "status": c["status"],
             "seconds": c["seconds"], "usd": c["usd"],
             "tokens": c["tokens"], "fence_retry": len(a) > 1,
             "partial": a[-1].get("partial") if a else None,
             "partial_goals": a[-1].get("partial_goals") if a else None,
             "end": a[-1].get("end") if a else None,
             "ledger_usd_before": round(before, 6)}
        with LOCK:
            self.rows.append(r)
            with open(self.a.out, "a") as f:
                f.write(json.dumps(r) + "\n")
        print(f"{phase} {model} {goal} #{k}: {r['status']} "
              f"({r['seconds']} s, ${r['usd']}; comparison ${self.spent()})",
              flush=True)
        return r

    def pool(self, jobs):
        with cf.ThreadPoolExecutor(self.a.jobs) as ex:
            list(ex.map(lambda j: self.attempt(*j[:-1], **j[-1]), jobs))

    def s1(self):
        for m in FREE:
            self.pool([("s1", m, g, {}) for g in self.goals])
        self.s1paid()

    def s1free(self):
        for m in FREE:
            self.pool([("s1", m, g, {}) for g in self.goals])

    def s1paid(self):
        for m in (tiers.SONNET, OPUS):
            self.pool([("s1", m, g, {}) for g in self.goals])

    def s4(self):
        def glm(g):
            for k in range(2, self.a.glm_k + 1):
                prev = [self.done("s1" if j == 1 else "s4", FREE[0], g, j)
                        for j in range(1, k)]
                if any(p and p["status"] == "proved" for p in prev):
                    return
                self.attempt("s4", FREE[0], g, k)
        with cf.ThreadPoolExecutor(self.a.jobs) as ex:
            list(ex.map(glm, self.goals))

    def s3(self):
        def esc(g):
            g1 = self.done("s1", FREE[0], g)
            if not g1 or g1["status"] == "proved":
                return
            ho = (g1["partial"], g1["partial_goals"]) if g1["partial"] \
                else None
            s = self.attempt("s3", tiers.SONNET, g, handoff=ho)
            if s["status"] == "proved" or s["status"].startswith("skipped"):
                return
            ho = (s["partial"], None) if s.get("partial") else ho
            self.attempt("s3", OPUS, g, handoff=ho)
        with cf.ThreadPoolExecutor(self.a.jobs) as ex:
            list(ex.map(esc, self.goals))


def compose(rows, goals, chain):
    """A strategy as an ordered list of (phase, model, k) attempts per
    goal: the first proved one wins; cost and time add up to it."""
    out = []
    for g in goals:
        usd = sec = 0.0
        closed, by, n = False, None, 0
        for phase, model, k in chain(g):
            r = next((x for x in rows if x["phase"] == phase
                      and x["model"] == model and x["goal"] == g
                      and x["k"] == k), None)
            if r is None:
                break
            n += 1
            usd += r.get("usd") or 0
            sec += r.get("seconds") or 0
            if r["status"] == "proved":
                closed, by = True, model
                break
        out.append({"goal": g, "closed": closed, "by": by, "usd": usd,
                    "seconds": sec, "attempts": n})
    return out


def strategies(glm_k):
    glm = FREE[0]
    s = {f"S1 {m}": (lambda m: lambda g: [("s1", m, 1)])(m)
         for m in FREE + (tiers.SONNET, OPUS)}
    s["S2 GLM, Sonnet, Opus"] = lambda g: [("s1", glm, 1),
                                           ("s1", tiers.SONNET, 1),
                                           ("s1", OPUS, 1)]
    s["S3 S2 with hand-off"] = lambda g: [("s1", glm, 1),
                                          ("s3", tiers.SONNET, 1),
                                          ("s3", OPUS, 1)]
    for k in (1, 4, 16):
        if k <= glm_k:
            s[f"S4 k={k}"] = (lambda k: lambda g: [
                ("s1" if j == 1 else "s4", glm, j) for j in range(1, k + 1)]
                + [("s1", tiers.SONNET, 1), ("s1", OPUS, 1)])(k)
    return s


def table(rows, goals, glm_k):
    lines = ["| Strategy | Goals closed | Anthropic USD | USD per closed "
             "goal | Wall clock (s) | s per closed goal | Closed by |",
             "|---|---|---|---|---|---|---|"]
    for name, chain in strategies(glm_k).items():
        res = compose(rows, goals, chain)
        n = sum(r["closed"] for r in res)
        usd = sum(r["usd"] for r in res)
        sec = sum(r["seconds"] for r in res)
        by = {}
        for r in res:
            if r["by"]:
                by[r["by"]] = by.get(r["by"], 0) + 1
        per = (lambda x: f"{x / n:.3f}" if n else "-")
        lines.append(f"| {name} | {n} / {len(goals)} | {usd:.2f} | "
                     f"{per(usd)} | {sec:.0f} | "
                     f"{(sec / n if n else 0):.0f} | "
                     + ", ".join(f"{k} {v}" for k, v in by.items()) + " |")
    return "\n".join(lines)


def main():
    ap = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    ap.add_argument("--goals", default=os.path.join(HERE, "results",
                                                    "escalation", "goals"))
    ap.add_argument("--out", default=os.path.join(HERE, "results",
                                                  "escalation",
                                                  "attempts.jsonl"))
    ap.add_argument("--ledger", default=budget.PATH)
    ap.add_argument("--usd", type=float, default=15.0)
    ap.add_argument("--glm-k", type=int, default=16)
    ap.add_argument("--jobs", type=int, default=3)
    ap.add_argument("--phases", default="s1,s4,s3")
    ap.add_argument("--table", action="store_true",
                    help="only print the table of what --out holds")
    a = ap.parse_args()
    r = Runner(a)
    if not a.table:
        for ph in [p for p in a.phases.split(",") if p]:
            t = time.time()
            getattr(r, ph)()
            print(f"phase {ph}: {time.time() - t:.0f} s; comparison "
                  f"${r.spent()}", flush=True)
    print(table(r.rows, r.goals, a.glm_k))


def make_goals(sources, out):
    """Write the fixed goal set: each source goal file with its proof
    removed (an empty script), as <name>.v in `out`."""
    os.makedirs(out, exist_ok=True)
    for name, src in sources:
        prefix, _, suffix = split_goal(open(src).read())
        with open(os.path.join(out, name + ".v"), "w") as f:
            f.write(prefix + "\n" + suffix)


if __name__ == "__main__":
    main()
