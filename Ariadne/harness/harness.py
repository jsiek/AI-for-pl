#!/usr/bin/env python3
"""The Ariadne pipeline without an LLM (plan section 5, steps 0-7;
milestone M2): runtime checks, Frama-C/WP, tier-0 proof search, close
out with coqc / coqchk / Print Assumptions, guardrails, and a report.

    python3 harness.py ../bench/b1 [--config b1.json] [--run-dir DIR]
        [--blank-coq] [--overlay EDITED.c] [--no-rac] [--tiers 0,2]
        [--goal-seconds 300] [--tactic-seconds 60] [--glm-seconds 120]
        [--claude-model claude-opus-5-5] [--claude-calls 30]
        [--claude-seconds 600] [--claude-usd 1]
        [--ledger ../runs/budget.json]
        [--max-iterations 1] [--max-seconds 3600]

A run works on a copy of the benchmark in its own directory (default
Ariadne/runs/<name>-<time>/; it must be under Ariadne/, which the
toolchain image mounts at /ariadne).  Nothing in the benchmark is
written: the harness hashes every benchmark file before and after and
reports a change as a failed guardrail.  --blank-coq drops the
benchmark's Coq proof scripts from the copy (the M2 measurement "how
much does automation alone close").

Steps (plan section 5):
  guardrails  overlay, frozen spec, ACSL lint of the copy against the
              benchmark (plan 7.1-7.3a), before any tool runs on it;
  0  runtime checking: the benchmark's RAC script (sanitizers, E-ACSL,
     mutants), run on the copy;
  1  normalise: -ariadne + RTE, `-print` into <source>.rte.c;
  2  Eva: skipped (optional in the plan);
  3  WP, one run per pass of the config; `-wp-interactive update`
     writes a Coq goal file for every goal sent to Coq;
  4  proof search on each open goal: tier 0 (tier0.py, no model), then
     tier 1 (GLM 5.3 Flash, off by default) and tier 2 (Opus 5.5 by
     default, within the budget ledger) (tiers.py); each proof is checked by coqc, then step 3 runs
     again if any goal was closed, so WP checks it too;
  5  refinement: a stub; it records each open goal as a stall, with its
     statement as the last state (there is no annotator in M2);
  6  close out: Coq lint, coqc, coqchk -o and Print Assumptions on every
     goal Coq closed, axioms against the allow-list (plan 7.4);
  7  caps (refinement iterations, total seconds) and the verdict: a
     certificate only if every goal is accounted for (plan 7.5) and
     every guardrail passed; otherwise a failure report.

Output in the run directory: report.json, report.md, logs/, cert/.
"""
import argparse
import collections
import fnmatch
import hashlib
import json
import os
import re
import shutil
import subprocess
import sys
import time

HERE = os.path.dirname(os.path.abspath(__file__))
ARIADNE = os.path.dirname(HERE)
sys.path.insert(0, HERE)
import guardrails  # noqa: E402
import budget  # noqa: E402
import tier0  # noqa: E402
import tiers  # noqa: E402
import annotator  # noqa: E402
import annotator_cli  # noqa: E402
from reallms_coq import split_goal  # noqa: E402  (path set by guardrails)

RUN = os.path.join(ARIADNE, "env", "run.sh")
WHY3 = "/home/rocq/.opam/4.14.2/lib/why3/coq"
COQ_FLAGS = ["-native-compiler", "no", "-R", WHY3, "Why3"]


def tree_hashes(root):
    """sha256 of every file under root, by relative path."""
    out = {}
    for d, _, files in os.walk(root):
        for f in files:
            p = os.path.join(d, f)
            with open(p, "rb") as fh:
                out[os.path.relpath(p, root)] = \
                    hashlib.sha256(fh.read()).hexdigest()
    return out


def discharger(goal):
    """Who closed a goal of a WP JSON report: qed, smt:<prover>, coq, or
    open."""
    if goal["verdict"] != "valid":
        return "open"
    winners = [p["prover"] for p in goal.get("provers", [])
               if p.get("success")]
    w = winners[0] if winners else "qed"
    if w == "qed":
        return "qed"
    if w.lower().startswith("coq"):
        return "coq"
    return "smt:" + w.split(":")[0]


def census(goals):
    c = collections.Counter()
    for g in goals:
        d = g["discharger"]
        c["smt" if d.startswith("smt:") else d] += 1
    smt = collections.Counter(g["discharger"][4:] for g in goals
                              if g["discharger"].startswith("smt:"))
    return {"goals": len(goals), "proved": len(goals) - c["open"],
            "qed": c["qed"], "smt": c["smt"], "coq": c["coq"],
            "open": c["open"], "smt_by_prover": dict(sorted(smt.items()))}



def rac_outcome(rac):
    """Step 0 on a patch: `pass`; `false` (a check fired on a run); or
    `inconclusive` (only the E-ACSL build or the RAC generation failed:
    a limit of the tooling, not evidence against the annotations)."""
    if not rac or rac.get("ok") is not False:
        return "pass"
    fails = rac.get("fail_lines") or []
    if fails and all(re.match(r"FAIL: (E-ACSL build|gen_rac\.py|"
                              r"gen_twins\.py)", f) for f in fails):
        return "inconclusive"
    return "false"


def steps_succeeded(report):
    """Normalisation and WP ran and succeeded, no step failed (a skipped
    RAC pass has no "ok"), and the time cap was not hit."""
    steps = report["steps"]
    return (all(steps.get(k, {}).get("ok") is True
                for k in ("1_normalise", "3_wp"))
            and not any(v.get("ok") is False for v in steps.values())
            and report.get("cap_hit") != "max_seconds")

TASK_HEAD = """\
# Annotate SOURCE.c so that WP proves every goal

SOURCE.c is a C benchmark (sglib's doubly linked list) with its frozen
specification: shape predicates and function contracts.  The goal is a
memory-safety certificate: every proof obligation of the functions
{functions}, and of every ACSL lemma, must be proved.  WP runs as
`frama-c -ariadne SOURCE.c -then -wp {wp} -wp-rte -rte-initialized @all`
(RTE: every memory access must be valid and every read initialised; the
-ariadne plugin adds `assert ariadne,live` before each access, the ghost
liveness model of ariadne_alloc.h).  Termination is not checked.

This is refinement iteration {iteration} of at most {cap}.

## Rules (checked before Frama-C sees your file; a violation rejects it)

- Change only ACSL annotations (`/*@ ... */`, `//@ ...`) and ghost code.
  The C code must stay byte-identical.
- Frozen: every function contract (the annotation just before a function)
  and every `predicate`, `logic`, `inductive`, `axiomatic` and `type`
  definition.  Do not change, remove or add any; in particular, give no
  contract to a function that has none.
- No `axiom`, `axiomatic`, `admit`, and no new definitions.
- Ghost code may only declare and assign ghost variables: no ghost loops,
  jumps, returns or calls, and never `__heap`.
- Allowed: `loop invariant`, `loop assigns`, `loop variant`, `assert`,
  statement contracts, ghost variables, and file-scope ACSL `lemma`s.
  Every annotation you add is itself a goal and must be proved.  A lemma
  is proved first by the SMT provers; one they cannot prove (induction
  over an inductive predicate or a list) goes to Coq provers, which
  usually succeed on small, well-stated lemmas.  Lemmas are available as
  hypotheses in every later goal.
- Your `wp` command uses 20 s per prover; the harness gives each goal
  60 s, so a goal that needs 20-60 s may still be proved.
"""


class Run:
    def __init__(self, a):
        self.a = a
        self.bench = os.path.abspath(a.bench)
        self.cfg = json.load(open(a.config))
        name = self.cfg["name"]
        stamp = time.strftime("%Y%m%d-%H%M%S")
        self.dir = os.path.abspath(a.run_dir or os.path.join(
            ARIADNE, "runs", f"{name}-{stamp}"))
        if not self.dir.startswith(ARIADNE + os.sep):
            sys.exit(f"run directory must be under {ARIADNE}")
        if os.path.exists(self.dir):
            sys.exit(f"{self.dir} exists")
        self.work = os.path.join(self.dir, "bench")
        self.logs = os.path.join(self.dir, "logs")
        self.start = time.time()
        self.containers = 0
        self.report = {"benchmark": self.bench, "config": a.config,
                       "run_dir": self.dir, "blank_coq": a.blank_coq,
                       "llm_calls": 0, "steps": {}, "guardrails": {}}
        self.tiers = {int(x) for x in a.tiers.split(",") if x.strip()}
        if a.no_tier0:
            self.tiers.discard(0)
        self.ledger = budget.Ledger(a.ledger)
        self.wp_prefix = {}  # goal file -> its context as WP wrote it
        self.goals = []
        self.certified = set()
        if a.functions:
            self.restrict(a.functions.split(","))
        self.annotator = None  # set in prepare (it needs the run dir)
        self.patches = 0  # accepted annotator patches
        self.history = []  # one line per refinement iteration, for TASK.md
        self.tried = {}  # goal -> its goal file's text when step 4 failed

    def restrict(self, fcts):
        """--functions: WP's selection cut down to these functions; the
        functions pass then needs at least their frozen-only goal count
        (config `function_goals`), and the lemma pass is kept."""
        known = self.cfg.get("function_goals", {})
        for p in self.cfg["passes"]:
            o = p["options"]
            if "-wp-fct" in o:
                k = o.index("-wp-fct") + 1
                sel = o[k].split(",")
                bad = [f for f in fcts if f not in sel]
                if bad:
                    sys.exit(f"--functions: not in the selection: {bad}")
                o[k] = ",".join(fcts)
                p["goals"] = {"min": sum(known.get(f, 0) for f in fcts)}
        self.report["functions"] = fcts

    # ---- helpers ------------------------------------------------------

    def log(self, msg):
        print(f"[{time.time() - self.start:7.1f}s] {msg}", flush=True)

    def left(self):
        """Seconds left under --max-seconds."""
        return self.a.max_seconds - (time.time() - self.start)

    def sh(self, cmd, cwd, log):
        """Run cmd (via ../env/run.sh when it starts with "image"), log
        its output; return the exit code (124 on timeout).  The time
        left under --max-seconds is its timeout; a container still
        running then is stopped by name."""
        env, name = None, None
        if cmd[0] == "image":
            cmd = [RUN] + cmd[1:]
            self.containers += 1
            name = f"ariadne-h-{os.getpid()}-{self.containers}"
            env = dict(os.environ, ARIADNE_NAME=name)
        with open(os.path.join(self.logs, log), "a") as fh:
            fh.write("$ " + " ".join(cmd) + "\n")
            fh.flush()
            try:
                return subprocess.run(cmd, cwd=cwd, stdout=fh,
                                      stderr=subprocess.STDOUT, env=env,
                                      timeout=max(1, self.left())
                                      ).returncode
            except subprocess.TimeoutExpired:
                fh.write("(timeout: --max-seconds used up)\n")
                self.report["cap_hit"] = "max_seconds"
                if name:
                    subprocess.run(["docker", "stop", "-t", "2", name],
                                   capture_output=True)
                return 124

    def step(self, name, fn):
        """Run one step, timed; its result goes into report["steps"]."""
        if self.left() <= 0:
            self.report["steps"][name] = {"skipped": "total time cap"}
            self.report["cap_hit"] = "max_seconds"
            return None
        self.log(f"step {name}")
        t = time.time()
        r = fn()
        r = r if isinstance(r, dict) else {"result": r}
        r["seconds"] = round(time.time() - t, 1)
        if name in self.report["steps"]:  # a repeated step (step 3 again)
            prev = self.report["steps"][name]
            r["seconds"] = round(r["seconds"] + prev["seconds"], 1)
            r["runs"] = prev.get("runs", 1) + 1
        self.report["steps"][name] = r
        self.log(f"step {name}: {r['seconds']} s")
        return r

    def guard(self, name, verdict):
        self.report["guardrails"][name] = verdict
        if not verdict["ok"]:
            self.log(f"GUARDRAIL FAILED: {name}: "
                     f"{json.dumps(verdict)[:300]}")
        return verdict["ok"]

    # ---- preparation and pre-checks ------------------------------------

    def prepare(self):
        os.makedirs(self.logs)
        pats = self.cfg.get("copy_ignore", [])

        def ignore(d, names):
            rel = os.path.relpath(d, self.bench)
            return {n for n in names
                    if any(fnmatch.fnmatch(n, p) or fnmatch.fnmatch(
                        os.path.normpath(os.path.join(rel, n)), p)
                        for p in pats)}
        shutil.copytree(self.bench, self.work, ignore=ignore)
        # The effective config (after --functions), for annotator_cli.py.
        self.cfg_path = os.path.join(self.dir, "config.json")
        with open(self.cfg_path, "w") as f:
            json.dump(self.cfg, f, indent=1)
        if self.a.annotator == "opus":
            self.annotator = annotator.Opus(
                os.path.join(self.dir, "annotator"), self.ledger,
                self.cfg_path, os.path.join(self.bench, self.cfg["source"]),
                calls=self.a.opus_wp_calls, turns=self.a.opus_turns,
                seconds=self.a.opus_seconds, usd=self.a.opus_usd,
                left=self.left)
        elif self.a.annotator.startswith("fake:"):
            # a JSON list of source files (null: return SOURCE.c unchanged)
            lst = self.a.annotator[5:]
            srcs = [x if x in (None, annotator.FENCED) else
                    open(os.path.join(os.path.dirname(lst), x)).read()
                    for x in json.load(open(lst))]
            self.annotator = annotator.Fake(
                os.path.join(self.dir, "annotator"), srcs)
        if self.a.overlay:  # an edited source, as the annotator would give
            shutil.copy(self.a.overlay,
                        os.path.join(self.work, self.cfg["source"]))
            self.report["overlay"] = os.path.abspath(self.a.overlay)
        inter = os.path.join(self.work, "session", "interactive")
        os.makedirs(inter, exist_ok=True)
        if self.a.blank_coq:
            dropped = sorted(f for f in os.listdir(inter)
                             if f.endswith(".v"))
            for f in dropped:
                os.remove(os.path.join(inter, f))
            self.report["dropped_coq_scripts"] = dropped
        # The RAC script reads the benchmark through an absolute path in
        # the image; point the copy's script at the copy.
        # With `source_line`, point its source variable at the config's
        # source (the annotator's patches are written there).
        rac = self.cfg.get("rac")
        if rac:
            script = next(c for c in rac["command"] if c.endswith(".sh"))
            p = os.path.join(self.work, rac["dir"], script)
            text = open(p).read()
            inner = "/ariadne/" + os.path.relpath(self.work, ARIADNE)
            lines = [(rac["bench_line"],
                      rac["bench_line"].split("=")[0] + "=" + inner)]
            if rac.get("source_line"):
                lines.append((rac["source_line"],
                              rac["source_line"].split("=")[0] + "=" + inner
                              + "/" + self.cfg["source"]))
            for old, new in lines:
                assert text.count(old) == 1, old
                text = text.replace(old, new)
            open(p, "w").write(text)

    def source(self, root):
        return open(os.path.join(root, self.cfg["source"])).read()

    def patch_checks(self, ed):
        """Guardrails 7.1-7.3a of a source against the benchmark's:
        {check: verdict}.  The textual checks first; Frama-C (the overlay
        check) only on a text that passed them."""
        base = self.source(self.bench)
        v = {"frozen_spec": guardrails.frozen(base, ed),
             "lint_acsl": guardrails.lint_acsl(base, ed),
             "lint_ghost": guardrails.lint_ghost(base, ed)}
        if all(x["ok"] for x in v.values()):
            v["overlay"] = guardrails.overlay(
                self.dir, base, ed, self.cfg["cpp_args"],
                os.path.join(self.logs, "overlay.log"))
        else:
            v["overlay"] = {"ok": False, "skipped": "a textual check failed"}
        return v

    def pre_checks(self):
        ok = True
        for k, v in self.patch_checks(self.source(self.work)).items():
            ok &= self.guard(k, v)
        return {"ok": ok}

    # ---- step 0: runtime checking --------------------------------------

    def rac(self):
        rac = self.cfg.get("rac")
        if not rac or self.a.no_rac:
            return {"skipped": "no RAC configured" if not rac else "--no-rac"}
        cwd = os.path.join(self.work, rac["dir"])
        rc = self.sh(["image"] + rac["command"], cwd, "step0_rac.log")
        lines = open(os.path.join(self.logs, "step0_rac.log")).read()
        passes = len(re.findall(r"^PASS", lines, re.M))
        fails = re.findall(r"^FAIL.*", lines, re.M)
        # The mutant table: "<mutant>  <sanitizers>  <E-ACSL>  [ok]".
        mutants = dict(re.findall(r"^(\w+) .*\[(\w+)\]\s*$", lines, re.M))
        return {"ok": rc == 0 and not fails, "exit": rc, "pass_lines":
                passes, "fail_lines": fails[:20], "mutants": mutants,
                "mutants_as_expected": sum(v == "ok"
                                           for v in mutants.values())}

    # ---- step 1: normalise and instrument ------------------------------

    def normalise(self):
        src = self.cfg["source"]
        out = src[:-2] + ".rte.c"
        rc = self.sh(["image", "frama-c"] + self.cfg["frama_c"] + [src]
                     + ["-then"] + self.cfg["rte"]
                     + ["-then", "-print", "-ocode", f"/work/{out}"],
                     self.work, "step1_normalise.log")
        ok = rc == 0 and os.path.exists(os.path.join(self.work, out))
        return {"ok": ok, "exit": rc, "output": f"bench/{out}"}

    # ---- step 3: WP ------------------------------------------------------

    def wp(self, mode):
        """One WP run per pass; `mode` is the -wp-interactive mode.
        Returns the goals of all passes."""
        goals, runs = [], []
        for p in self.cfg["passes"]:
            rep = f"report_{p['name']}.json"
            path = os.path.join(self.work, rep)
            if os.path.exists(path):
                os.remove(path)
            rc = self.sh(["image", "frama-c"] + self.cfg["frama_c"]
                         + [self.cfg["source"], "-then", "-wp"]
                         + self.cfg["wp"] + p["options"]
                         # the text of each open goal, for the annotator
                         + (["-wp-status"] if self.annotator else [])
                         + ["-wp-interactive", mode,
                            "-wp-interactive-timeout",
                            str(int(self.a.tactic_seconds) * 2),
                            "-wp-session", "/work/session",
                            "-wp-report-json", f"/work/{rep}"],
                         self.work, f"step3_wp_{p['name']}.log")
            n = 0
            if os.path.exists(path):
                for g in json.load(open(path)):
                    goals.append({
                        "goal": g["goal"], "pass": p["name"],
                        "function": g.get("function", "(lemma)"),
                        "property": g.get("property"),
                        "line": g.get("line"), "verdict": g["verdict"],
                        "discharger": discharger(g)})
                    n += 1
            # WP's cache (session/cache): "found:N" are reused results
            log = open(os.path.join(self.logs, f"step3_wp_{p['name']}.log")
                       ).read().rsplit("\n$ ", 1)[-1]
            cache = re.findall(r"\[Cache\] (.*)", log)
            runs.append({"pass": p["name"], "exit": rc, "goals": n,
                         "cache": cache[-1] if cache else None})
        # The context of every Coq goal file, as WP just wrote it.
        inter = os.path.join(self.work, "session", "interactive")
        for f in os.listdir(inter):
            if f.endswith(".v"):
                try:
                    self.wp_prefix[f] = split_goal(
                        open(os.path.join(inter, f)).read())[0]
                except SystemExit:
                    pass
        self.goals = goals
        return {"ok": all(r["exit"] == 0 for r in runs), "passes": runs,
                "mode": mode, "census": census(goals)}

    def open_goals(self):
        return [g for g in self.goals if g["discharger"] == "open"]

    def goal_file(self, goal):
        """WP's Coq goal file for a goal name (`typed_X` -> X.v)."""
        name = re.sub(r"^typed_", "", goal) + ".v"
        return os.path.join(self.work, "session", "interactive", name)

    # ---- step 4: proof search, tiers 0-2 ---------------------------------

    def model_tiers(self):
        """The tier-1 and tier-2 provers --tiers selects (tier 0 is run by
        search itself).  Each gets at most the time left."""
        out = []
        if 1 in self.tiers:
            out.append(tiers.Tier1(
                self.logs, self.a.glm_seconds, ledger=self.ledger,
                hide=tiers.hidden_paths(), keep=[self.work],
                left=self.left))
        if 2 in self.tiers:
            out.append(tiers.Tier2(
                os.path.join(self.dir, "tier2"), self.ledger,
                model=self.a.claude_model,
                calls=self.a.claude_calls, turns=self.a.claude_turns,
                seconds=self.a.claude_seconds, usd=self.a.claude_usd,
                left=self.left))
        return out

    def tier0(self, g, path, r, log):
        self.log(f"  tier 0: {g['goal']}")
        s = tier0.Search(path, min(self.a.goal_seconds, self.left()),
                         self.a.tactic_seconds)
        t = s.run()
        t["goal"] = g["goal"]
        log.append(t)
        r["seconds"] = t["seconds"]
        r["attempts"].append({"tier": 0, "status": t["status"],
                              "seconds": t["seconds"],
                              "candidates": len(t["tried"])})
        if t["status"] == "proved":
            s.apply(t["script"])
            r.update(status="proved", tier=0, model="tier0",
                     script=t["script"])
        self.log(f"  tier 0: {g['goal']}: {t['status']} ({t['seconds']} s)")

    def search(self):
        results, t0_log = [], []
        model_tiers = self.model_tiers()
        claude = any(t.tier >= 2 for t in model_tiers)
        b = self.budget_report()
        b.setdefault("start", self.ledger.summary())
        if claude and "weekly_usage_before" not in b:
            b["weekly_usage_before"] = budget.weekly_usage()
            self.ledger.record_reading(b["weekly_usage_before"],
                                       f"{self.dir}: before step 4")
        refused = False
        for g in [g for g in self.goals if g["discharger"] == "open"
                  and re.search(self.a.goals, g["goal"])
                  and (self.a.prove_scope == "all"
                       or g["pass"] == self.a.prove_scope)]:
            path = self.goal_file(g["goal"])
            if self.left() <= 0:
                self.report["cap_hit"] = "max_seconds"
                break
            if not os.path.exists(path):
                results.append({"goal": g["goal"], "status": "open",
                                "tier": None, "error": "no Coq goal file"})
                continue
            text = open(path).read()
            if self.tried.get(g["goal"]) == text:
                # the same goal file (context and statement) as a failed
                # earlier round: the tiers would see the same problem
                results.append({"goal": g["goal"], "status": "open",
                                "tier": None, "skipped":
                                "unchanged since a failed attempt",
                                "attempts": []})
                continue
            r = {"goal": g["goal"], "status": "open", "tier": None,
                 "model": None, "script": None, "seconds": 0.0,
                 "tokens": 0, "charged_tokens": 0, "usd": 0.0,
                 "attempts": []}
            if 0 in self.tiers:
                self.tier0(g, path, r, t0_log)
            todo = [t for t in model_tiers if not (refused and t.tier >= 2)]
            if r["status"] != "proved" and todo:
                self.log(f"  tiers {[t.tier for t in todo]}: {g['goal']}")
                c = tiers.chain(path, g["goal"], todo, tier0.coqc,
                                stop=lambda: self.left() <= 0)
                self.report["llm_calls"] += sum(
                    a["status"] != "refused" for a in c["attempts"])
                r["attempts"] += c["attempts"]
                r["seconds"] = round(r["seconds"] + c["seconds"], 1)
                r["tokens"] = c["tokens"]
                r["charged_tokens"] = c["charged_tokens"]
                r["usd"] = c["usd"]
                b["tokens_charged"] += c["charged_tokens"]
                b["usd_charged"] = round(b["usd_charged"] + c["usd"], 6)
                for a in c["attempts"]:
                    if a.get("warning"):
                        b["warnings"].append(
                            f"{g['goal']}: the ledger is at "
                            f"{a.get('pct_after')}% of the weekly limit "
                            f"(warning at {budget.WARN_PCT}%)")
                if c["status"] == "refused":
                    refused = True
                    self.report["cap_hit"] = "budget"
                    b["refused"].append({"goal": g["goal"],
                                         **c["attempts"][-1]["budget"]})
                if c["status"] == "proved":
                    r.update({k: c[k] for k in ("status", "tier", "model",
                                                "script")})
                self.log(f"  tiers: {g['goal']}: {r['status']}"
                         + (f" by tier {r['tier']}" if r["tier"] else "")
                         + f" ({r['seconds']} s, {r['tokens']} tokens)")
            if r["status"] != "proved" and not refused:
                self.tried[g["goal"]] = text
            results.append(r)
        if claude:
            b["weekly_usage_after"] = budget.weekly_usage()
            self.ledger.record_reading(b["weekly_usage_after"],
                                       f"{self.dir}: after step 4")
        b["end"] = self.ledger.summary()
        if not b["end"]["calibrated"]:
            b["note"] = (f"ledger not calibrated: placeholder "
                         f"{b['end']['pct_per_usd']}% of the weekly limit "
                         "per API-equivalent USD")
        for name, rows in (("step4_tier0.jsonl", t0_log),
                           ("step4_prove.jsonl", results)):
            with open(os.path.join(self.logs, name), "w") as f:
                for x in rows:
                    f.write(json.dumps(x) + "\n")
        by_tier = collections.Counter(r["tier"] for r in results
                                      if r["status"] == "proved")
        return {"tiers": sorted(self.tiers), "tried": len(results),
                "proved": sum(r["status"] == "proved" for r in results),
                "by_tier": {str(k): v for k, v in sorted(by_tier.items())},
                "refused": refused, "goals": results}

    def wp_confirm(self, step):
        """After step 3 again: did WP accept each proof step 4 found?"""
        dis = {g["goal"]: g["discharger"] for g in self.goals}
        for r in step["goals"]:
            if r["status"] == "proved":
                r["wp_confirmed"] = dis.get(r["goal"]) == "coq"

    # ---- step 5: refinement (the annotator) --------------------------------

    def stalls(self):
        out = []
        for g in [g for g in self.goals if g["discharger"] == "open"]:
            path = self.goal_file(g["goal"])
            state = None
            if os.path.exists(path):
                prefix = split_goal(open(path).read())[0]
                state = prefix[prefix.index("(* Why3 goal *)"):]
            out.append({"goal": g["goal"], "function": g["function"],
                        "line": g["line"], "property": g.get("property"),
                        "last_state": state})
        return out

    def refine(self):
        """On a stall, ask the annotator for a patch; a patch the
        guardrails or the runtime checks reject goes back to it with the
        reason (--annotator-retries times).  An accepted patch replaces
        the source of the copy: `edits` 1."""
        stalls = self.stalls()
        if not self.annotator:
            return {"stub": "no annotator: open goals are reported as "
                    "stalls and the loop ends", "stalls": stalls,
                    "edits": 0}
        current = self.source(self.work)
        offered, feedback, calls = current, None, []
        r = {"stalls": stalls, "edits": 0, "calls": calls}
        b = self.budget_report()
        tries, fence_retried = 1 + self.a.annotator_retries, False
        while len(calls) < tries:
            if self.left() <= 0:
                self.report["cap_hit"] = "max_seconds"
                break
            task = self.task(stalls, feedback)
            self.log(f"  annotator ({self.annotator.name}): "
                     f"{len(stalls)} open goals")
            c = self.annotator.run(offered, task)
            new = c.pop("source", None)
            calls.append(c)
            if c["status"] != "refused" and self.annotator.name != "fake":
                self.report["llm_calls"] += 1
            b["annotator_usd"] = round(b.get("annotator_usd", 0.0)
                                       + (c.get("usd") or 0.0), 6)
            b["tokens_charged"] += c.get("tokens") or 0
            b["usd_charged"] = round(b["usd_charged"] + (c.get("usd") or 0),
                                     6)
            if c.get("warning"):
                b["warnings"].append(f"annotator: the ledger is at "
                                     f"{c.get('pct_after')}% of the weekly "
                                     f"limit")
            if c["status"] == "refused":
                self.report["cap_hit"] = "budget"
                b["refused"].append({"goal": "(annotator)", **c["budget"]})
                break
            if c["status"] != "answered" or new is None or new == current:
                c["verdict"] = "no change"
                if c.get("permission_denials") and not fence_retried:
                    # a fence retry: the call ended after the fence refused
                    # a command, with no patch; once more, refusal named
                    fence_retried, tries = True, tries + 1
                    feedback = "FENCE:" + tiers.fence_note(c.get("denied"),
                                                           "SOURCE.c")
                    c["verdict"] = "no change after a refused command"
                    continue
                break
            v = self.patch_checks(new)
            c["guardrails"] = {k: x["ok"] for k, x in v.items()}
            if not all(x["ok"] for x in v.values()):
                c["verdict"] = "rejected by the guardrails"
                feedback = ("The guardrails rejected your patch; Frama-C "
                            "did not run on it.\n" + "\n".join(
                                annotator_cli.explain(v)))
                offered = new
                self.log("  annotator: patch rejected by the guardrails")
                continue
            # Step 0 again, on the patch (plan 5.0): a false annotation
            # is caught here with a concrete input.
            src = os.path.join(self.work, self.cfg["source"])
            open(src, "w").write(new)
            prev = dict(self.report["steps"].get("0_rac", {}))
            rac = self.step("0_rac", self.rac)
            kind = rac_outcome(rac)
            if kind != "pass":
                # step 0's verdict goes back to the last accepted state;
                # the outcome stays with the call
                c["rac"] = {k: rac.get(k) for k in ("exit", "fail_lines")}
                c["rac"]["outcome"] = kind
                detail = self.rac_failure(rac)
                if prev:
                    prev["seconds"] = rac["seconds"]
                    self.report["steps"]["0_rac"] = prev
            if kind == "false":
                open(src, "w").write(current)
                c["verdict"] = "rejected by the runtime checks"
                feedback = ("Your patch passed the guardrails, but a runtime "
                            "check (sanitizers and E-ACSL on random inputs) "
                            "fired, so an annotation is false or reads "
                            "memory it may not:\n" + detail)
                offered = new
                self.log("  annotator: patch rejected by runtime checks")
                continue
            if kind == "inconclusive":
                # The runtime-check tooling could not build the patch (as
                # gen_rac.py with ghost variables): testing is a filter
                # only (plan 5.0), so WP decides; the reason is reported.
                c["rac_note"] = ("step 0 inconclusive (" + detail[:300]
                                 + "); WP decides")
                self.log("  annotator: step 0 inconclusive (RAC build)")
            for k, x in v.items():
                self.guard(k, x)
            c["verdict"] = "accepted"
            r["edits"] = 1
            self.patches += 1
            with open(os.path.join(self.dir, f"patch{self.patches}.c"),
                      "w") as f:
                f.write(new)
            self.log("  annotator: patch accepted")
            break
        return r

    def rac_failure(self, rac):
        """The failing checks of a RAC run (its result), for feedback:
        the FAIL lines with what the script printed after them, and the
        end of E-ACSL's run log."""
        out = list(rac.get("fail_lines") or [])
        lines = open(os.path.join(self.logs, "step0_rac.log")).read() \
            .rsplit("\n$ ", 1)[-1].splitlines()
        k = next((i for i, x in enumerate(lines) if x.startswith("FAIL")),
                 None)
        if k is not None:
            out += lines[k + 1:k + 20]
        log = os.path.join(self.work, self.cfg["rac"]["dir"], "build",
                           "orig", "eacsl.log")
        if os.path.exists(log):
            text = open(log).read()
            out = out + text.splitlines()[-25:]
            if "RTE failed" in text:
                out.append(
                    "(An `RTE failed` check is about a term of an annotation "
                    "being unreadable when E-ACSL evaluates it.  E-ACSL "
                    "evaluates `\\at(e, Pre)` and `\\at(e, L)` when control "
                    "is at Pre or L, on every path, so e must be readable "
                    "there even on paths where the annotation is not "
                    "reached; e.g. `\\at((*list)->f, Pre)` fails when *list "
                    "is NULL at entry.  Guard the term, or name the value "
                    "with a ghost variable assigned on the path.)")
        return "\n".join(out)[-3000:]

    def budget_report(self):
        return self.report.setdefault("budget", {
            "ledger": self.ledger.path, "tokens_charged": 0,
            "usd_charged": 0.0, "warnings": [], "refused": []})

    def goal_texts(self):
        """WP's text of each open goal, from the last step-3 run's logs
        (-wp-status), by function: {function: [text]}."""
        out = collections.defaultdict(list)
        for p in self.cfg["passes"]:
            path = os.path.join(self.logs, f"step3_wp_{p['name']}.log")
            if not os.path.exists(path):
                continue
            last = open(path).read().rsplit("\n$ ", 1)[-1]
            for fct, _, body in annotator_cli.goal_blocks(last):
                out[fct].append(body)
        return out

    def task(self, stalls, feedback):
        """TASK.md for the annotator (plan 12.1)."""
        texts = self.goal_texts()
        by_fct = collections.defaultdict(list)
        for s in stalls:
            by_fct[s["function"]].append(s)
        proved = (self.report["steps"].get("4_prove") or {}).get("goals", [])
        reports = {g["goal"]: g for g in proved}
        sel = sorted(annotator_cli.selection(self.cfg))
        out = [TASK_HEAD.format(
            functions=", ".join(sel), wp=" ".join(self.cfg["wp"]),
            iteration=self.patches + 1, cap=self.a.max_iterations)]
        if feedback and feedback.startswith("FENCE:"):
            out += ["## Your previous call was stopped by the fence", "",
                    feedback[6:], ""]
        elif feedback:
            out += ["## Your previous patch was rejected", "",
                    "SOURCE.c is that patch; fix it.", "", "```",
                    feedback, "```", ""]
        out += ["## Open goals", "",
                f"{len(stalls)} goals are open after WP (Alt-Ergo, CVC5, "
                "Z3, 60 s each) and the prover tiers.  Grouped by function "
                "(its frozen contract is the annotation just above it in "
                "SOURCE.c) and source line (line numbers are those of "
                "SOURCE.c):", ""]
        for fct in sorted(by_fct):
            out.append(f"### {fct}")
            out.append("")
            for s in sorted(by_fct[fct], key=lambda s: (s["line"] or 0)):
                out.append(f"- line {s['line']}: `{s['goal']}`")
                rep = reports.get(s["goal"])
                if rep and rep.get("attempts"):
                    out.append("  prover tiers: " + "; ".join(
                        f"tier {a['tier']} {a['status']}"
                        + (f" ({a.get('end')})" if a.get("end") else "")
                        + (f": {a['answer'][-200:]!r}"
                           if a.get("answer") else "")
                        for a in rep["attempts"]))
                elif rep and rep.get("skipped"):
                    out.append(f"  prover tiers: skipped, {rep['skipped']}")
            out.append("")
            shown = texts.get(fct, [])
            if shown:
                out.append("WP's text of these goals:")
                out.append("")
                for body in shown[:10]:
                    b = body.splitlines()
                    if len(b) > 60:
                        b = b[:40] + ["  (...)"] + b[-15:]
                    out += ["```"] + b + ["```", ""]
                if len(shown) > 10:
                    out.append(f"({len(shown) - 10} more; run the `wp` "
                               "command to see them)")
                    out.append("")
        if self.history:
            out += ["## Earlier iterations", ""] + self.history + [""]
        return "\n".join(out)

    # ---- step 6: close out -------------------------------------------------

    def close_out(self):
        coq = [g for g in self.goals if g["discharger"] == "coq"]
        cert = os.path.join(self.dir, "cert")
        os.makedirs(cert, exist_ok=True)
        lint, modules, compiled = {}, {}, []
        for g in coq:
            path = self.goal_file(g["goal"])
            base = os.path.basename(path)
            if not os.path.exists(path):
                lint[g["goal"]] = {"ok": False, "error": "no goal file"}
                continue
            lint[g["goal"]] = guardrails.lint_coq(
                path, self.wp_prefix.get(base))
            mod = base[:-2]
            shutil.copy(path, os.path.join(cert, base))
            rc = self.sh(["image", "coqc"] + COQ_FLAGS
                         + ["-Q", ".", "Goals", base], cert,
                         "step6_coqc.log")
            if rc == 0:
                compiled.append(g["goal"])
                modules["Goals." + mod] = guardrails.wp_axioms(
                    split_goal(open(path).read())[0])
        self.guard("lint_coq", {"ok": all(v["ok"] for v in lint.values()),
                                "files": lint})
        r = {"coq_goals": len(coq), "coqc_ok": len(compiled)}
        if modules:
            rc = self.sh(["image", "coqchk", "-silent", "-o"]
                         + ["-R", WHY3, "Why3", "-Q", ".", "Goals"]
                         + sorted(modules), cert, "step6_coqchk.log")
            out = open(os.path.join(self.logs, "step6_coqchk.log")).read()
            axioms = guardrails.coqchk_axioms(out)
            r["coqchk_exit"] = rc
            if rc != 0 or axioms is None:
                self.guard("allow_list_coqchk", {"ok": False,
                                                 "error": "coqchk failed"})
            else:
                self.guard("allow_list_coqchk",
                           guardrails.allow_list(axioms, modules))
            r["print_assumptions"] = self.print_assumptions(cert, modules)
        self.certified = set(compiled) if modules or not coq else set()
        return r

    def print_assumptions(self, cert, modules):
        """`Print Assumptions wp_goal` for each module, its axioms checked
        against the same allow-list (names qualified by the module)."""
        bad, n = {}, 0
        for mod in sorted(modules):
            base = mod.split(".", 1)[1]
            pa = f"pa_{base}.v"
            text = open(os.path.join(cert, base + ".v")).read()
            with open(os.path.join(cert, pa), "w") as f:
                f.write(text + "\nPrint Assumptions wp_goal.\n")
            log = f"step6_print_assumptions_{base}.log"
            self.sh(["image", "coqc"] + COQ_FLAGS + [pa], cert, log)
            out = open(os.path.join(self.logs, log)).read()
            names = re.findall(r"^([A-Za-z_][\w'.]*) :", out.split(
                "Axioms:", 1)[-1], re.M) if "Axioms:" in out else None
            if names is None:
                bad[mod] = ["(no Axioms: section)"]
                continue
            n += len(names)
            # Names of the goal file itself come unqualified; Rocq's
            # come partly qualified (`Classical_Prop.classic`).
            qualified = [self.stdlib_name(x) if "." in x else f"{mod}.{x}"
                         for x in names]
            v = guardrails.allow_list(qualified, modules)
            if not v["ok"]:
                bad[mod] = v["not_allowed"]
        self.guard("allow_list_print_assumptions",
                   {"ok": not bad, "axioms": n, "not_allowed": bad})
        return {"modules": len(modules), "axioms": n}

    @staticmethod
    def stdlib_name(x):
        """A Print Assumptions name (partly qualified, e.g.
        `Classical_Prop.classic`) as its full allow-list name, if one
        ends with it."""
        for full in guardrails.ALLOWED_STDLIB:
            if full == x or full.endswith("." + x):
                return full
        return x

    # ---- the loop -------------------------------------------------------------

    def main(self):
        before = tree_hashes(self.bench)
        self.prepare()
        pre = self.step("guardrails_pre", self.pre_checks)
        if pre["ok"]:
            try:
                self.pipeline()
            except Exception as e:  # still a failure report, never a cert
                import traceback
                self.report["error"] = traceback.format_exc()[-3000:]
                self.report["steps"]["pipeline"] = {"ok": False,
                                                    "error": repr(e)}
                self.log(f"ERROR: {e!r}")
        else:  # plan 7.1: reject the edit before any tool sees it
            self.report["stopped"] = "guardrails failed before step 0"
        self.step("6_close_out", self.close_out)
        self.verdict(before)
        self.write()
        return 0 if self.report["verdict"] == "certified" else 1

    def pipeline(self):
        """Steps 0-5, with the refinement loop and its caps."""
        self.step("0_rac", self.rac)
        self.step("1_normalise", self.normalise)
        self.report["steps"]["2_eva"] = {"skipped": "optional (plan 5.2)"}
        r = self.step("3_wp", lambda: self.wp("update"))
        self.report["census_after_wp"] = r["census"] if r else None
        iterations = 0
        while r is not None and self.open_goals():
            if self.tiers:
                s = self.step("4_prove", self.search)
                if s and s["proved"]:
                    r = self.step("3_wp", lambda: self.wp("batch"))
                    self.wp_confirm(s)
            if r is None or not self.open_goals():
                break
            if iterations >= self.a.max_iterations:
                self.report["cap_hit"] = "max_iterations"
                break
            before = len(self.open_goals())
            f = self.step("5_refine", self.refine)
            iterations += 1
            if f is not None:
                self.report.setdefault("refinement", []).append(
                    {"iteration": iterations, "edits": f["edits"],
                     "open_before": before, "calls": f.get("calls", [])})
            if f is None or not f["edits"]:
                break  # a stall: another round would change nothing
            self.step("1_normalise", self.normalise)
            r = self.step("3_wp", lambda: self.wp("update"))
            if r is not None:
                c = r["census"]
                self.report["refinement"][-1]["census_after"] = c
                self.history.append(
                    f"- iteration {iterations}: your patch was accepted; "
                    f"open goals {before} before it, {c['open']} after WP "
                    f"({c['goals']} goals in all, {c['qed']} by Qed, "
                    f"{c['smt']} by SMT, {c['coq']} by Coq).")
        self.report["refinement_iterations"] = iterations

    # ---- step 7: verdict and report --------------------------------------

    def verdict(self, before):
        goals = getattr(self, "goals", [])
        after = tree_hashes(self.bench)
        changed = sorted(k for k in set(before) | set(after)
                         if before.get(k) != after.get(k))
        self.guard("benchmark_untouched", {"ok": not changed,
                                           "changed": changed})
        self.guard("goal_accounting", guardrails.accounting(
            goals, {p["name"]: p["goals"] for p in self.cfg["passes"]},
            self.cfg.get("out_of_scope", []), self.certified))
        g_ok = all(v["ok"] for v in self.report["guardrails"].values())
        steps_ok = steps_succeeded(self.report)
        self.report["census"] = census(goals)
        self.report["goals"] = goals
        self.report["seconds"] = round(time.time() - self.start, 1)
        if g_ok and steps_ok:
            self.report["verdict"] = "certified"
        else:
            self.report["verdict"] = "failed"
            self.report["failure"] = {
                "guardrails_failed": sorted(
                    k for k, v in self.report["guardrails"].items()
                    if not v["ok"]),
                "steps_failed": [k for k, v in self.report["steps"].items()
                                 if v.get("ok") is False],
                "open_goals": self.report["steps"].get("5_refine", {})
                .get("stalls", [g for g in goals
                                if g["discharger"] == "open"])}
            # Never a partial certificate (plan 5.7).
            shutil.rmtree(os.path.join(self.dir, "cert"),
                          ignore_errors=True)

    def write(self):
        with open(os.path.join(self.dir, "report.json"), "w") as f:
            json.dump(self.report, f, indent=1)
        with open(os.path.join(self.dir, "report.md"), "w") as f:
            f.write(markdown(self.report))
        self.log(f"verdict: {self.report['verdict']}; "
                 f"{self.dir}/report.md")


def markdown(r):
    c = r["census"]
    w = r.get("census_after_wp") or {}
    out = [f"# Ariadne run: {os.path.basename(r['benchmark'])}"
           f"{' (Coq scripts dropped)' if r['blank_coq'] else ''}", "",
           f"**Verdict: {r['verdict']}.**  {c['proved']} / {c['goals']} "
           f"goals proved; {r['seconds']} s; model runs: {r['llm_calls']}.",
           "", "## Goal census", "",
           "| Discharger | after step 3 | final |", "|---|---|---|"]
    for k in ("qed", "smt", "coq", "open"):
        out.append(f"| {k} | {w.get(k, '')} | {c[k]} |")
    out.append(f"| total | {w.get('goals', '')} | {c['goals']} |")
    if c["smt_by_prover"]:
        out += ["", "SMT by prover: " + ", ".join(
            f"{k} {v}" for k, v in c["smt_by_prover"].items()) + "."]
    out += ["", "## Steps", "", "| Step | Seconds | Result |",
            "|---|---|---|"]
    for k, v in r["steps"].items():
        res = ("skipped: " + v["skipped"]) if "skipped" in v else \
            ", ".join(f"{a}={b}" for a, b in v.items()
                      if a in ("ok", "proved", "tried", "coq_goals",
                               "coqc_ok", "pass_lines", "mutants_as_expected",
                               "runs", "edits"))
        out.append(f"| {k} | {v.get('seconds', '')} | {res} |")
    out += ["", "## Guardrails", "", "| Check | Verdict |", "|---|---|"]
    for k, v in r["guardrails"].items():
        out.append(f"| {k} | {'pass' if v['ok'] else 'FAIL'} |")
    pr = r["steps"].get("4_prove")
    if pr:
        out += ["", f"## Proof search (tiers {pr['tiers']})", "",
                "| Goal | Proved by | Seconds | Tokens | USD charged | "
                "Attempts (tier: result) |", "|---|---|---|---|---|---|"]
        for g in pr["goals"]:
            by = (f"tier {g['tier']} ({g['model']})"
                  if g["status"] == "proved" else g["status"])
            if g.get("wp_confirmed") is False:
                by += ", NOT confirmed by WP"
            att = "; ".join(
                f"{a['tier']}: {a['status']} {a.get('seconds', '')} s"
                + (f", {a['tokens']} tok" if a.get("tokens") else "")
                for a in g.get("attempts", []))
            out.append(f"| `{g['goal']}` | {by} | {g.get('seconds', '')} | "
                       f"{g.get('tokens', 0)} | {g.get('usd', 0)} | {att} |")
    if r.get("refinement"):
        out += ["", "## Refinement (step 5)", "",
                "| Iteration | Call | Verdict | Turns | wp calls | "
                "Seconds | USD | Open after |", "|---|---|---|---|---|---|---|---|"]
        for it in r["refinement"]:
            after = (it.get("census_after") or {}).get("open", "")
            for c in it["calls"]:
                out.append(
                    f"| {it['iteration']} | {c['annotator']} #{c['call']} | "
                    f"{c.get('verdict', c['status'])} | {c.get('turns', '')} "
                    f"| {(c.get('cli_calls') or {}).get('wp', '')} | "
                    f"{c.get('seconds', '')} | {c.get('usd', 0)} | "
                    f"{after if c.get('verdict') == 'accepted' else ''} |")
    b = r.get("budget")
    if b:
        e = b.get("end", {})
        wb = (b.get("weekly_usage_before") or {}).get("pct")
        wa = (b.get("weekly_usage_after") or {}).get("pct")
        out += ["", "## Budget", "",
                f"Anthropic use charged this run: ${b['usd_charged']} "
                f"(API-equivalent), {b['tokens_charged']} tokens.  Ledger "
                f"this week: ${e.get('usd')}, {e.get('pct')}% of the weekly "
                f"limit (cap {e.get('cap_pct')}%, warning "
                f"{e.get('warn_pct')}%), "
                + ("calibrated" if e.get("calibrated") else
                   f"**uncalibrated** (placeholder {e.get('pct_per_usd')}% "
                   "per USD)") + "."
                + (f"  `/usage` weekly (all Claude Code use): {wb}% before, "
                   f"{wa}% after." if wb is not None else "")]
        out += [f"- **Warning:** {w}" for w in b.get("warnings", [])]
        out += [f"- **Refused:** `{x['goal']}`: {x['projected_pct']}% would "
                f"pass the {x['cap_pct']}% cap" for x in b.get("refused", [])]
    coq = [g for g in r["goals"] if g["discharger"] in ("coq", "open")]
    if coq:
        out += ["", "## Goals not closed by Qed or SMT", ""]
        out += [f"- `{g['goal']}` (line {g['line']}): {g['discharger']}"
                for g in coq]
    if r["verdict"] != "certified":
        f = r["failure"]
        stopped = f"Stopped: {r['stopped']}.  " if r.get("stopped") else ""
        out += ["", "## Failure report", "",
                f"{stopped}Guardrails failed: {', '.join(f['guardrails_failed']) or 'none'}."
                f"  Steps failed: {', '.join(f['steps_failed']) or 'none'}."
                f"  Open goals: {len(f['open_goals'])} (last states in "
                "report.json).  No certificate was produced."]
    return "\n".join(out) + "\n"


def main():
    ap = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    ap.add_argument("bench")
    ap.add_argument("--config", default=os.path.join(HERE, "b1.json"))
    ap.add_argument("--run-dir")
    ap.add_argument("--blank-coq", action="store_true")
    ap.add_argument("--overlay", help="an edited copy of the benchmark's "
                    "source to run instead of it (checked by the "
                    "guardrails against the benchmark's)")
    ap.add_argument("--no-rac", action="store_true")
    ap.add_argument("--no-tier0", action="store_true",
                    help="drop tier 0 from --tiers")
    ap.add_argument("--tiers", default="0,2",
                    help="prover tiers for step 4 (0 tier0.py, 1 GLM, "
                    "2 --claude-model; plan Q9: 0,2); empty for none")
    ap.add_argument("--goal-seconds", type=float, default=300,
                    help="tier 0: seconds per goal")
    ap.add_argument("--tactic-seconds", type=float, default=60)
    ap.add_argument("--glm-seconds", type=int, default=120,
                    help="tier 1: working time per goal")
    ap.add_argument("--claude-model", default=tiers.OPUS,
                    help="tier 2: the Claude model")
    ap.add_argument("--claude-calls", type=int, default=30,
                    help="tier 2: prover_cli goals/check calls per goal")
    ap.add_argument("--claude-turns", type=int, default=60,
                    help="tier 2: Claude Code turns per goal")
    ap.add_argument("--claude-seconds", type=int, default=600,
                    help="tier 2: wall clock per goal")
    ap.add_argument("--claude-usd", type=float, default=1.0,
                    help="tier 2: --max-budget-usd per goal (API-"
                    "equivalent), also what the ledger reserves")
    ap.add_argument("--ledger", default=budget.PATH)
    ap.add_argument("--goals", default="",
                    help="step 4 only on the open goals whose name "
                    "matches this regex (default: all)")
    ap.add_argument("--prove-scope", default="all",
                    choices=["all", "functions", "lemmas"],
                    help="step 4 only on the open goals of this pass "
                    "(lemmas: function goals go straight to the annotator)")
    ap.add_argument("--functions", default="",
                    help="WP's selection cut down to these functions "
                    "(comma-separated)")
    ap.add_argument("--annotator", default="none",
                    help="step 5: none, opus, or fake:LIST.json (a JSON "
                    "list of source files, relative to it, returned in "
                    "turn; null returns SOURCE.c unchanged)")
    ap.add_argument("--annotator-retries", type=int, default=2,
                    help="step 5: rejected patches sent back per iteration")
    ap.add_argument("--opus-usd", type=float, default=5.0,
                    help="annotator: --max-budget-usd per call (API-"
                    "equivalent), also what the ledger reserves")
    ap.add_argument("--opus-turns", type=int, default=80)
    ap.add_argument("--opus-seconds", type=int, default=1800)
    ap.add_argument("--opus-wp-calls", type=int, default=12,
                    help="annotator: annotator_cli.py wp calls per call")
    ap.add_argument("--max-iterations", type=int, default=1,
                    help="refinement iterations (annotator patches)")
    ap.add_argument("--max-seconds", type=float, default=3600)
    sys.exit(Run(ap.parse_args()).main())


if __name__ == "__main__":
    main()
