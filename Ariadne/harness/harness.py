#!/usr/bin/env python3
"""The Ariadne pipeline without an LLM (plan section 5, steps 0-7;
milestone M2): runtime checks, Frama-C/WP, tier-0 proof search, close
out with coqc / coqchk / Print Assumptions, guardrails, and a report.

    python3 harness.py ../bench/b1 [--config b1.json] [--run-dir DIR]
        [--blank-coq] [--overlay EDITED.c] [--no-rac] [--no-tier0]
        [--goal-seconds 300]
        [--tactic-seconds 60] [--max-iterations 1] [--max-seconds 3600]

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
  4  tier-0 search (tier0.py) on each open goal, then step 3 again if it
     closed any;
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
import tier0  # noqa: E402
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



def steps_succeeded(report):
    """Normalisation and WP ran and succeeded, no step failed (a skipped
    RAC pass has no "ok"), and the time cap was not hit."""
    steps = report["steps"]
    return (all(steps.get(k, {}).get("ok") is True
                for k in ("1_normalise", "3_wp"))
            and not any(v.get("ok") is False for v in steps.values())
            and report.get("cap_hit") != "max_seconds")

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
        self.wp_prefix = {}  # goal file -> its context as WP wrote it
        self.goals = []
        self.certified = set()

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
        rac = self.cfg.get("rac")
        if rac:
            p = os.path.join(self.work, rac["dir"], rac["command"][-1])
            text = open(p).read()
            inner = "/ariadne/" + os.path.relpath(self.work, ARIADNE)
            assert text.count(rac["bench_line"]) == 1, rac["bench_line"]
            open(p, "w").write(text.replace(
                rac["bench_line"],
                rac["bench_line"].split("=")[0] + "=" + inner))

    def source(self, root):
        return open(os.path.join(root, self.cfg["source"])).read()

    def pre_checks(self):
        base, ed = self.source(self.bench), self.source(self.work)
        ok = self.guard("overlay", guardrails.overlay(
            self.dir, base, ed, self.cfg["cpp_args"],
            os.path.join(self.logs, "overlay.log")))
        ok &= self.guard("frozen_spec", guardrails.frozen(base, ed))
        ok &= self.guard("lint_acsl", guardrails.lint_acsl(base, ed))
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
            runs.append({"pass": p["name"], "exit": rc, "goals": n})
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

    # ---- step 4: tier-0 proof search -------------------------------------

    def search(self):
        results = []
        for g in [g for g in self.goals if g["discharger"] == "open"]:
            path = self.goal_file(g["goal"])
            if self.left() <= 0:
                self.report["cap_hit"] = "max_seconds"
                break
            if not os.path.exists(path):
                results.append({"goal": g["goal"], "status": "open",
                                "error": "no Coq goal file"})
                continue
            self.log(f"  tier 0: {g['goal']}")
            s = tier0.Search(path, min(self.a.goal_seconds, self.left()),
                             self.a.tactic_seconds)
            r = s.run()
            r["goal"] = g["goal"]
            if r["status"] == "proved":
                s.apply(r["script"])
            results.append(r)
            self.log(f"  tier 0: {g['goal']}: {r['status']} "
                     f"({r['seconds']} s)")
        with open(os.path.join(self.logs, "step4_tier0.jsonl"), "w") as f:
            for r in results:
                f.write(json.dumps(r) + "\n")
        return {"tried": len(results),
                "proved": sum(r["status"] == "proved" for r in results),
                "goals": [{k: r.get(k) for k in
                           ("goal", "status", "script", "seconds", "error")}
                          for r in results]}

    # ---- step 5: refinement (stub) ----------------------------------------

    def refine(self):
        stalls = []
        for g in [g for g in self.goals if g["discharger"] == "open"]:
            path = self.goal_file(g["goal"])
            state = None
            if os.path.exists(path):
                prefix = split_goal(open(path).read())[0]
                state = prefix[prefix.index("(* Why3 goal *)"):]
            stalls.append({"goal": g["goal"], "function": g["function"],
                           "line": g["line"], "last_state": state})
        return {"stub": "no annotator in M2: open goals are reported as "
                "stalls and the loop ends", "stalls": stalls,
                "edits": 0}

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
            self.pipeline()
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
            if not self.a.no_tier0:
                s = self.step("4_tier0", self.search)
                if s and s["proved"]:
                    r = self.step("3_wp", lambda: self.wp("batch"))
            if r is None or not self.open_goals():
                break
            f = self.step("5_refine", self.refine)
            iterations += 1
            if f is None or not f["edits"]:
                break  # a stall: another round would change nothing
            if iterations >= self.a.max_iterations:
                self.report["cap_hit"] = "max_iterations"
                break
            r = self.step("3_wp", lambda: self.wp("update"))
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
    out = [f"# Ariadne M2 run: {os.path.basename(r['benchmark'])}"
           f"{' (Coq scripts dropped)' if r['blank_coq'] else ''}", "",
           f"**Verdict: {r['verdict']}.**  {c['proved']} / {c['goals']} "
           f"goals proved; {r['seconds']} s; LLM calls: {r['llm_calls']}.",
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
    t0 = r["steps"].get("4_tier0")
    if t0:
        out += ["", "## Tier-0 search", "", "| Goal | Result | Seconds | "
                "Script |", "|---|---|---|---|"]
        for g in t0["goals"]:
            out.append(f"| `{g['goal']}` | {g['status']} | "
                       f"{g.get('seconds', '')} | "
                       f"{('`' + g['script'] + '`') if g.get('script') else ''}"
                       " |")
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
    ap.add_argument("--no-tier0", action="store_true")
    ap.add_argument("--goal-seconds", type=float, default=300)
    ap.add_argument("--tactic-seconds", type=float, default=60)
    ap.add_argument("--max-iterations", type=int, default=1)
    ap.add_argument("--max-seconds", type=float, default=3600)
    sys.exit(Run(ap.parse_args()).main())


if __name__ == "__main__":
    main()
