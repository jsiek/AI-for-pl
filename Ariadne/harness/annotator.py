"""The annotator of step 5 (plan sections 5 and 12.1): Claude Opus 5.5 as
headless Claude Code, billed to the owner's subscription and charged to
the budget ledger's `annotator` role.

One call gets its own directory holding

  SOURCE.c          the current annotated source (the file it edits),
  TASK.md           what to do: the functions with open goals, their
                    frozen contracts, the open goals grouped by function
                    and source line with WP's goal text, step 4's prover
                    reports, and the reason a previous patch was rejected,
  ariadne_alloc.h   the ghost liveness model (frozen, for reference),

and may run only `annotator_cli.py check|wp SOURCE.c ...` (guardrails,
then WP with the SMT provers) and Read/Write/Edit in that directory.  No
git, no other files: the benchmark's own annotated b1.c and the
repository history hold the human's invariants.  Its output is the
SOURCE.c it leaves: the patch, which the harness checks with the
guardrails before Frama-C sees it.

`Fake` replays a fixed list of sources instead, for the offline tests.
"""
import json
import os
import shutil
import subprocess
import sys
import time

HERE = os.path.dirname(os.path.abspath(__file__))
ARIADNE = os.path.dirname(HERE)
sys.path.insert(0, HERE)
import budget  # noqa: E402

CLI = os.path.join(HERE, "annotator_cli.py")
OPUS = "claude-opus-5-5"
ALLOC_H = os.path.join(ARIADNE, "plugin", "share", "ariadne_alloc.h")

PROMPT = """\
You are the annotator of a proof pipeline for memory safety of C code
(Frama-C 31 / WP, Typed model, RTE with initialisation checks, and the
`-ariadne` ghost liveness model).  Read TASK.md in this directory first:
it lists the functions with open proof goals, the goals with WP's text,
and the rules.  Then edit SOURCE.c, adding ACSL annotations only (loop
invariants, loop assigns, asserts, ghost code, lemmas), until WP proves
the goals.  Commands (nothing else is allowed):

  python3 {cli} check SOURCE.c           (guardrails only, fast)
  python3 {cli} wp SOURCE.c FUNCTION     (guardrails, then WP with the
                                         SMT provers on one function, or
                                         `lemmas` for the ACSL lemmas)

You have {calls} `wp` calls in all.  Read/Write/Edit only files in this
directory.  When done, answer with one line: DONE, or GAVE UP followed
by what blocks you.
"""


def opus_command(work, model=OPUS, calls=12, turns=80, usd=5.0):
    """The `claude -p` command line for one annotator call in `work`,
    fenced as tiers.sonnet_command fences the prover."""
    rule = f"python3 {CLI}"
    allowed = [f"Bash({rule} check SOURCE.c)",
               f"Bash({rule} wp SOURCE.c *)",
               f"Read(/{work}/**)", f"Write(/{work}/**)",
               f"Edit(/{work}/**)"]
    return ["claude", "-p", PROMPT.format(cli=CLI, calls=calls),
            "--model", model, "--output-format", "json",
            "--max-turns", str(turns), "--max-budget-usd", str(usd),
            "--no-session-persistence", "--safe-mode", "--restricted",
            "--strict-mcp-config", "--disable-slash-commands",
            "--tools", "Bash,Read,Write,Edit",
            "--allowedTools", *allowed,
            "--disallowedTools", "Bash(git *)", "Bash(git)",
            "--permission-mode", "dontAsk"]


def opus_env(work, cfg_path, baseline, calls, wp_timeout):
    return dict(os.environ, ANNOTATOR_CONFIG=cfg_path,
                ANNOTATOR_BASELINE=baseline,
                ANNOTATOR_SCRATCH=os.path.join(os.path.dirname(work),
                                               os.path.basename(work)
                                               + ".scratch"),
                ANNOTATOR_LOG=os.path.join(work, "calls.jsonl"),
                ANNOTATOR_MAX_CALLS=str(calls),
                ANNOTATOR_WP_TIMEOUT=str(wp_timeout),
                GIT_CEILING_DIRECTORIES=os.path.dirname(work),
                GIT_DIR=os.path.join(work, ".no-git"))


def prepare(work, source, task):
    os.makedirs(work)
    open(os.path.join(work, "SOURCE.c"), "w").write(source)
    open(os.path.join(work, "TASK.md"), "w").write(task)
    shutil.copy(ALLOC_H, os.path.join(work, "ariadne_alloc.h"))


class Opus:
    """Opus 5.5 through `claude -p`, within the ledger."""
    name = "opus"

    def __init__(self, root, ledger, cfg_path, baseline, model=OPUS,
                 calls=12, turns=80, seconds=1800, usd=5.0, wp_timeout=20,
                 left=lambda: 1e9):
        self.root, self.ledger, self.model = root, ledger, model
        self.cfg_path, self.baseline = cfg_path, baseline
        self.calls, self.turns, self.seconds = calls, turns, seconds
        self.usd, self.wp_timeout, self.left = usd, wp_timeout, left
        self.n = 0

    def run(self, source, task):
        """One call: {status, source, usd, tokens, ...}; status is
        `answered`, `refused` (budget) or an error."""
        self.n += 1
        t = time.time()
        res = {"annotator": self.model, "call": self.n}
        gate = self.ledger.reserve("annotator", self.model, self.usd)
        res["budget"] = gate
        if not gate["ok"]:
            res.update(status="refused", source=None, seconds=0.0, usd=0.0,
                       tokens=0, error=f"budget: {gate['projected_pct']}% "
                       f"would pass the {gate['cap_pct']}% cap")
            return res
        try:
            return self._run(source, task, t, res, gate["id"])
        except BaseException:
            self.ledger.release(gate["id"])
            raise

    def _run(self, source, task, t, res, reservation):
        work = os.path.join(self.root, f"call{self.n}")
        prepare(work, source, task)
        env = opus_env(work, self.cfg_path, self.baseline, self.calls,
                       self.wp_timeout)
        cmd = opus_command(work, self.model, self.calls, self.turns,
                           self.usd)
        out = None
        try:
            p = subprocess.run(cmd, cwd=work, env=env, capture_output=True,
                               text=True, timeout=max(1, min(
                                   self.seconds, self.left())),
                               stdin=subprocess.DEVNULL)
            open(os.path.join(work, "result.json"), "w").write(p.stdout)
            if p.stderr:
                open(os.path.join(work, "stderr.txt"), "w").write(p.stderr)
            out = json.loads(p.stdout)
            res["end"] = out.get("subtype")
        except subprocess.TimeoutExpired:
            res["end"] = "timeout"
        except ValueError:
            res["end"] = "no JSON result"
        mu = budget.by_model(out, self.model) if out else {}
        c = self.ledger.charge("annotator", mu, est_usd=self.usd,
                               model=self.model, reservation=reservation)
        res.update(tokens=c["tokens"], usd=c["usd"], pct_after=c["pct"],
                   warning=c["warning"], estimated=not mu, usage=mu)
        if out:
            res.update(turns=out.get("num_turns"),
                       answer=(out.get("result") or "")[-600:],
                       permission_denials=len(
                           out.get("permission_denials") or []))
        res["cli_calls"] = cli_calls(os.path.join(work, "calls.jsonl"))
        res.update(status="answered",
                   source=open(os.path.join(work, "SOURCE.c")).read(),
                   seconds=round(time.time() - t, 1))
        return res


def cli_calls(path):
    log = [json.loads(x) for x in open(path)] if os.path.exists(path) \
        else []
    return {"wp": sum(c["cmd"] == "wp" for c in log),
            "check": sum(c["cmd"] == "check" for c in log),
            "last_wp_open": next((c.get("open") for c in reversed(log)
                                  if c["cmd"] == "wp" and "open" in c),
                                 None)}


class Fake:
    """Replays `sources` (texts, or None for "return SOURCE.c unchanged")
    in order, then returns the input unchanged: an annotator that stalls.
    Records the tasks it was given."""
    name = "fake"

    def __init__(self, root, sources):
        self.root, self.sources, self.tasks = root, list(sources), []

    def run(self, source, task):
        self.tasks.append(task)
        work = os.path.join(self.root, f"call{len(self.tasks)}")
        prepare(work, source, task)
        new = self.sources.pop(0) if self.sources else None
        return {"annotator": "fake", "call": len(self.tasks),
                "status": "answered", "source": source if new is None
                else new, "usd": 0.0, "tokens": 0, "seconds": 0.0}
