#!/usr/bin/env python3
"""Tier-0 proof search (plan section 12.2, tier 0; section 5 step 4):
no model, only `hammer`, `sauto` and a small fixed list of tactic
combinations, tried one at a time through Pétanque on a WP goal file
(session/interactive/*.v), with a time cap per tactic and per goal.
coqc gives the verdict.

    python3 tier0.py GOAL.v [GOAL2.v ...] [--goal-seconds 300]
        [--tactic-seconds 60] [--apply] [--json out.jsonl]

The search starts from the statement (`wp_goal` right after its
`Theorem`), so whatever script the file holds is ignored: started on a
stub WP wrote, or on a file with a proof, it searches from a blank
proof.  A candidate is a whole script; the first one Pétanque finishes
is checked by coqc (whole file, the script between `Proof.` and
`Qed.`) and, with --apply, written into the file.  When `hammer`
succeeds, the tactic it reconstructs (`srun ...`, `sauto ...`) is
tried first in the coqc check, since it needs no ATP and is faster;
`hammer` itself is the fallback.

One JSON object per goal goes to stdout (and to --json): status
(`proved` / `open`), the script, the candidates tried with their
outcome and seconds, and the total seconds.
"""
import argparse
import json
import os
import re
import subprocess
import sys
import tempfile
import time

HERE = os.path.dirname(os.path.abspath(__file__))
ARIADNE = os.path.dirname(HERE)
sys.path.insert(0, os.path.join(ARIADNE, "prover"))
from petanque import Petanque, PetanqueError, PetanqueTimeout  # noqa: E402
from reallms_coq import FORBIDDEN, split_goal  # noqa: E402

RUN = os.path.join(ARIADNE, "env", "run.sh")
COQC = ("coqc -native-compiler no "
        "-R /home/rocq/.opam/4.14.2/lib/why3/coq Why3")


def binders(statement):
    """(name, type) of the statement's leading `forall` binders, in
    order; `(x y:T)` gives two."""
    m = re.match(r"\s*Theorem wp_goal\s*:\s*forall\s+(.*?),\s",
                 statement, re.S)
    if not m:
        return []
    out = []
    for names, ty in re.findall(r"\(([^():]+):([^()]*(?:\([^()]*\)[^()]*)*)\)",
                                m.group(1)):
        for n in names.split():
            out.append((n, " ".join(ty.split())))
    return out


def premises(statement):
    """Number of top-level `->` premises after the binders (an upper
    bound: arrows inside parentheses are not counted)."""
    body = statement.split(",", 1)[1] if "forall" in statement else statement
    depth, n = 0, 0
    for i, c in enumerate(body):
        depth += c == "("
        depth -= c == ")"
        if not depth and body.startswith("->", i) and body[i - 1] != "<":
            n += 1
    return n


def definitions(prefix, statement):
    """Names of the transparent definitions of the context (`Definition`
    or `Fixpoint`) that the statement mentions, in order."""
    defined = re.findall(r"^(?:Definition|Fixpoint)\s+([A-Za-z_][\w']*)",
                         prefix, re.M)
    return [d for d in dict.fromkeys(defined)
            if re.search(rf"\b{re.escape(d)}\b", statement)]


# Library lemmas given to `sauto use:` when the context has them: Why3's
# list theory, as WP exports it (`nth` and `length` are axiomatised by
# conditional lemmas, which hammer's premise selection often misses).
# A fixed list, the same for every goal.
LIBRARY = ("nth_zero", "nth_cons", "length_cons", "length_pos",
           "length_nil")


def candidates(prefix, statement):
    """The fixed list of tactic combinations, instantiated for this goal:
    the names unfolded and the variables and premises inducted on come
    from the statement, the library lemmas from the context."""
    iff = "<->" in statement
    lib = [x for x in LIBRARY
           if re.search(rf"^Axiom {x}\b", prefix, re.M)]
    use = f"sauto use: {', '.join(lib)}" if lib else "sauto"
    out = ["sauto.", "hammer.", "intros; firstorder.", "intros; lia.",
           "intuition auto."]
    if iff:
        out += ["intros; split; intros; sauto.",
                "intros; split; intros; hammer."]
    defs = definitions(prefix, statement)
    if defs:
        u = f"intros; unfold {', '.join(defs)} in *"
        out += [f"{u}; sauto.", f"{u}; hammer.", f"{u}; firstorder."]
        if lib:
            out += [f"{u}; {use}."]
        if iff:
            out += [f"{u}; split; intros; hammer."]
            if lib:
                out += [f"{u}; split; intros; {use}."]
    for name, ty in binders(statement):
        if ty.startswith(("Init.Datatypes.list", "list")):
            out += [f"induction {name}; sauto.",
                    f"induction {name}; hammer."]
    for k in range(1, min(premises(statement), 3) + 1):
        out += [f"induction {k}; sauto.", f"induction {k}; hammer."]
        if lib:
            out += [f"induction {k}; {use}."]
    return out


def coqc(prefix, script, suffix, timeout):
    """(ok, output) of coqc on the goal file with `script` as proof."""
    d = tempfile.mkdtemp(dir=os.path.join(ARIADNE, "runs"), prefix="coqc_")
    try:
        with open(os.path.join(d, "goal.v"), "w") as f:
            f.write(prefix + "\n" + script + suffix)
        inner = os.path.relpath(d, ARIADNE)
        r = subprocess.run(
            [RUN, "sh", "-c", f"cd /ariadne/{inner} && "
             f"timeout {timeout} {COQC} goal.v"],
            capture_output=True, text=True, timeout=timeout + 60)
        return r.returncode == 0, (r.stdout + r.stderr).strip()[-2000:]
    except subprocess.TimeoutExpired:
        return False, "(timeout)"
    finally:
        subprocess.run(["rm", "-rf", d])


def reconstructed(feedback):
    """The tactic `hammer` reports it found ("Replace the hammer tactic
    with: srun eauto use: ..."), or None."""
    for _, msg in feedback or []:
        m = re.search(r"Replace the hammer tactic with:\s*(.+?\.)\s*$",
                      msg, re.S)
        if m:
            return " ".join(m.group(1).split())
    return None


class Search:
    def __init__(self, path, goal_seconds, tactic_seconds):
        self.path = os.path.abspath(path)
        self.text = open(self.path).read()
        self.prefix, _, self.suffix = split_goal(self.text)
        m = re.search(r"\(\* Why3 goal \*\)\s*\n", self.prefix)
        self.statement = self.prefix[m.end():]
        self.goal_seconds = goal_seconds
        self.tactic_seconds = tactic_seconds
        self.pet = None
        self.root = None
        self.dir = None

    def _open(self):
        """A Pétanque session on a copy whose proof is `Admitted.`, so
        pet never sees a proof the file may hold."""
        self.dir = tempfile.mkdtemp(dir=os.path.join(ARIADNE, "runs"),
                                    prefix="pet_")
        with open(os.path.join(self.dir, "goal.v"), "w") as f:
            f.write(self.prefix + "\nAdmitted.\n")
        self.pet = Petanque(self.dir)
        self.root = self.pet.start("goal.v", "wp_goal", timeout=300)["st"]

    def close(self):
        if self.pet:
            self.pet.close()
            subprocess.run(["rm", "-rf", self.dir])
            self.pet = None

    def attempt(self, script, timeout):
        """Run `script` from the statement.  ("proved" | "unfinished" |
        "error" | "timeout", detail, feedback)."""
        if self.pet is None:
            self._open()
        try:
            r = self.pet.run(self.root, script, timeout=timeout)
        except PetanqueTimeout:
            self.close()  # the session is stuck: a new one next time
            return "timeout", f"over {timeout:.0f} s", None
        except PetanqueError as e:
            return "error", str(e)[:300], None
        if r.get("proof_finished"):
            return "proved", "", r.get("feedback")
        return "unfinished", "goals left", r.get("feedback")

    def run(self):
        start = time.time()
        tried = []
        result = {"goal": os.path.basename(self.path), "status": "open",
                  "script": None, "tried": tried}
        try:
            for tac in candidates(self.prefix, self.statement):
                left = self.goal_seconds - (time.time() - start)
                if left <= 1:
                    result["stopped"] = "goal time cap"
                    break
                t = time.time()
                outcome, detail, feedback = self.attempt(
                    tac, min(self.tactic_seconds, left))
                tried.append({"tactic": tac, "outcome": outcome,
                              "seconds": round(time.time() - t, 1)})
                if outcome != "proved":
                    continue
                # Pétanque says no goals left; the verdict is coqc's.
                scripts = [tac]
                found = reconstructed(feedback)
                if found and not FORBIDDEN.search(found):
                    scripts.insert(0, found)
                for s in scripts:
                    ok, out = coqc(self.prefix, s, self.suffix,
                                   max(int(self.tactic_seconds) * 2, 60))
                    tried[-1].setdefault("coqc", []).append(
                        {"script": s, "ok": ok})
                    if ok:
                        result.update(status="proved", script=s)
                        break
                if result["status"] == "proved":
                    break
        finally:
            self.close()
        result["seconds"] = round(time.time() - start, 1)
        return result

    def apply(self, script):
        with open(self.path, "w") as f:
            f.write(self.prefix + "\n" + script + self.suffix)


def main():
    ap = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    ap.add_argument("goals", nargs="+")
    ap.add_argument("--goal-seconds", type=float, default=300)
    ap.add_argument("--tactic-seconds", type=float, default=60)
    ap.add_argument("--apply", action="store_true")
    ap.add_argument("--json")
    a = ap.parse_args()
    status = 0
    for g in a.goals:
        s = Search(g, a.goal_seconds, a.tactic_seconds)
        r = s.run()
        if r["status"] == "proved" and a.apply:
            s.apply(r["script"])
        line = json.dumps(r)
        print(line, flush=True)
        if a.json:
            with open(a.json, "a") as f:
                f.write(line + "\n")
        status |= r["status"] != "proved"
    sys.exit(status)


if __name__ == "__main__":
    main()
