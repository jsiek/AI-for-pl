"""The check: what a proof directory proves about a target, decided by
the tools alone (G2), and the bundle manifest that re-checks it (G4).

In PROOF_DIR/check_NAME/, with pristine copies of the target's frozen files
and the proof files only (proof_files.txt in build order, ending with
the target's `proof`; or just `proof`):

 1. clightgen -normalize on the C file; coqc on its AST, the pristine
    .v files and the proof files, in order;
 2. keyword lint of the proof files: no admit, Axiom, Parameter,
    Conjecture, Hypothesis outside a Section (Admitted is allowed while
    work is in progress, and makes the verdict NOT PROVED);
 3. each goal checked against its statement (`Definition _ : STATEMENT
    := M.lemma`), the extra lines, and `Print Assumptions` per goal: a
    goal is PROVED if every assumption is VST's baseline or a trusted
    axiom (by short name) and none is declared in a proof file;
 4. coqchk on the proof modules (and so on everything they load): every
    axiom, by its full name, is in VST's baseline
    (vst/smoke/coqchk_axioms.txt) or is an `Axiom`/`Parameter` of a
    pristine file (the owner-approved trust base); no type-in-type,
    unsafe fixpoint or assumed positivity;
 5. the leak lint (ariadne/lint/post_lint.py) on the pristine modules
    named in `lint` and every proof module.

Verdict PROVED: all goals PROVED and no violation.  Writes
PROOF_DIR/check_NAME.json and PROOF_DIR/manifest_NAME.json (hashes of every input,
tool versions, the image, the verdict and the command that re-checks).
"""
import hashlib
import json
import os
import re
import shutil
import subprocess
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import targets  # noqa: E402

ARIADNE = targets.ARIADNE
RUN = targets.RUN
BASELINE = os.path.join(ARIADNE, "vst", "smoke", "coqchk_axioms.txt")
LINT = os.path.join(HERE, "lint")
IMAGE = os.environ.get("ARIADNE_VST_IMAGE", "ariadne-vst:dev")
FORBIDDEN = r"\b(admit|Axiom|Parameter|Conjecture)\b"
DECL = (r"\b(?:Lemma|Theorem|Corollary|Fact|Remark|Proposition|Example|"
        r"Definition|Fixpoint|Instance|Hypothesis|Hypotheses|Variable|"
        r"Variables|Context|Axiom|Parameter|Conjecture)\s+([A-Za-z_][\w']*)")
ASSUMED = r"^\s*(?:Axiom|Parameter|Conjecture)\s+([A-Za-z_][\w']*)"
MARK = "@@goal "


def sh(work, cmd, log):
    with open(os.path.join(work, log), "w") as f:
        return subprocess.run([RUN] + cmd, cwd=work, stdout=f,
                              stderr=subprocess.STDOUT).returncode


def coqc(t):
    return ["coqc", "-native-compiler", "no", "-Q", ".", t["lib"]]


def strip_comments(text):
    out, depth, i = [], 0, 0
    while i < len(text):
        if text.startswith("(*", i):
            depth += 1
            i += 2
        elif text.startswith("*)", i) and depth:
            depth -= 1
            i += 2
        else:
            if not depth:
                out.append(text[i])
            i += 1
    return "".join(out)


def lint_text(text):
    """Forbidden keywords (outside comments), and a Hypothesis/Variable
    outside a Section (an axiom)."""
    code = strip_comments(text)
    out = []
    depth = 0
    for i, l in enumerate(code.split("\n"), 1):
        if re.search(FORBIDDEN, l):
            out.append("%d: %s" % (i, l.strip()))
        if re.match(r"\s*Section\b", l):
            depth += 1
        elif re.match(r"\s*End\s+\w+\s*\.", l) and depth:
            depth -= 1
        if depth == 0 and re.search(
                r"\b(Hypothesis|Hypotheses|Variable|Variables|Context)\b", l):
            out.append("%d: %s (outside a Section)" % (i, l.strip()))
    return out


def proof_list(t, d):
    p = os.path.join(d, "proof_files.txt")
    if os.path.exists(p):
        return [l.strip() for l in open(p) if l.strip()]
    return [t["proof"]]


def print_assumptions(log):
    """{goal: [short names] or None (no answer)} from the check's log."""
    out = {}
    for chunk in log.split(MARK)[1:]:
        name, _, rest = chunk.partition("\n")
        name = name.strip().strip('"')
        if "Closed under the global context" in rest:
            out[name] = []
        elif "Axioms:" in rest:
            body = rest[rest.index("Axioms:") + len("Axioms:"):]
            out[name] = [m.group(1).split(".")[-1] for m in
                         re.finditer(r"^([A-Za-z_][\w.']*) :", body, re.M)]
        else:
            out[name] = None
    return out


def coqchk_summary(text):
    """(axioms by full name, [unsafe lines]) from `coqchk -o` output."""
    if "CONTEXT SUMMARY" not in text:
        return None, ["coqchk gave no context summary"]
    axioms, unsafe, section = [], [], None
    for l in text[text.index("CONTEXT SUMMARY"):].split("\n"):
        if l.startswith("* "):
            section = l
            if ":" in l and l.split(":", 1)[1].strip() not in ("", "<none>") \
                    and not l.startswith("* Theory") \
                    and not l.startswith("* Axioms"):
                unsafe.append(l.strip())
        elif section and section.startswith("* Axioms") and l.strip():
            axioms.append(l.strip())
    return axioms, unsafe


def sha(path):
    return hashlib.sha256(open(path, "rb").read()).hexdigest()


def versions(work):
    out = {}
    for name, cmd in (("coqc", ["coqc", "--version"]),
                      ("clightgen", ["clightgen", "-version"]),
                      ("coqchk", ["coqchk", "--version"])):
        r = subprocess.run([RUN] + cmd, cwd=work, capture_output=True,
                           text=True)
        out[name] = (r.stdout + r.stderr).strip().split("\n")[0]
    r = subprocess.run(["docker", "image", "inspect", "--format",
                        "{{.Id}}", IMAGE], capture_output=True, text=True)
    out["image"] = "%s %s" % (IMAGE, r.stdout.strip())
    return out


def check(name, proof_dir, coqchk=True):
    t = targets.load(name)
    d = os.path.abspath(proof_dir)
    work = os.path.join(d, "check_" + name)
    shutil.rmtree(work, ignore_errors=True)
    os.makedirs(work)
    s = {"target": name, "violations": []}
    files = proof_list(t, d)
    s["proof_files"] = files
    bad = [f for f in files if not re.fullmatch(r"\w+\.v", f)
           or f in t["files"] or not os.path.exists(os.path.join(d, f))]
    if bad or files[-1] != t["proof"]:
        s["violations"].append("proof files: bad or missing %s, or the last "
                               "is not %s" % (bad, t["proof"]))
        return finish(d, s, t, files)
    frozen = targets.frozen_files(t)
    for f, text in frozen.items():
        open(os.path.join(work, f), "w").write(text)
    trusted = set()
    for f in targets.checked_files(t):
        if f.endswith(".v"):
            trusted |= {"%s.%s.%s" % (t["lib"], f[:-2], n) for n in
                        re.findall(ASSUMED, strip_comments(frozen[f]), re.M)}
    s["trusted"] = sorted(trusted)
    declared, s["forbidden"], s["lemmas"] = set(), [], {}
    for f in files:
        shutil.copy(os.path.join(d, f), work)
        text = open(os.path.join(d, f)).read()
        declared |= set(re.findall(DECL, strip_comments(text)))
        s["forbidden"] += ["%s:%s" % (f, x) for x in lint_text(text)]
        for m in re.finditer(r"(?:Lemma|Theorem)\s+(body_\w+|prog_correct)\b",
                             text):
            end = re.search(r"\b(Qed|Admitted|Defined|Abort)\.", text[m.end():])
            s["lemmas"][m.group(1)] = end.group(1) if end else "(none)"
    if s["forbidden"]:
        s["violations"].append("forbidden keywords (%d)" % len(s["forbidden"]))
    c_file = t["c"]
    steps = [("clightgen", ["clightgen", "-normalize", c_file]),
             ("ast", coqc(t) + [c_file[:-2] + ".v"])]
    steps += [(f, coqc(t) + [f]) for f in targets.checked_files(t)
              if f.endswith(".v")]
    steps += [(f, coqc(t) + [f]) for f in files]
    c = s["compile"] = {}
    for step, cmd in steps:
        c[step] = sh(work, cmd, step + ".log")
        if c[step]:
            s["error"] = open(os.path.join(work, step + ".log")).read()[-1500:]
            s["violations"].append("does not compile: %s" % step)
            return finish(d, s, t, files)
    # 3. the goals
    mod = "%s.%s" % (t["lib"], t["proof"][:-2])
    # pristine modules are only Required (statements name them in full);
    # the proof modules are Imported, so `Gprog` is the proof's own
    pristine = targets.modules(t, [c_file[:-2] + ".v"] + [
        f for f in targets.checked_files(t) if f.endswith(".v")])
    lines = ["Require Import VST.floyd.proofauto VST.floyd.library.",
             "Require %s." % " ".join(pristine),
             "Require Import %s." % " ".join(targets.modules(t, files))
             ] + t.get("preamble", [])
    goals = t.get("goals", {})
    for g, stmt in goals.items():
        lines += ["Definition stmt_%s : %s := %s.%s." % (
            g, stmt.replace("{M}", mod), mod, g),
            'Goal True. idtac "%s%s". exact I. Qed.' % (MARK, g),
            "Print Assumptions %s.%s." % (mod, g)]
    lines += [x.replace("{M}", mod) for x in t.get("extra", [])]
    open(os.path.join(work, "check_goals.v"), "w").write("\n".join(lines) + "\n")
    rc = sh(work, coqc(t) + ["check_goals.v"], "check_goals.log")
    log = open(os.path.join(work, "check_goals.log")).read()
    if rc:
        s["error"] = log[-1500:]
        s["violations"].append("a goal is missing or not its statement, or "
                               "an extra line fails")
        return finish(d, s, t, files)
    base_short = {a.split(".")[-1] for a in baseline()}
    ok_short = base_short | {a.split(".")[-1] for a in trusted}
    # a pristine file's Admitted lemmas (sglib's spec states its six body
    # lemmas that way) are in the environment, but a goal may not use one
    pristine_admitted = {}
    for f in targets.checked_files(t):
        if f.endswith(".v"):
            for n in admitted_names(strip_comments(frozen[f])):
                pristine_admitted["%s.%s.%s" % (t["lib"], f[:-2], n)] = n
    s["goals"] = {}
    for g, ax in print_assumptions(log).items():
        if ax is None:
            s["goals"][g] = "NO ANSWER"
            continue
        extra = sorted({a for a in ax if a not in ok_short
                        or a in declared or a in pristine_admitted.values()})
        s["goals"][g] = "PROVED" if not extra else "OPEN (assumes %s)" % (
            ", ".join(extra))
    open_goals = [g for g, v in s["goals"].items() if v != "PROVED"]
    if open_goals or set(s["goals"]) != set(goals):
        s["violations"].append("goals not proved: %s" % (
            open_goals or sorted(set(goals) - set(s["goals"]))))
    # 4. coqchk
    if coqchk:
        rc = sh(work, ["coqchk", "-silent", "-o", "-Q", ".", t["lib"]]
                + targets.modules(t, files), "coqchk.log")
        axioms, unsafe = coqchk_summary(
            open(os.path.join(work, "coqchk.log")).read())
        s["coqchk"] = {"rc": rc, "unsafe": unsafe}
        if rc or axioms is None:
            s["violations"].append("coqchk failed")
        else:
            new = sorted(set(axioms) - baseline())
            s["coqchk"]["axioms_beyond_vst"] = new
            s["coqchk"]["unexpected"] = sorted(
                a for a in new if a not in trusted
                and a not in pristine_admitted)
            if s["coqchk"]["unexpected"] or unsafe:
                s["violations"].append("coqchk: axioms outside VST's and the "
                                       "trusted specs: %s %s" % (
                                           s["coqchk"]["unexpected"], unsafe))
    else:
        s["coqchk"] = "skipped"
        s["violations"].append("coqchk skipped")
    # 5. the leak lint
    mods = ["%s.%s" % (t["lib"], m) for m in t.get("lint", [])] + \
        targets.modules(t, files)
    pl = subprocess.run(["python3", "-I", os.path.join(LINT, "post_lint.py"),
                         "--root", work, "--lib", t["lib"]]
                        + (["--allow-none"] if t.get("lint_allow_none") else [])
                        + mods, capture_output=True, text=True)
    s["post_lint"] = {"rc": pl.returncode, "out": pl.stdout[-3000:]}
    if pl.returncode:
        s["violations"].append("post_lint failed (leak freedom)")
    return finish(d, s, t, files)


def admitted_names(text):
    """Names of the lemmas a (comment-free) file ends with Admitted."""
    out = set()
    for m in re.finditer(r"\b(?:Lemma|Theorem|Corollary|Fact|Remark|"
                         r"Proposition|Example|Definition)\s+([A-Za-z_][\w']*)",
                         text):
        end = re.search(r"\b(Qed|Admitted|Defined|Abort)\.", text[m.end():])
        if end and end.group(1) == "Admitted":
            out.add(m.group(1))
    return out


_BASELINE = None


def baseline():
    global _BASELINE
    if _BASELINE is None:
        _BASELINE = {l.strip() for l in open(BASELINE) if l.strip()
                     and not l.startswith("#")}
    return _BASELINE


def finish(d, s, t, files):
    s["verdict"] = "PROVED" if not s["violations"] else "NOT PROVED"
    json.dump(s, open(os.path.join(d, "check_%s.json" % t["name"]), "w"),
              indent=1)
    work = os.path.join(d, "check_" + t["name"])
    inputs = {f: sha(os.path.join(work, f)) for f in sorted(os.listdir(work))
              if f in t["files"] or f in files}
    m = {"target": t["name"], "verdict": s["verdict"],
         "recheck": "python3 Ariadne/ariadne/cli.py check %s %s" % (
             t["name"], os.path.relpath(d, os.path.dirname(ARIADNE))),
         "inputs_sha256": inputs,
         "trusted": s.get("trusted", []),
         "axioms_beyond_vst": (s.get("coqchk") or {}).get("axioms_beyond_vst")
         if isinstance(s.get("coqchk"), dict) else None,
         "tools": versions(work)}
    json.dump(m, open(os.path.join(d, "manifest_%s.json" % t["name"]), "w"),
              indent=1)
    return s
