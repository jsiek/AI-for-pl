"""Leak-freedom lint for VST funspecs (owner, R10, 2026-11-17).

VST 2.17 lets a proof drop owned memory only through an absorbing
predicate in a postcondition (`../affine_probe/`).  This lint checks
every funspec of the given compiled Coq modules on Coq's *elaborated*
terms, not on the source text, so no spelling (notation, parentheses,
line breaks, local definitions) can hide a violation:

1.  `Print Module` lists each module's declarations with their types
    (Coq's canonical output).  Every declaration whose type ends in
    `funspec`, `funspecs` or `prod ident funspec` is a spec to lint; a
    `Parameter`/`Axiom` of such a type fails (fail closed: no body to
    examine).
2.  For each spec, Coq unfolds the modules' own definitions
    (`Std.eval_cbv` with delta on exactly those constants, beta, zeta,
    match) and `PostLint.report` (Ltac2, `PostLint.v`) walks the term:
    every NDmk_funspec / mk_funspec postcondition must contain no `TT`,
    no existential over `mpred`, no `!! P` outside a conjunction, and no
    unknown connective; `_main`'s must hold `mem_mgr`.  A spec in which
    no postcondition is found fails (fail closed).
3.  Every spec must get an OK or FAIL line from Coq; a missing line, or
    a coqc error, fails (fail closed).

A private helper whose postcondition contains `TT` cannot hide a leak:
its caller would then hold `TT`, which entails no `TT`-free assertion,
so the caller could not end in a `TT`-free public postcondition.

    python3 -I post_lint.py [--root DIR] [--lib LIB] MODULE [MODULE ...]

MODULE is a logical name (e.g. SglibVST.spec_dllist), already compiled
under `-Q DIR LIB` (--root DIR, --lib LIB); the lint copies PostLint.v
to DIR/lint/ and compiles it there.
Coq runs in the VST image through ../../../vst/run.sh.  Prints one line
per spec and exits 1 on any failure.
"""
import argparse
import os
import re
import shutil
import subprocess
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)
RUN = os.path.join(ROOT, "..", "vst", "run.sh")
KEYWORDS = r"(?:Definition|Parameter|Axiom|Inductive|CoInductive|Record|" \
           r"Structure|Variant|Class|Instance|Fixpoint|CoFixpoint|Module|" \
           r"Module Type|End|Notation|Ltac|Ltac2|Theorem|Lemma|Scheme)"
SPEC_TYPE = re.compile(r"(?:^|[,(]\s*|\s)(?:funspec|funspecs|"
                       r"prod\s+ident\s+funspec)\s*\)*\s*$")
# Not unfolded: instances, and identifiers (so that `_main` stays
# recognisable in `(_main, spec)`).
SKIP_TYPES = {"compspecs", "varspecs", "ident"}


def coqc(root, lib, path):
    rel = os.path.relpath(path, root)
    p = subprocess.run([RUN, "coqc", "-native-compiler", "no", "-Q", ".",
                        lib, rel], cwd=root, capture_output=True, text=True)
    return p.returncode, p.stdout + p.stderr


def declarations(text):
    """(kind, name, type) for each declaration in Print Module output."""
    body = text[text.find("Struct") + len("Struct"):] if "Struct" in text \
        else text
    out = []
    for m in re.finditer(r"\b(Definition|Parameter|Axiom)\s+([A-Za-z_][\w']*)"
                         r"\s*:\s*(.*?)\.(?=\s+(?:" + KEYWORDS + r")\b|\s*$)",
                         body, re.S):
        out.append((m.group(1), m.group(2), " ".join(m.group(3).split())))
    return out


def main(argv):
    ap = argparse.ArgumentParser()
    ap.add_argument("--root", required=True)
    ap.add_argument("--lib", required=True)
    ap.add_argument("--allow-none", action="store_true",
                    help="a module with no funspec passes (a proof file)")
    ap.add_argument("modules", nargs="+")
    a = ap.parse_args(argv[1:])
    root = os.path.abspath(a.root)
    work = os.path.join(root, "postlint_tmp.v")
    fails = []
    try:
        # the checker is compiled under --root, as <lib>.lint.PostLint
        own = os.path.join(HERE, "PostLint.v")
        copy = os.path.join(root, "lint", "PostLint.v")
        if os.path.abspath(own) != os.path.abspath(copy):
            os.makedirs(os.path.dirname(copy), exist_ok=True)
            shutil.copy(own, copy)
        rc, out = coqc(root, a.lib, os.path.join(root, "lint", "PostLint.v"))
        if rc:
            print(out)
            print("FAIL: PostLint.v does not compile (fail closed)")
            return 1
        head = ["Require Import VST.floyd.proofauto."] + \
            ["Require %s." % m for m in a.modules]
        open(work, "w").write("\n".join(
            head + ["Set Printing All.", "Set Printing Width 2000000."]
            + ["Print Module %s." % m for m in a.modules]) + "\n")
        rc, out = coqc(root, a.lib, work)
        if rc:
            print(out)
            print("FAIL: Print Module failed (fail closed)")
            return 1
        decls = []
        for chunk in re.split(r"(?=Module \S+ := Struct)", out):
            if ":= Struct" not in chunk:
                continue
            mod = re.match(r"Module (\S+)", chunk).group(1)
            full = [m for m in a.modules if m.split(".")[-1] == mod]
            decls += [(k, n, t, full[0] if full else mod)
                      for k, n, t in declarations(chunk)]
        if not decls and not a.allow_none:
            print("FAIL: no declarations found in %s (fail closed)"
                  % " ".join(a.modules))
            return 1
        locals_ = [(n, m) for k, n, t, m in decls
                   if k == "Definition" and t not in SKIP_TYPES]
        specs = []
        for k, n, t, m in decls:
            if SPEC_TYPE.search(t):
                if k != "Definition":
                    fails.append("%s: a %s of funspec type has no body to "
                                 "examine (fail closed)" % (n, k))
                else:
                    specs.append((n, m))
        if not specs:
            if a.allow_none:
                print("OK: no funspec defined in %s" % " ".join(a.modules))
                return 1 if fails else 0
            fails.append("no funspec found (fail closed)")
        refs = "; ".join("reference:(%s.%s)" % (m, n) for n, m in locals_)
        lines = head + ["Require Import %s.lint.PostLint." % a.lib,
                        "From Ltac2 Require Import Ltac2."]
        for n, m in specs:
            lines.append('Ltac2 Eval report "%s" (unfold_locals [%s] '
                         'constr:(%s.%s)).' % (n, refs, m, n))
        open(work, "w").write("\n".join(lines) + "\n")
        rc, out = coqc(root, a.lib, work)
        if rc:
            print(out[-3000:])
            fails.append("the checker failed in Coq (fail closed)")
        seen = {}
        for line in out.split("\n"):
            m = re.match(r"\s*POSTLINT (OK|FAIL) ([\w']+)(.*)", line)
            if m:
                seen.setdefault(m.group(2), []).append(
                    (m.group(1), m.group(3).strip()))
        for n, _ in specs:
            res = seen.get(n)
            if not res:
                fails.append("%s: no result from the checker (fail closed)"
                             % n)
            for ok, rest in res or []:
                if ok == "OK":
                    print("OK: %s (%s postcondition(s) checked)" % (n, rest))
                else:
                    fails.append("%s%s" % (n, rest))
    finally:
        for ext in ("", "o", "ok", "os"):
            p = work[:-2] + ".v" + ext
            if os.path.exists(p):
                os.remove(p)
        for p in (os.path.join(root, ".postlint_tmp.aux"),
                  os.path.join(root, "postlint_tmp.glob")):
            if os.path.exists(p):
                os.remove(p)
    for f in fails:
        print("FAIL:", f)
    return 1 if fails else 0


if __name__ == "__main__":
    sys.exit(main(sys.argv))
