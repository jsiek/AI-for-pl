#!/usr/bin/env python3
"""Generate GTNF/agda/proof/DGG/DASHBOARD.md from tree.txt and the files.

Run from GTNF/agda:  python3 proof/DGG/dashboard.py [--no-agda]

Status of an item N (files proof/DGG/{NDef,NProof,N}.agda):
  not yet started        no NProof.agda
  skeleton (does not check)
                         NProof.agda has holes and fails to check even
                         with holes allowed (e.g. missing cases)
  skeleton complete, k/n cases finished (p%)
                         NProof.agda checks with holes allowed (so every
                         case is present); a clause counts as finished
                         when its body has no hole
  conditionally complete NProof.agda checks with no holes, but some item
                         it depends on is not finished (or N.agda, the
                         instantiation, does not exist yet)
  finished               N.agda exists and checks, and every dependency
                         is finished
With --no-agda, nothing is type-checked: a file with holes is assumed to
check, and a hole-free file is assumed to check.
"""

import os
import re
import subprocess
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.abspath(os.path.join(HERE, "..", ".."))   # GTNF/agda
TREE = os.path.join(HERE, "tree.txt")
OUT = os.path.join(HERE, "DASHBOARD.md")

HOLE = re.compile(r"\{!|(?<![\w?])\?(?![\w?])")


def parse_tree():
    items, order = {}, []
    stack = []
    for raw in open(TREE, encoding="utf-8"):
        if not raw.strip() or raw.lstrip().startswith("#"):
            continue
        indent = (len(raw) - len(raw.lstrip(" "))) // 2
        name, _, rest = raw.strip().partition("|")
        name = name.strip()
        desc, uses = rest, []
        if "uses:" in rest:
            desc, _, u = rest.partition("uses:")
            uses = u.split()
        stack = stack[:indent]
        parent = stack[-1] if stack else None
        items[name] = dict(name=name, desc=desc.strip(), uses=uses,
                           children=[], depth=indent, parent=parent)
        if parent:
            items[parent]["children"].append(name)
        order.append(name)
        stack.append(name)
    return items, order


def path(name, suffix):
    """Item `N` is proof/DGG/N*.agda; item `Dir/N` is proof/Dir/N*.agda."""
    if "/" in name:
        d, base = name.rsplit("/", 1)
        return os.path.join(ROOT, "proof", d, base + suffix + ".agda")
    return os.path.join(HERE, name + suffix + ".agda")


HOLE_ERRORS = {"UnsolvedInteractionMetas", "UnsolvedMetaVariables"}


def agda_ok(file, allow_holes):
    """Type-check FILE.  With allow_holes, a run whose only errors are
    unsolved holes counts as a success: every other error (a missing
    case is a CoverageIssue) still fails.  (`--allow-unsolved-metas`
    cannot be used: the library interfaces were built under --safe.)"""
    args = ["agda", "-v0"] + ([] if allow_holes else ["--safe"])
    args.append(os.path.relpath(file, ROOT))
    r = subprocess.run(args, cwd=ROOT, capture_output=True, text=True)
    if r.returncode == 0:
        return True
    if not allow_holes:
        return False
    errors = set(re.findall(r"error: \[(\w+)\]", r.stdout + r.stderr))
    return bool(errors) and errors <= HOLE_ERRORS


def clauses(text):
    """Clause blocks: a line that starts (at any indentation) with the
    name of a declared function (`name :` somewhere in the file) and
    has `=` or `with`, together with the more indented lines after it."""
    lines = text.splitlines()
    sig = re.compile(r"^\s*(\S+)\s+:(\s|$)")
    names = {m.group(1) for l in lines for m in [sig.match(l)] if m}
    blocks, cur, ind = [], None, 0
    for line in lines:
        code = line.split("--")[0]
        if not code.strip():
            if cur is not None:
                cur += "\n" + line
            continue
        indent = len(code) - len(code.lstrip())
        first = code.split()[0]
        is_head = first in names and (" = " in code
                                      or code.rstrip().endswith("=")
                                      or " with " in code)
        if cur is not None and indent > ind and not is_head:
            cur += "\n" + line
            continue
        if cur is not None:
            blocks.append(cur)
            cur = None
        if is_head:
            cur, ind = line, indent
    if cur is not None:
        blocks.append(cur)
    return blocks


def status(items, use_agda):
    st = {}

    def go(n):
        if n in st:
            return st[n]
        it = items.get(n)
        if it is None:
            st[n] = ("unknown item", False)
            return st[n]
        deps = it["children"] + it["uses"]
        deps_done = all(go(d)[1] for d in deps)
        proof = path(n, "Proof")
        if not os.path.exists(proof):
            st[n] = ("not yet started", False)
            return st[n]
        text = open(proof, encoding="utf-8").read()
        body = "\n".join(l.split("--")[0] for l in text.splitlines())
        holes = len(HOLE.findall(body))
        if holes:
            if use_agda and not agda_ok(proof, allow_holes=True):
                st[n] = ("skeleton (does not check)", False)
                return st[n]
            bl = clauses(text)
            done = sum(1 for b in bl
                       if not HOLE.search("\n".join(
                           l.split("--")[0] for l in b.splitlines())))
            pct = (100 * done // len(bl)) if bl else 0
            st[n] = (f"skeleton complete, {done}/{len(bl)} cases "
                     f"finished ({pct}%)", False)
            return st[n]
        if use_agda and not agda_ok(proof, allow_holes=False):
            st[n] = ("proof does not check", False)
            return st[n]
        lemma = path(n, "")
        if deps_done and os.path.exists(lemma) and (
                not use_agda or agda_ok(lemma, allow_holes=False)):
            st[n] = ("finished", True)
        else:
            st[n] = ("conditionally complete", False)
        return st[n]

    for n in items:
        go(n)
    return st


ICON = {"not yet started": "⬜", "finished": "✅",
        "conditionally complete": "🟨"}


def icon(s):
    for k, v in ICON.items():
        if s.startswith(k):
            return v
    return "🟧" if s.startswith("skeleton complete") else "🟥"


def wip():
    """`make wip`: check every skeleton, holes allowed."""
    bad = []
    proofdir = os.path.join(ROOT, "proof")
    for dirpath, _, files in sorted(os.walk(proofdir)):
        for f in sorted(files):
            if f.endswith("Proof.agda"):
                full = os.path.join(dirpath, f)
                ok = agda_ok(full, allow_holes=True)
                print(f"{'ok  ' if ok else 'FAIL'} "
                      f"{os.path.relpath(full, ROOT)}")
                if not ok:
                    bad.append(f)
    sys.exit(1 if bad else 0)


def main():
    if "--wip" in sys.argv:
        wip()
    use_agda = "--no-agda" not in sys.argv
    items, order = parse_tree()
    st = status(items, use_agda)
    lines = ["# GTNF DGG dashboard", "",
             "Generated by `make dashboard` (proof/DGG/dashboard.py) "
             "from `tree.txt` and the files; do not edit by hand.  "
             "Statuses: ⬜ not yet started, 🟧 skeleton complete "
             "(k/n cases), 🟨 conditionally complete, ✅ finished, "
             "🟥 does not check.  The plan is `PLAN.md`.", ""]
    roots = [n for n in order if items[n]["parent"] is None]
    for n in order:
        it = items[n]
        if it["parent"] is None and n != roots[0]:
            pass
        s, _ = st[n]
        pad = "  " * it["depth"]
        uses = (f" — uses {', '.join(it['uses'])}" if it["uses"] else "")
        lines.append(f"{pad}- {icon(s)} **{n}**: {s}. {it['desc']}{uses}")
    open(OUT, "w", encoding="utf-8").write("\n".join(lines) + "\n")
    print(f"wrote {os.path.relpath(OUT, ROOT)}")


if __name__ == "__main__":
    main()
