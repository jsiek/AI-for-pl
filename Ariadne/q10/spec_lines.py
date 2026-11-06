#!/usr/bin/env python3
"""Plan Q10: size of the human-facing public spec on each side, in
non-blank lines that are not only a comment.

    python3 spec_lines.py [VERIF_B1A.v]

Frama-C: the public macros of ../bench/b1a/spec/sglib_dl_list_spec.h
that B1a uses (the predicates SGLIB_DL_LIST_SPEC, the four contracts,
and SGLIB_DL_LIST_SUBCMP_OK with the helpers it expands through), plus
what b1a_frozen.c writes itself (the cmp_reads predicate, the template
invocations, the driver's contract).  The ghost allocator contracts
(plugin/share/ariadne_alloc.h) are the trusted liveness model, shared by
every benchmark, and are counted apart.
VST: every Definition / Fixpoint / Inductive sentence of the file
(representation predicates, funspecs, Gprog), listed by name so that
proof-only definitions can be told apart.
"""
import os
import re
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
B1A = os.path.join(HERE, "..", "bench", "b1a")
USED = ["SGLIB_DL_LIST_SPEC", "SGLIB_DL_LIST_CONTRACT_ADD",
        "SGLIB_DL_LIST_CONTRACT_IT_INIT_ON_EQUAL",
        "SGLIB_DL_LIST_CONTRACT_IT_INIT", "SGLIB_DL_LIST_CONTRACT_IT_NEXT",
        "SGLIB_DL_LIST_SUBCMP_OK", "SGLIB_DL__ID", "SGLIB_DL__CAT",
        "SGLIB_DL__CAT_", "SGLIB_DL__N", "SGLIB_DL__N_", "SGLIB_DL__IS0",
        "SGLIB_DL__IS1", "SGLIB_DL__IS2", "SGLIB_DL__IS3", "SGLIB_DL__IS4",
        "SGLIB_DL__ISANY", "SGLIB_DL__ISANY_L"]


def count(lines):
    n, incomment = 0, False
    for raw in lines:
        l = raw.strip().rstrip("\\").strip()
        if incomment:
            if "*/" in l:
                incomment = False
                l = l.split("*/", 1)[1].strip()
            else:
                continue
        while "/*" in l and not l.startswith("/*@"):
            a, b = l.split("/*", 1)
            if "*/" in b:
                l = (a + b.split("*/", 1)[1]).strip()
            else:
                l, incomment = a.strip(), True
        if l.startswith("//") or l in ("", "*/", "/*@"):
            continue
        n += 1
    return n


def macro(hdr, name):
    i = hdr.index(f"#define {name}(")
    lines = []
    for l in hdr[i:].split("\n"):
        lines.append(l)
        if not l.endswith("\\"):
            break
    return lines


def wp():
    hdr = open(os.path.join(B1A, "spec", "sglib_dl_list_spec.h")).read()
    per = {m: count(macro(hdr, m)) for m in USED}
    src = open(os.path.join(B1A, "b1a_frozen.c")).read()
    own = [m.group(0) for m in re.finditer(r"/\*@.*?\*/", src, re.S)
           if "ARIADNE_" not in m.group(0)]
    own_n = sum(count(a.split("\n")) for a in own)
    alloc = open(os.path.join(HERE, "..", "plugin", "share",
                              "ariadne_alloc.h")).read()
    return per, own_n, alloc


def vst(path):
    text = re.sub(r"\(\*.*?\*\)", "", open(path).read(), flags=re.S)
    out = []
    for m in re.finditer(r"^\s*(Definition|Fixpoint|Inductive)\s+(\S+)"
                         r"(.*?)\.\s*$", text, re.S | re.M):
        body = m.group(0)
        out.append((m.group(2), len([l for l in body.split("\n")
                                     if l.strip()])))
    return out


def main():
    per, own, _ = wp()
    print(f"Frama-C: template macros {sum(per.values())} "
          f"({', '.join(f'{k} {v}' for k, v in per.items() if v)}); "
          f"b1a_frozen.c's own annotations {own}; total "
          f"{sum(per.values()) + own}")
    if len(sys.argv) > 1:
        d = vst(sys.argv[1])
        print(f"VST: {sum(n for _, n in d)} lines in {len(d)} sentences")
        for name, n in d:
            print(f"  {name} {n}")


if __name__ == "__main__":
    main()
