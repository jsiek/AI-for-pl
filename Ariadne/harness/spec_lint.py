"""The unanchored-postcondition lint (plan Q11, spec-validation rule 2,
owner 2026-11-08).

    python3 spec_lint.py FILE.c [--cpp-args="-I..."]   (expands first)

A postcondition can lose the link between what a function returns or
leaves behind and what it was given: `ensures \\exists s; P(\\result, s)`
says the result belongs to *some* list, not to the caller's.  B1 had
this bug twice: get_first / get_last before eaa42ed2 (2026-11-03), and
the iterator until B1c found it (2026-11-07).

For every function contract, every `ensures` clause is checked with the
public predicates unfolded (their bodies substituted, binders renamed,
up to 6 levels; inductive and body-less predicates stay atoms).  The
clause is split into atoms at `&&`, `||`, `==>`, `<==>`, `!` and the
quantifier headers; two names in one atom are connected.  An existential
binder is *anchored* when its connected component holds an input:

  * a parameter used as a value (`list`, not `list->next` or `*list`,
    which read the post-state);
  * a pre-state term: inside `\\old(..)`, `\\at(.., Pre)`, or a predicate
    applied at label Pre (`iter_at{Pre}(..)`);
  * a global named in `globals`;
  * or `\\result`, when some clause of the same contract connects
    `\\result` to an input.

`\\forall` binders only carry connections.  The lint is syntactic and
over-approximates connection (any shared atom counts); it reports, it
does not prove.  spec_checks (guardrails.py) runs it on the baseline's
expanded spec as a warning."""
import argparse
import itertools
import re
import sys
import os

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from acsl_expand import acsl_code, annotations, expand  # noqa: E402

PRE = "\\PRE"     # marker of a pre-state atom
CONNECTIVES = r"&&|\|\||==>|<==>|\?|(?<![=!<>])!(?!=)"


def match_paren(s, i):
    """Index of the parenthesis closing the one at s[i]."""
    depth = 0
    for k in range(i, len(s)):
        if s[k] == "(":
            depth += 1
        elif s[k] == ")":
            depth -= 1
            if depth == 0:
                return k
    raise ValueError("unbalanced")


def split_args(s):
    out, depth, cur = [], 0, ""
    for ch in s:
        if ch in "(<[{":
            depth += 1
        elif ch in ")>]}":
            depth -= 1
        if ch == "," and depth == 0:
            out.append(cur.strip())
            cur = ""
        else:
            cur += ch
    if cur.strip():
        out.append(cur.strip())
    return out


def binder_names(header):
    """Names bound by a quantifier header `T x, y, U z`."""
    return [re.findall(r"[A-Za-z_]\w*", part)[-1]
            for part in split_args(header)]


def predicates(code):
    """{name: (params, body)} of the predicates with a body (labels
    dropped); inductive and abstract ones are left out (atoms)."""
    out = {}
    # quantifier headers end in `;`: hide those from the body's end
    code = re.sub(r"\\(exists|forall)\s+[^;]*;",
                  lambda m: m.group(0)[:-1] + "\x00", code)
    for m in re.finditer(r"\bpredicate\s+(\w+)\s*(\{[^}]*\})?\s*\(", code):
        i = m.end() - 1
        j = match_paren(code, i)
        rest = code[j + 1:].lstrip()
        if not rest.startswith("="):
            continue
        body_start = code.index("=", j) + 1
        depth, k = 0, body_start
        while k < len(code):
            if code[k] in "({":
                depth += 1
            elif code[k] in ")}":
                depth -= 1
            elif code[k] == ";" and depth == 0:
                break
            k += 1
        params = binder_names(code[i + 1:j]) if code[i + 1:j].strip() else []
        out[m.group(1)] = (params,
                           code[body_start:k].strip().replace("\x00", ";"))
    return out


def subst(text, mapping):
    if not mapping:
        return text
    rx = r"(?<![\\\w])(" + "|".join(map(re.escape, mapping)) + r")(?!\w)"
    return re.sub(rx, lambda m: mapping[m.group(1)], text)


def mark_pre(text):
    """Every atom of text marked as pre-state."""
    return PRE + " " + re.sub(r"(" + CONNECTIVES + r"|;)",
                              lambda m: m.group(1) + " " + PRE + " ", text)


fresh = itertools.count()


def unfold(text, preds, depth=0):
    """text with the predicates of `preds` unfolded."""
    if depth > 6:
        return text
    out, i = "", 0
    rx = re.compile(r"(?<![\\\w])(" + "|".join(map(re.escape, preds))
                    + r")\s*(\{[^}]*\})?\s*\(") if preds else None
    while rx:
        m = rx.search(text, i)
        if not m:
            break
        j = match_paren(text, m.end() - 1)
        params, body = preds[m.group(1)]
        args = split_args(text[m.end():j])
        if len(args) != len(params):
            out += text[i:j + 1]
            i = j + 1
            continue
        n = next(fresh)
        # rename the body's binders, then substitute the arguments
        bound = {}
        for q in re.finditer(r"\\(?:exists|forall)\s+([^;]*);", body):
            for b in binder_names(q.group(1)):
                bound[b] = f"{b}__{n}"
        b2 = subst(body, bound)
        b2 = subst(b2, {p: f"({a})" for p, a in zip(params, args)})
        b2 = unfold(b2, preds, depth + 1)
        label = m.group(2) or ""
        if re.search(r"\b(Pre|Old)\b", label):
            b2 = mark_pre(b2)
        out += text[i:m.start()] + "(" + b2 + ")"
        i = j + 1
    return out + text[i:]


def mark_old(text):
    """\\old(e) and \\at(e, Pre|Old) marked as pre-state."""
    while True:
        m = re.search(r"\\old\s*\(|\\at\s*\(", text)
        if not m:
            return text
        j = match_paren(text, m.end() - 1)
        args = split_args(text[m.end():j])
        inner = args[0]
        if m.group(0).startswith("\\at") and not (
                len(args) == 2 and args[1] in ("Pre", "Old")):
            text = text[:m.start()] + "(" + inner + ")" + text[j + 1:]
            continue
        text = text[:m.start()] + "(" + mark_pre(inner) + ")" + text[j + 1:]


def atoms(clause):
    """(atoms, existential binders) of a clause."""
    exists = []
    for q in re.finditer(r"\\exists\s+([^;]*);", clause):
        exists += binder_names(q.group(1))
    flat = re.sub(r"\\(exists|forall)\s+([^;]*);", " ; ", clause)
    parts = re.split(r"(?:" + CONNECTIVES + r"|;)", flat)
    return [p for p in parts if p.strip()], exists


def union_find():
    """(find, union) over a fresh partition (one per clause)."""
    parent = {}

    def find(x):
        parent.setdefault(x, x)
        while parent[x] != x:
            x = parent[x]
        return x

    def union(a, b):
        parent[find(a)] = find(b)
    return find, union


def anchored(contract, params, preds, globals_=()):
    """Findings of one contract: [(clause, unanchored binders)]."""
    clauses = [c.strip() for c in re.findall(
        r"\bensures\s+(?:\w+\s*:\s*)?(.*?);(?=\s*(?:ensures|requires|"
        r"assigns|behavior|complete|disjoint|$))", contract, re.S)]
    value = r"(?<![\\\w*&])({})(?!\w)(?!\s*->)"
    anchors = list(params) + list(globals_)
    graphs = []
    for c in clauses:
        text = mark_old(unfold(c, preds))
        # (x) -> x, so that `((it))->next` reads as a dereference
        while True:
            t2 = re.sub(r"\(\s*(\\?\w+)\s*\)(?!\s*\()", r"\1", text)
            if t2 == text:
                break
            text = t2
        parts, exists = atoms(text)
        find, union = union_find()
        names = set(exists)
        for q in re.finditer(r"\\(?:exists|forall)\s+([^;]*);", text):
            names.update(binder_names(q.group(1)))
        for p in parts:
            nodes = [n for n in names
                     if re.search(r"(?<![\\\w])" + re.escape(n) + r"(?!\w)", p)]
            if "\\result" in p:
                nodes.append("RESULT")
            if PRE in p or (anchors and re.search(
                    value.format("|".join(map(re.escape, anchors))), p)):
                nodes.append("INPUT")
            for a, b in zip(nodes, nodes[1:]):
                union(a, b)
        graphs.append((c, exists, find))
    result_ok = any(f("RESULT") == f("INPUT") for _, _, f in graphs)
    out = []
    for c, exists, f in graphs:
        bad = [x for x in exists
               if f(x) != f("INPUT")
               and not (result_ok and f(x) == f("RESULT"))]
        if bad:
            out.append((c, sorted(set(re.sub(r"__\d+$", "", b)
                                      for b in bad))))
    return out


def lint(text, globals_=()):
    """[{function, clause, binders}] of an expanded C file."""
    found, logic = [], []
    contracts = []
    for depth, _, end, body in annotations(text):
        if depth:
            continue
        code = acsl_code(body)
        if not code:
            continue
        if re.match(r"(predicate|logic|inductive|axiomatic|lemma|type)\b",
                    code):
            logic.append(code)
            continue
        m = re.search(r"([A-Za-z_]\w*)\s*\(", text[end:])
        if not m:
            continue
        j = match_paren(text, end + m.end() - 1)
        sig = text[end + m.end():j]
        params = [re.findall(r"[A-Za-z_]\w*", p)[-1]
                  for p in split_args(sig) if p.strip() and p.strip() != "void"]
        # a function pointer parameter: its name is in (*name)
        params = [re.search(r"\(\s*\*\s*(\w+)", p).group(1)
                  if "(*" in p.replace(" ", "") else q
                  for p, q in zip(split_args(sig), params)]
        contracts.append((m.group(1), code, params))
    preds = predicates(" ".join(logic))
    for fct, code, params in contracts:
        for clause, binders in anchored(code, params, preds, globals_):
            found.append({"function": fct, "binders": binders,
                          "clause": re.sub(r"\s+", " ", clause)[:300]})
    return found


def check(text, globals_=()):
    """The spec_checks verdict: always ok (a warning), with findings."""
    f = lint(text, globals_)
    return {"ok": True, "severity": "warning", "unanchored": f}


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("file")
    ap.add_argument("--cpp-args", default="")
    ap.add_argument("--raw", action="store_true",
                    help="the file is already expanded")
    a = ap.parse_args()
    text = open(a.file).read()
    if not a.raw:
        text = expand(text, a.cpp_args)
    f = lint(text)
    for x in f:
        print(f"UNANCHORED {x['function']}: {', '.join(x['binders'])}: "
              f"ensures {x['clause']}")
    print(f"{len(f)} unanchored postcondition(s)")


if __name__ == "__main__":
    main()
